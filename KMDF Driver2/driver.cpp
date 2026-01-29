// Target x64
#define _AMD64_ 1


#include <ntifs.h>
#include <ntddk.h>
#include <windef.h>
#include <intrin.h>


// -------------------- Manual declarations --------------------

// SYSTEM_INFORMATION_CLASS subset we need
typedef enum _SYSTEM_INFORMATION_CLASS {
    SystemBasicInformation = 0,
    SystemProcessInformation = 5,
    SystemBigPoolInformation = 0x42
} SYSTEM_INFORMATION_CLASS;

// ZwQuerySystemInformation
extern "C" NTSTATUS ZwQuerySystemInformation(
    SYSTEM_INFORMATION_CLASS SystemInformationClass,
    PVOID SystemInformation,
    ULONG SystemInformationLength,
    PULONG ReturnLength
);

// PsGetProcessSectionBaseAddress
extern "C" PVOID PsGetProcessSectionBaseAddress(PEPROCESS Process);

// -------------------- Globals / structures --------------------

UNICODE_STRING name, link;

#define code_rw CTL_CODE(FILE_DEVICE_UNKNOWN, 0x1645, METHOD_BUFFERED, FILE_SPECIAL_ACCESS)
#define code_ba CTL_CODE(FILE_DEVICE_UNKNOWN, 0x1646, METHOD_BUFFERED, FILE_SPECIAL_ACCESS)
#define code_get_guarded_region CTL_CODE(FILE_DEVICE_UNKNOWN, 0x1647, METHOD_BUFFERED, FILE_SPECIAL_ACCESS)
#define code_security 0x85b3b69

#define PAGE_OFFSET_SIZE 12
static const UINT64 PMASK = (~0xfull << 8) & 0xfffffffffull;

typedef struct _rw {
    INT32 security;
    INT32 process_id;
    ULONGLONG address;
    ULONGLONG buffer;
    ULONGLONG size;
    BOOLEAN write;
} rw, * prw;

typedef struct _ba {
    INT32 security;
    INT32 process_id;
    ULONGLONG* address;
} ba, * pba;

typedef struct _ga {
    INT32 security;
    ULONGLONG* address;
} ga, * pga;

// -------------------- Big pool structures --------------------

typedef struct _SYSTEM_BIGPOOL_ENTRY {
    PVOID VirtualAddress;
    ULONG_PTR NonPaged : 1;
    ULONG_PTR SizeInBytes;
    UCHAR Tag[4];
} SYSTEM_BIGPOOL_ENTRY, * PSYSTEM_BIGPOOL_ENTRY;

typedef struct _SYSTEM_BIGPOOL_INFORMATION {
    ULONG Count;
    SYSTEM_BIGPOOL_ENTRY AllocatedInfo[1]; // Flexible array
} SYSTEM_BIGPOOL_INFORMATION, * PSYSTEM_BIGPOOL_INFORMATION;

// -------------------- EPROCESS offset cache --------------------

typedef struct _EPROCESS_OFFSETS {
    ULONG DirectoryTableBase;
    ULONG UserDirectoryTableBase;
    BOOLEAN Initialized;
} EPROCESS_OFFSETS, * PEPROCESS_OFFSETS;

static EPROCESS_OFFSETS g_eprocess_offsets = { 0 };

// -------------------- Memory helpers --------------------

NTSTATUS read(PVOID target_address, PVOID buffer, SIZE_T size, SIZE_T* bytes_read) {
    MM_COPY_ADDRESS to_read = { 0 };
    to_read.PhysicalAddress.QuadPart = (LONGLONG)target_address;
    return MmCopyMemory(buffer, to_read, size, MM_COPY_MEMORY_PHYSICAL, bytes_read);
}

NTSTATUS write(PVOID target_address, PVOID buffer, SIZE_T size, SIZE_T* bytes_written) {
    if (!target_address) return STATUS_UNSUCCESSFUL;
    PHYSICAL_ADDRESS phys = { 0 };
    phys.QuadPart = (LONGLONG)target_address;
    PVOID mapped = MmMapIoSpaceEx(phys, size, PAGE_READWRITE);
    if (!mapped) return STATUS_UNSUCCESSFUL;
    memcpy(mapped, buffer, size);
    *bytes_written = size;
    MmUnmapIoSpace(mapped, size);
    return STATUS_SUCCESS;
}

// -------------------- EPROCESS runtime discovery --------------------

ULONG FindDirectoryTableBaseOffset(PEPROCESS Process) {
    PUCHAR p = (PUCHAR)Process;
    ULONG max_search = 0x400;
    ULONG_PTR cr3 = 0;

    __try { cr3 = __readcr3(); }
    __except (EXCEPTION_EXECUTE_HANDLER) { return 0; }

    for (ULONG i = 0; i < max_search; i += sizeof(ULONG_PTR)) {
        ULONG_PTR val = *(PULONG_PTR)(p + i);
        if ((val & 0xFFF) == 0 && val != 0) return i;
    }
    return 0;
}

ULONG FindUserDirectoryTableBaseOffset(PEPROCESS Process) {
    PUCHAR p = (PUCHAR)Process;
    ULONG max_search = 0x400;
    ULONG dirbase_offset = FindDirectoryTableBaseOffset(Process);
    if (dirbase_offset == 0) return 0;
    ULONG_PTR dirbase_val = *(PULONG_PTR)(p + dirbase_offset);
    for (ULONG i = 0; i < max_search; i += sizeof(ULONG_PTR)) {
        if (i == dirbase_offset) continue;
        ULONG_PTR val = *(PULONG_PTR)(p + i);
        if ((val & 0xFFF) == 0 && val != 0 && val != dirbase_val) return i;
    }
    return 0;
}

NTSTATUS InitializeEPROCESSOffsets() {
    if (g_eprocess_offsets.Initialized) return STATUS_SUCCESS;
    PEPROCESS current = PsGetCurrentProcess();
    if (!current) return STATUS_UNSUCCESSFUL;
    g_eprocess_offsets.DirectoryTableBase = FindDirectoryTableBaseOffset(current);
    if (g_eprocess_offsets.DirectoryTableBase == 0) return STATUS_UNSUCCESSFUL;
    g_eprocess_offsets.UserDirectoryTableBase = FindUserDirectoryTableBaseOffset(current);
    g_eprocess_offsets.Initialized = TRUE;
    return STATUS_SUCCESS;
}

// -------------------- CR3 / paging helpers --------------------

UINT64 get_process_cr3(const PEPROCESS pProcess) {
    if (!g_eprocess_offsets.Initialized) {
        if (!NT_SUCCESS(InitializeEPROCESSOffsets())) return 0;
    }
    PUCHAR p = (PUCHAR)pProcess;
    ULONG_PTR dtb = *(PULONG_PTR)(p + g_eprocess_offsets.DirectoryTableBase);
    if (dtb == 0 && g_eprocess_offsets.UserDirectoryTableBase != 0)
        dtb = *(PULONG_PTR)(p + g_eprocess_offsets.UserDirectoryTableBase);
    return dtb;
}

UINT64 translate_linear(UINT64 directoryTableBase, UINT64 virtualAddress) {
    directoryTableBase &= ~0xf;
    UINT64 pageOffset = virtualAddress & 0xFFF;
    UINT64 pte = (virtualAddress >> 12) & 0x1FF;
    UINT64 pt = (virtualAddress >> 21) & 0x1FF;
    UINT64 pd = (virtualAddress >> 30) & 0x1FF;
    UINT64 pdp = (virtualAddress >> 39) & 0x1FF;
    SIZE_T rs = 0;
    UINT64 pdpe = 0; read(PVOID(directoryTableBase + 8 * pdp), &pdpe, sizeof(pdpe), &rs);
    if (~pdpe & 1) return 0;
    UINT64 pde = 0; read(PVOID((pdpe & PMASK) + 8 * pd), &pde, sizeof(pde), &rs);
    if (~pde & 1) return 0;
    if (pde & 0x80) return (pde & (~0ull << 42 >> 12)) + (virtualAddress & ~(~0ull << 30));
    UINT64 pteAddr = 0; read(PVOID((pde & PMASK) + 8 * pt), &pteAddr, sizeof(pteAddr), &rs);
    if (~pteAddr & 1) return 0;
    if (pteAddr & 0x80) return (pteAddr & PMASK) + (virtualAddress & ~(~0ull << 21));
    virtualAddress = 0; read(PVOID((pteAddr & PMASK) + 8 * pte), &virtualAddress, sizeof(virtualAddress), &rs);
    virtualAddress &= PMASK;
    if (!virtualAddress) return 0;
    return virtualAddress + pageOffset;
}

// -------------------- IOCTL handlers --------------------

ULONG64 find_min(INT32 g, SIZE_T f) { return ((g) < (INT32)f) ? g : (INT32)f; }

NTSTATUS frw(prw x) {
    if (x->security != code_security) return STATUS_UNSUCCESSFUL;
    if (!x->process_id) return STATUS_UNSUCCESSFUL;
    PEPROCESS process = nullptr;
    PsLookupProcessByProcessId((HANDLE)x->process_id, &process);
    if (!process) return STATUS_UNSUCCESSFUL;
    ULONGLONG base = get_process_cr3(process);
    ObDereferenceObject(process);
    SIZE_T this_offset = 0;
    SIZE_T total_size = x->size;
    INT64 phys = translate_linear(base, (ULONG64)x->address + this_offset);
    if (!phys) return STATUS_UNSUCCESSFUL;
    ULONG64 final_size = find_min(PAGE_SIZE - (phys & 0xFFF), total_size);
    SIZE_T bytes_trough = 0;
    if (x->write) write(PVOID(phys), (PVOID)((ULONG64)x->buffer + this_offset), final_size, &bytes_trough);
    else read(PVOID(phys), (PVOID)((ULONG64)x->buffer + this_offset), final_size, &bytes_trough);
    return STATUS_SUCCESS;
}

NTSTATUS fba(pba x) {
    if (x->security != code_security) return STATUS_UNSUCCESSFUL;
    if (!x->process_id) return STATUS_UNSUCCESSFUL;
    PEPROCESS process = nullptr;
    PsLookupProcessByProcessId((HANDLE)x->process_id, &process);
    if (!process) return STATUS_UNSUCCESSFUL;
    ULONGLONG base = (ULONGLONG)PsGetProcessSectionBaseAddress(process);
    if (!base) return STATUS_UNSUCCESSFUL;
    RtlCopyMemory(x->address, &base, sizeof(base));
    ObDereferenceObject(process);
    return STATUS_SUCCESS;
}

NTSTATUS fget_guarded_region(pga x) {
    if (x->security != code_security) return STATUS_UNSUCCESSFUL;
    ULONG infoLen = 0; NTSTATUS status = ZwQuerySystemInformation(SystemBigPoolInformation, &infoLen, 0, &infoLen);
    PSYSTEM_BIGPOOL_INFORMATION pPoolInfo = 0;
    while (status == STATUS_INFO_LENGTH_MISMATCH) {
        if (pPoolInfo) ExFreePool(pPoolInfo);
        pPoolInfo = (PSYSTEM_BIGPOOL_INFORMATION)ExAllocatePool(NonPagedPool, infoLen);
        status = ZwQuerySystemInformation(SystemBigPoolInformation, pPoolInfo, infoLen, &infoLen);
    }
    if (pPoolInfo) {
        for (ULONG i = 0; i < pPoolInfo->Count; i++) {
            SYSTEM_BIGPOOL_ENTRY* e = &pPoolInfo->AllocatedInfo[i];
            if (e->NonPaged && e->SizeInBytes == 0x200000) {
                UCHAR tag[] = "TnoC";
                if (memcmp(e->Tag, tag, sizeof(tag)) == 0) {
                    RtlCopyMemory(x->address, &e->VirtualAddress, sizeof(e->VirtualAddress));
                    ExFreePool(pPoolInfo);
                    return STATUS_SUCCESS;
                }
            }
        }
        ExFreePool(pPoolInfo);
    }
    return STATUS_SUCCESS;
}

// -------------------- IOCTL dispatcher --------------------

NTSTATUS io_controller(PDEVICE_OBJECT device_obj, PIRP irp) {
    UNREFERENCED_PARAMETER(device_obj);
    NTSTATUS status = STATUS_SUCCESS;
    ULONG bytes = 0;
    PIO_STACK_LOCATION stack = IoGetCurrentIrpStackLocation(irp);
    ULONG code = stack->Parameters.DeviceIoControl.IoControlCode;
    ULONG size = stack->Parameters.DeviceIoControl.InputBufferLength;

    if (code == code_rw && size == sizeof(_rw)) { status = frw((prw)irp->AssociatedIrp.SystemBuffer); bytes = sizeof(_rw); }
    else if (code == code_ba && size == sizeof(_ba)) { status = fba((pba)irp->AssociatedIrp.SystemBuffer); bytes = sizeof(_ba); }
    else if (code == code_get_guarded_region && size == sizeof(_ga)) { status = fget_guarded_region((pga)irp->AssociatedIrp.SystemBuffer); bytes = sizeof(_ga); }
    else { status = STATUS_INFO_LENGTH_MISMATCH; }

    irp->IoStatus.Status = status;
    irp->IoStatus.Information = bytes;
    IoCompleteRequest(irp, IO_NO_INCREMENT);
    return status;
}

// -------------------- Dispatch routines --------------------

NTSTATUS unsupported_dispatch(PDEVICE_OBJECT device_obj, PIRP irp) {
    UNREFERENCED_PARAMETER(device_obj);
    irp->IoStatus.Status = STATUS_NOT_SUPPORTED;
    IoCompleteRequest(irp, IO_NO_INCREMENT);
    return STATUS_NOT_SUPPORTED;
}

NTSTATUS dispatch_handler(PDEVICE_OBJECT device_obj, PIRP irp) {
    UNREFERENCED_PARAMETER(device_obj);
    IoCompleteRequest(irp, IO_NO_INCREMENT);
    return STATUS_SUCCESS;
}

// -------------------- Driver unload --------------------

void unload_drv(PDRIVER_OBJECT drv_obj) {
    IoDeleteSymbolicLink(&link);
    IoDeleteDevice(drv_obj->DeviceObject);
}

// -------------------- Driver initialization --------------------

NTSTATUS initialize_driver(PDRIVER_OBJECT drv_obj, PUNICODE_STRING path) {
    UNREFERENCED_PARAMETER(path);
    NTSTATUS status = STATUS_SUCCESS;
    PDEVICE_OBJECT device_obj = nullptr;

    RtlInitUnicodeString(&name, L"\\Device\\paysoniscoolio");
    RtlInitUnicodeString(&link, L"\\DosDevices\\paysoniscoolio");

    status = IoCreateDevice(drv_obj, 0, &name, FILE_DEVICE_UNKNOWN, FILE_DEVICE_SECURE_OPEN, FALSE, &device_obj);
    if (!NT_SUCCESS(status)) return status;
    status = IoCreateSymbolicLink(&link, &name);
    if (!NT_SUCCESS(status)) { IoDeleteDevice(device_obj); return status; }

    for (int i = 0; i <= IRP_MJ_MAXIMUM_FUNCTION; i++) drv_obj->MajorFunction[i] = unsupported_dispatch;
    drv_obj->MajorFunction[IRP_MJ_CREATE] = dispatch_handler;
    drv_obj->MajorFunction[IRP_MJ_CLOSE] = dispatch_handler;
    drv_obj->MajorFunction[IRP_MJ_DEVICE_CONTROL] = io_controller;
    drv_obj->DriverUnload = unload_drv;

    device_obj->Flags |= DO_BUFFERED_IO;
    device_obj->Flags &= ~DO_DEVICE_INITIALIZING;

    InitializeEPROCESSOffsets();

    return status;
}

// -------------------- Driver entry --------------------

extern "C" NTSTATUS DriverEntry(PDRIVER_OBJECT DriverObject, PUNICODE_STRING RegistryPath) {
    UNREFERENCED_PARAMETER(RegistryPath);
    return initialize_driver(DriverObject, nullptr);
}
