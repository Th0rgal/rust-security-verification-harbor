"""Linux Landlock + seccomp for untrusted proof elaboration (fail closed)."""
import ctypes
import ctypes.util
import errno
import os
import resource

# Linux x86_64/aarch64 use these Landlock syscall numbers.
SECCOMP_LIBRARY = ctypes.util.find_library('seccomp')
CREATE, ADD, RESTRICT = 444, 445, 446
EXECUTE, WRITE_FILE, READ_FILE, READ_DIR = 1, 2, 4, 8
WRITE = WRITE_FILE | sum(1 << n for n in range(4, 13))  # remove/create/refer

class Ruleset(ctypes.Structure):
    _fields_ = [('handled_access_fs', ctypes.c_uint64)]
class PathRule(ctypes.Structure):
    _pack_ = 1
    _fields_ = [('allowed_access', ctypes.c_uint64), ('parent_fd', ctypes.c_int32)]


def restrict(workdir, read_paths):
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3, 16 * 1024**3))
    resource.setrlimit(resource.RLIMIT_FSIZE, (32 * 1024**2, 32 * 1024**2))
    resource.setrlimit(resource.RLIMIT_NOFILE, (128, 128))
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(38, 1, 0, 0, 0) != 0: raise OSError('no_new_privs failed')
    abi = libc.syscall(CREATE, 0, 0, 1)
    if abi < 1: raise OSError('Landlock unavailable: sandbox cannot be established')
    # REFER (bit 13) is not required; cross-directory rename is denied by default.
    access = EXECUTE | READ_FILE | READ_DIR | WRITE
    if abi >= 3: access |= 1 << 14  # TRUNCATE
    ruleset = Ruleset(access)
    fd = libc.syscall(CREATE, ctypes.byref(ruleset), ctypes.sizeof(ruleset), 0)
    if fd < 0: raise OSError(ctypes.get_errno(), 'Landlock create failed')
    try:
        for path, rights in [(workdir, access)] + [(p, EXECUTE | READ_FILE | READ_DIR) for p in read_paths]:
            if not os.path.exists(path): continue
            pathfd = os.open(path, os.O_PATH | os.O_CLOEXEC)
            try:
                if not os.path.isdir(path): rights &= EXECUTE | READ_FILE | WRITE_FILE
                rule = PathRule(rights, pathfd)
                if libc.syscall(ADD, fd, 1, ctypes.byref(rule), 0) < 0:
                    raise OSError(ctypes.get_errno(), 'Landlock add failed')
            finally: os.close(pathfd)
        if libc.syscall(RESTRICT, fd, 0) < 0: raise OSError(ctypes.get_errno(), 'Landlock restrict failed')
    finally: os.close(fd)
    sec = ctypes.CDLL(SECCOMP_LIBRARY)
    sec.seccomp_init.argtypes = [ctypes.c_uint32]; sec.seccomp_init.restype = ctypes.c_void_p
    sec.seccomp_rule_add.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int, ctypes.c_uint]
    sec.seccomp_load.argtypes = [ctypes.c_void_p]; sec.seccomp_release.argtypes = [ctypes.c_void_p]
    sec.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    ctx = sec.seccomp_init(0x7fff0000)  # allow except explicitly denied effects
    if not ctx: raise OSError('seccomp init failed')
    try:
        for name in ('socket', 'connect', 'bind', 'listen', 'accept', 'accept4', 'sendto', 'sendmsg',
                     'ptrace', 'process_vm_readv', 'process_vm_writev', 'kill', 'tkill', 'tgkill',
                     'setsid', 'setpgid', 'mount', 'umount2', 'unshare', 'setns', 'bpf',
                     'io_uring_setup', 'open_by_handle_at', 'pidfd_getfd',
                     'chmod', 'fchmod', 'fchmodat', 'fchmodat2', 'chown', 'fchown', 'lchown', 'fchownat',
                     'setxattr', 'lsetxattr', 'fsetxattr', 'removexattr', 'lremovexattr', 'fremovexattr',
                     'truncate', 'ftruncate', 'reboot', 'kexec_load', 'kexec_file_load', 'init_module', 'finit_module'):
            number = sec.seccomp_syscall_resolve_name(name.encode())
            if number >= 0 and sec.seccomp_rule_add(ctx, 0x50000 | errno.EPERM, number, 0) != 0:
                raise OSError('seccomp rule failed: ' + name)
        if sec.seccomp_load(ctx) != 0: raise OSError('seccomp load failed')
    finally: sec.seccomp_release(ctx)
