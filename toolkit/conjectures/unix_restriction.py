"""Add the AF_UNIX restriction inside an isolated evaluation container.

This only supplements Landrun. It never replaces the existing sandbox or kernels.
The filter is inherited by children and cannot be removed after loading.
"""
import ctypes
import ctypes.util
import errno
import os
import socket
import sys
from .core import Failure


def restrict():
    if sys.platform!='linux' or os.getuid()==0:
        raise Failure('unqualified_executor','The evaluation verifier requires unprivileged Linux.',3)
    name=ctypes.util.find_library('seccomp') or 'libseccomp.so.2'
    try:lib=ctypes.CDLL(name,use_errno=True)
    except OSError as error:raise Failure('missing_tool','Install libseccomp2 in the verifier image.',3) from error
    class Compare(ctypes.Structure):
        _fields_=[('arg',ctypes.c_uint),('op',ctypes.c_int),('a',ctypes.c_uint64),('b',ctypes.c_uint64)]
    lib.seccomp_init.argtypes=[ctypes.c_uint32];lib.seccomp_init.restype=ctypes.c_void_p
    lib.seccomp_syscall_resolve_name.argtypes=[ctypes.c_char_p];lib.seccomp_syscall_resolve_name.restype=ctypes.c_int
    lib.seccomp_rule_add_array.argtypes=[ctypes.c_void_p,ctypes.c_uint32,ctypes.c_int,ctypes.c_uint,ctypes.POINTER(Compare)]
    lib.seccomp_load.argtypes=[ctypes.c_void_p];lib.seccomp_release.argtypes=[ctypes.c_void_p]
    context=lib.seccomp_init(0x7fff0000)  # ALLOW; existing container filters remain in force.
    if not context:raise Failure('unqualified_executor','Cannot allocate AF_UNIX filter.',3)
    try:
        for syscall in (b'socket',b'socketpair'):
            number=lib.seccomp_syscall_resolve_name(syscall)
            comparison=Compare(0,4,socket.AF_UNIX,0)  # SCMP_CMP_EQ
            if number<0 or lib.seccomp_rule_add_array(context,0x00050000|errno.EAFNOSUPPORT,number,1,ctypes.byref(comparison))<0:
                raise Failure('unqualified_executor','Cannot configure AF_UNIX filter.',3)
        if lib.seccomp_load(context)<0:raise Failure('unqualified_executor','Cannot load AF_UNIX filter.',3)
    finally:lib.seccomp_release(context)
    for create in (lambda:socket.socket(socket.AF_UNIX),socket.socketpair):
        try:
            sockets=create()
        except OSError as error:
            if error.errno not in (errno.EAFNOSUPPORT,errno.EPERM,errno.EACCES):raise
        else:
            for sock in sockets if isinstance(sockets,tuple) else (sockets,):sock.close()
            raise Failure('unqualified_executor','AF_UNIX filter did not take effect.',3)
