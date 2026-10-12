"""Optional exact K-linear solve through the installed FLINT 3 C library.

K=Q(sqrt(13),sqrt(-3)).  The regular representation converts an n by n
K-system into a 4n by 4n rational system.  This is a solve accelerator,
not a containment certificate: callers must verify full vector residuals.
Use only inside the root-coordinated safe numerical launcher.
"""
import ctypes as C
import resource

from gmpy2 import mpq

from hi_cft_20260923_next_fast_field import FastField


class Q(C.Structure):
    _fields_ = [('num', C.c_long), ('den', C.c_long)]


class Mat(C.Structure):
    # Verified against /usr/include/flint/fmpq_types.h on this machine.
    _fields_ = [('entries', C.POINTER(Q)), ('r', C.c_long),
                ('c', C.c_long), ('stride', C.c_long)]


def regular_block(value):
    a, b, c, d = FastField(value)
    return ((a, 13*b, -3*c, -39*d),
            (b, a, -3*d, -3*c),
            (c, 13*d, a, 13*b),
            (d, c, b, a))


class Flint:
    def __init__(self):
        assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 6*1024**3
        self.lib = C.CDLL('libflint.so.22')
        version = C.string_at(C.addressof(C.c_char.in_dll(self.lib, 'flint_version')))
        assert version.startswith(b'3.'), version
        self.version = version.decode()
        spec = {
            'flint_set_num_threads': ([C.c_int], None),
            'flint_get_num_threads': ([], C.c_int),
            'fmpq_mat_init': ([C.POINTER(Mat), C.c_long, C.c_long], None),
            'fmpq_mat_clear': ([C.POINTER(Mat)], None),
            'fmpq_set_str': ([C.POINTER(Q), C.c_char_p, C.c_int], C.c_int),
            'fmpq_get_str': ([C.c_void_p, C.c_int, C.POINTER(Q)], C.c_void_p),
            'flint_free': ([C.c_void_p], None),
            'fmpq_mat_solve_dixon': ([C.POINTER(Mat)]*3, C.c_int),
            'fmpq_mat_solve_multi_mod': ([C.POINTER(Mat)]*3, C.c_int),
        }
        for name, (args, result) in spec.items():
            fn = getattr(self.lib, name)
            fn.argtypes, fn.restype = args, result
        # Keep native arithmetic within the permanent thread ceiling.
        self.lib.flint_set_num_threads(1)
        assert self.lib.flint_get_num_threads() == 1

    def matrix(self, rows, columns):
        mat = Mat()
        self.lib.fmpq_mat_init(C.byref(mat), rows, columns)
        assert mat.r == rows and mat.c == columns and mat.stride >= columns
        assert bool(mat.entries)
        assert mat.entries[0].num == 0 and mat.entries[0].den == 1
        return mat

    @staticmethod
    def entry(mat, i, j):
        return C.cast(C.byref(mat.entries.contents, (i*mat.stride+j)*C.sizeof(Q)),
                      C.POINTER(Q))

    def set(self, mat, i, j, value):
        if value:
            assert self.lib.fmpq_set_str(self.entry(mat, i, j), str(value).encode(), 10) == 0

    def get(self, mat, i, j):
        pointer = self.lib.fmpq_get_str(None, 10, self.entry(mat, i, j))
        assert pointer
        try:
            return mpq(C.string_at(pointer).decode())
        finally:
            self.lib.flint_free(pointer)

    def solve(self, a, b, method='dixon'):
        """Return x with a*x=b, for row-major K matrices; no input mutation.

        a must be square of order <=300 and b must have <=64 columns.
        These conservative bounds keep this optional pilot isolated.
        Native exact solve returns zero for singular a and raises here.
        """
        n = len(a)
        assert 0 < n <= 300 and all(len(row) == n for row in a)
        assert len(b) == n
        m = len(b[0])
        assert 0 < m <= 64 and all(len(row) == m for row in b)
        assert method in ('dixon', 'multi_mod')
        matrices = []
        try:
            aa = self.matrix(4*n, 4*n)
            matrices.append(aa)
            bb = self.matrix(4*n, m)
            matrices.append(bb)
            xx = self.matrix(4*n, m)
            matrices.append(xx)
            for i, row in enumerate(a):
                for j, value in enumerate(row):
                    if value:
                        block = regular_block(value)
                        for u in range(4):
                            for v in range(4):
                                self.set(aa, 4*i+u, 4*j+v, block[u][v])
            for i, row in enumerate(b):
                for j, value in enumerate(row):
                    for u, component in enumerate(FastField(value)):
                        self.set(bb, 4*i+u, j, component)
            fn = getattr(self.lib, 'fmpq_mat_solve_'+method)
            if not fn(C.byref(xx), C.byref(aa), C.byref(bb)):
                raise ValueError('Singular exact K pivot matrix')
            return [[FastField(tuple(self.get(xx, 4*i+u, j) for u in range(4)))
                     for j in range(m)] for i in range(n)]
        finally:
            for mat in reversed(matrices):
                self.lib.fmpq_mat_clear(C.byref(mat))
