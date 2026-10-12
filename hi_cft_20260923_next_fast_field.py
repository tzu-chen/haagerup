"""Exact GMP arithmetic for Q(sqrt(13),sqrt(-3)); opt-in, never implicit.

This replaces coefficient arithmetic only. Frozen lattice mode producers
remain unchanged. Consumers must bind this source and rerun their controls.
The basis is (1,s,t,s*t), with s*s=13 and t*t=-3.
"""
from fractions import Fraction

from gmpy2 import mpq


def rational(value):
    if isinstance(value, Fraction):
        return mpq(value.numerator, value.denominator)
    return mpq(value)


class FastField(tuple):
    def __new__(cls, value=0):
        if isinstance(value, cls):
            return value
        if isinstance(value, (tuple, list)):
            assert len(value) == 4
            return tuple.__new__(cls, tuple(rational(v) for v in value))
        return tuple.__new__(cls, (rational(value), mpq(0), mpq(0), mpq(0)))

    def __bool__(self):
        return any(self)

    def __add__(self, other):
        other = FastField(other)
        return FastField(tuple(a+b for a, b in zip(self, other)))

    __radd__ = __add__

    def __neg__(self):
        return FastField(tuple(-a for a in self))

    def __sub__(self, other):
        other = FastField(other)
        return FastField(tuple(a-b for a, b in zip(self, other)))

    def __rsub__(self, other):
        return FastField(other)-self

    def __mul__(self, other):
        other = FastField(other)
        if not self or not other:
            return ZERO
        a, b, c, d = self
        e, f, g, h = other
        if not (f or g or h):
            return FastField((a*e, b*e, c*e, d*e))
        if not (b or c or d):
            return FastField((a*e, a*f, a*g, a*h))
        return FastField((a*e+13*b*f-3*c*g-39*d*h,
                          a*f+b*e-3*c*h-3*d*g,
                          a*g+c*e+13*b*h+13*d*f,
                          a*h+d*e+b*g+c*f))

    __rmul__ = __mul__

    def conj(self, mask):
        assert 0 <= mask <= 3
        return FastField(tuple(-v if (i & mask).bit_count() % 2 else v
                               for i, v in enumerate(self)))

    def inv(self):
        if not self:
            raise ZeroDivisionError
        a, b, c, d = self
        if not (b or c or d):
            return FastField(1/a)
        # Norm over t, followed by norm over s. This is exact rational
        # arithmetic, not an embedding or approximate algebraic inversion.
        norm0 = a*a+13*b*b+3*c*c+39*d*d
        norm1 = 2*a*b+6*c*d
        denominator = norm0*norm0-13*norm1*norm1
        assert denominator
        return FastField(((a*norm0-13*b*norm1)/denominator,
                          (b*norm0-a*norm1)/denominator,
                          (-c*norm0+13*d*norm1)/denominator,
                          (c*norm1-d*norm0)/denominator))

    def __truediv__(self, other):
        return self*FastField(other).inv()

    def __rtruediv__(self, other):
        return FastField(other)*self.inv()


ZERO = FastField(0)
ONE = FastField(1)


def install(module):
    """Install in one isolated exact-mode consumer, clearing mode caches.

    Calling this after a finite-prime installation is explicitly rejected:
    residues cannot be lifted back to number-field coefficients.
    """
    assert isinstance(module.ONE, tuple) and len(module.ONE) == 4
    for name in ('creation', 'vertex', 'basis_mode'):
        function = getattr(module, name)
        if hasattr(function, 'cache_clear'):
            function.cache_clear()
    module.LEFT = tuple({state: FastField(tuple(c)) for state, c in vector.items()}
                        for vector in module.LEFT)
    module.RIGHT = tuple({state: FastField(tuple(c)) for state, c in vector.items()}
                         for vector in module.RIGHT)
    module.A, module.ONE, module.ZERO_A = FastField, ONE, ZERO
    module.VAC = {(module.ZERO, ()): ONE}
