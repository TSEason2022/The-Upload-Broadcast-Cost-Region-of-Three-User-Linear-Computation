"""Exact finite fields; integers encode polynomial-basis coordinates.

No floating point arithmetic is used.  For GF(p**m), ``a`` encodes the
coefficients of a polynomial of degree < m as base-p digits, least significant
coefficient first.  In particular, GF(4) arithmetic is NOT arithmetic modulo 4.
Field orders are restricted to unsigned 64-bit integers so primality testing
has a deterministic guarantee. Large fields should supply an irreducible
``modulus``; automatic polynomial discovery has a bounded search budget.
"""
from __future__ import annotations

from functools import lru_cache
from typing import Iterable


def _integer(value: object, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be a Python integer (not bool or float)")
    return value


def _prime(n: int) -> bool:
    """Deterministic Miller--Rabin for n < 2**64."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def _root(n: int, k: int) -> int:
    lo, hi = 1, 1 << ((n.bit_length() + k - 1) // k)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** k <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi ** k == n else lo


@lru_cache(maxsize=128)
def _prime_power(q: int) -> tuple[int, int]:
    if _prime(q):
        return q, 1
    for m in range(2, q.bit_length()):
        p = _root(q, m)
        if p ** m == q and _prime(p):
            return p, m
    raise ValueError(f"{q} is not a prime power")


def _trim(a: Iterable[int]) -> list[int]:
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def _poly_rem(a: Iterable[int], b: Iterable[int], p: int) -> list[int]:
    a, b = _trim(a), _trim(b)
    if not b:
        raise ZeroDivisionError("zero polynomial divisor")
    inv_lead = pow(b[-1], p - 2, p)
    while len(a) >= len(b):
        offset = len(a) - len(b)
        coefficient = a[-1] * inv_lead % p
        for j, bj in enumerate(b):
            a[offset + j] = (a[offset + j] - coefficient * bj) % p
        a = _trim(a)
    return a


def _poly_mulmod(a: Iterable[int], b: Iterable[int], f: tuple[int, ...], p: int) -> list[int]:
    a, b = list(a), list(b)
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % p
    return _poly_rem(out, f, p)


def _poly_powmod(a: Iterable[int], n: int, f: tuple[int, ...], p: int) -> list[int]:
    a, out = list(a), [1]
    while n:
        if n & 1:
            out = _poly_mulmod(out, a, f, p)
        n >>= 1
        if n:
            a = _poly_mulmod(a, a, f, p)
    return out


def _poly_gcd(a: Iterable[int], b: Iterable[int], p: int) -> list[int]:
    a, b = _trim(a), _trim(b)
    while b:
        a, b = b, _poly_rem(a, b, p)
    if a:
        inverse = pow(a[-1], p - 2, p)
        a = [v * inverse % p for v in a]
    return a


@lru_cache(maxsize=128)
def _irreducible(f: tuple[int, ...], p: int) -> bool:
    m = len(f) - 1
    if m == 1:
        return True
    # Rabin criterion: x^(p^m)=x, and gcd(x^(p^(m/r))-x,f)=1
    # for every prime divisor r of m.
    divisors = [r for r in range(2, m + 1) if m % r == 0 and _prime(r)]
    checkpoints = {m // r for r in divisors}
    h = [0, 1]
    for j in range(1, m + 1):
        h = _poly_powmod(h, p, f, p)
        delta = h + [0] * max(0, 2 - len(h))
        delta[1] = (delta[1] - 1) % p
        delta = _trim(delta)
        if j in checkpoints and len(_poly_gcd(delta, f, p)) != 1:
            return False
    return not delta


@lru_cache(maxsize=64)
def _default_modulus(p: int, m: int) -> tuple[int, ...]:
    if m == 1:
        return (0, 1)
    for encoded in range(1, min(p ** m, 100_001)):
        if encoded % p == 0:
            continue
        a, value = [], encoded
        for _ in range(m):
            a.append(value % p)
            value //= p
        f = tuple(a) + (1,)
        if _irreducible(f, p):
            return f
    raise ValueError("automatic irreducible-polynomial search exhausted; provide modulus explicitly")


class Field:
    """A finite field GF(q) with an explicitly fixed polynomial basis.

    ``modulus`` contains coefficients from constant to leading term, is monic,
    has degree log_p(q), and must be irreducible over GF(p). Tables are used
    when q <= 256. Medium extension fields lazily share O(q)-space discrete
    exponent tables up to q=65536; larger fields use polynomial arithmetic.
    Instances are immutable and structurally comparable.
    """
    __slots__ = ("q", "p", "degree", "modulus", "_adds", "_muls", "_invs", "_subs", "_log_data", "_binary_modulus", "_locked")

    def __init__(self, q: int, modulus: Iterable[int] | None = None):
        q = _integer(q, "q")
        if not 2 <= q < 2 ** 64:
            raise ValueError("q must satisfy 2 <= q < 2**64")
        p, m = _prime_power(q)
        if modulus is None:
            f = _default_modulus(p, m)
        else:
            f = tuple(_integer(v, "modulus coefficient") for v in modulus)
            if len(f) != m + 1 or f[-1] != 1 or any(v < 0 or v >= p for v in f):
                raise ValueError("modulus must be monic of the field extension degree with coefficients in GF(p)")
            if not _irreducible(f, p):
                raise ValueError("modulus is reducible over GF(p)")
            if m == 1:
                f = (0, 1)
        self.q, self.p, self.degree, self.modulus = q, p, m, f
        self._binary_modulus = sum(v << i for i, v in enumerate(f)) if p == 2 else 0
        self._adds = self._muls = self._invs = self._subs = self._log_data = None
        if q <= 256:
            self._adds, self._muls, self._invs, self._subs = _small_tables(q, p, m, f)
        self._locked = True

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_locked", False):
            raise AttributeError("Field objects are immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"Field({self.q}, modulus={self.modulus!r})"

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Field) and self.q == other.q and self.modulus == other.modulus

    def __hash__(self) -> int:
        return hash((self.q, self.modulus))

    def validate(self, a: int) -> int:
        a = _integer(a, "field element")
        if not 0 <= a < self.q:
            raise ValueError(f"field element {a} is outside [0, {self.q})")
        return a

    def _add(self, a: int, b: int) -> int:
        if self.degree == 1:
            return (a + b) % self.p
        if self.p == 2:
            return a ^ b
        result, weight = 0, 1
        while a or b:
            result += ((a % self.p + b % self.p) % self.p) * weight
            a, b, weight = a // self.p, b // self.p, weight * self.p
        return result

    def _neg(self, a: int) -> int:
        if self.degree == 1:
            return (-a) % self.p
        if self.p == 2:
            return a
        result, weight = 0, 1
        while a:
            result += (-a % self.p) * weight
            a, weight = a // self.p, weight * self.p
        return result

    def _mul(self, a: int, b: int) -> int:
        if self.degree == 1:
            return a * b % self.p
        if self.p == 2:
            modulus = self._binary_modulus
            result = 0
            while b:
                if b & 1:
                    result ^= a
                b >>= 1
                a <<= 1
                if a & self.q:
                    a ^= modulus
            return result
        aa, bb = [], []
        for _ in range(self.degree):
            aa.append(a % self.p)
            bb.append(b % self.p)
            a //= self.p
            b //= self.p
        coefficients = _poly_mulmod(aa, bb, self.modulus, self.p)
        result = 0
        for c in reversed(coefficients):
            result = result * self.p + c
        return result

    def _power(self, a: int, exponent: int) -> int:
        if self.degree == 1:
            return pow(a, exponent, self.p)
        result = 1
        mul = self._mul if self._muls is None else lambda x, y: self._muls[x][y]
        while exponent:
            if exponent & 1:
                result = mul(result, a)
            exponent >>= 1
            if exponent:
                a = mul(a, a)
        return result

    def add(self, a: int, b: int) -> int:
        self.validate(a); self.validate(b)
        return self._adds[a][b] if self._adds is not None else self._add(a, b)

    def neg(self, a: int) -> int:
        return self._neg(self.validate(a))

    def sub(self, a: int, b: int) -> int:
        self.validate(a); self.validate(b)
        return self._subs[a][b] if self._subs is not None else self._add(a, self._neg(b))

    def _multiplication(self):
        """Return a trusted scalar kernel; public callers must validate first."""
        if self._muls is not None:
            table = self._muls
            return lambda a,b: table[a][b]
        if self.degree > 1 and self.q <= 65536:
            tables = self._log_data
            if tables is None:
                tables = _linear_log_tables(self.q, self.p, self.degree, self.modulus)
                object.__setattr__(self, "_log_data", tables)
            if tables is not None:
                logs, exps = tables
                return lambda a,b: exps[logs[a]+logs[b]] if a and b else 0
        return self._mul

    def mul(self, a: int, b: int) -> int:
        self.validate(a); self.validate(b)
        if self._muls is not None:
            return self._muls[a][b]
        return self._multiplication()(a,b)

    def inv(self, a: int) -> int:
        self.validate(a)
        if a == 0:
            raise ZeroDivisionError("zero has no multiplicative inverse")
        if self._invs is not None:
            return self._invs[a]
        if self.degree > 1 and self.q <= 65536:
            self._multiplication()  # lazily materialize the shared linear table
            if self._log_data is not None:
                logs, exps = self._log_data
                return exps[self.q-1-logs[a]]
        return self._power(a, self.q - 2)

    def pow(self, a: int, exponent: int) -> int:
        self.validate(a); _integer(exponent, "exponent")
        if exponent < 0:
            a, exponent = self.inv(a), -exponent
        return self._power(a, exponent)

    def dot(self, a: Iterable[int], b: Iterable[int]) -> int:
        a, b = tuple(a), tuple(b)
        if len(a) != len(b):
            raise ValueError("dot product lengths differ")
        for x, y in zip(a, b):
            self.validate(x)
            self.validate(y)
        if self.degree == 1:
            return sum(x*y for x,y in zip(a,b)) % self.p
        result = 0
        if self._muls is not None:
            muls, adds = self._muls, self._adds
            if self.p == 2:
                for x,y in zip(a,b):
                    result ^= muls[x][y]
            else:
                for x,y in zip(a,b):
                    result = adds[result][muls[x][y]]
        else:
            mul = self._multiplication()
            for x,y in zip(a,b):
                result = self._add(result,mul(x,y))
        return result

    def axpy(self, a: int, x: Iterable[int], y: Iterable[int]) -> tuple[int, ...]:
        """Return a*x+y without mutation; validate public vectors exactly once."""
        self.validate(a)
        x, y = tuple(x), tuple(y)
        if len(x) != len(y):
            raise ValueError("axpy vector lengths differ")
        for xi,yi in zip(x,y):
            self.validate(xi)
            self.validate(yi)
        if self.degree == 1:
            return tuple((a*xi+yi)%self.p for xi,yi in zip(x,y))
        if self._muls is not None:
            products,adds=self._muls[a],self._adds
            return tuple(adds[products[xi]][yi] for xi,yi in zip(x,y))
        mul = self._multiplication()
        return tuple(self._add(mul(a,xi),yi) for xi,yi in zip(x,y))

    def coeffs(self, a: int) -> tuple[int, ...]:
        """Polynomial-basis coordinates over GF(p), constant coefficient first."""
        self.validate(a)
        output = []
        for _ in range(self.degree):
            output.append(a % self.p)
            a //= self.p
        return tuple(output)

    def from_coeffs(self, coefficients: Iterable[int]) -> int:
        """Pack <= degree base-field coefficients; no polynomial reduction."""
        coefficients = tuple(_integer(c, "base-field coefficient") for c in coefficients)
        if len(coefficients) > self.degree or any(c < 0 or c >= self.p for c in coefficients):
            raise ValueError("invalid polynomial-basis coordinates")
        output = 0
        for c in reversed(coefficients):
            output = output * self.p + c
        return output

    def to_dict(self) -> dict:
        return {"q": self.q, "modulus": list(self.modulus)}

    @classmethod
    def from_dict(cls, data: dict) -> Field:
        return cls(data["q"], modulus=data.get("modulus"))


@lru_cache(maxsize=16)
def _small_tables(q: int, p: int, degree: int, modulus: tuple[int, ...]):
    """Share immutable, byte-packed arithmetic tables by exact representation.

    A bounded cache avoids O(q**2) construction on every Field/JSON load.
    The temporary object bypasses __init__ only to prevent recursive table
    discovery; its parameters have already passed public Field validation.
    """
    raw = object.__new__(Field)
    for key, value in (("q", q), ("p", p), ("degree", degree), ("modulus", modulus)):
        object.__setattr__(raw, key, value)
    object.__setattr__(raw, "_binary_modulus", sum(v << i for i, v in enumerate(modulus)) if p == 2 else 0)
    adds = tuple(bytes(raw._add(a, b) for b in range(q)) for a in range(q))
    muls = tuple(bytes(raw._mul(a, b) for b in range(q)) for a in range(q))
    object.__setattr__(raw, "_muls", muls)
    invs = bytes([0] + [raw._power(a, q - 2) for a in range(1, q)])
    negatives = tuple(raw._neg(b) for b in range(q))
    subs = tuple(bytes(adds[a][b] for b in negatives) for a in range(q))
    return adds, muls, invs, subs


@lru_cache(maxsize=4)
def _linear_log_tables(q: int, p: int, degree: int, modulus: tuple[int, ...]):
    """O(q)-space log/antilog multiplication for medium extension fields.

    Primitive candidates are checked with exact polynomial arithmetic. A
    bounded discovery failure returns None and retains the exact fallback.
    Read-only 16-bit buffers cap one q=65536 table pair near 384 KiB (payload).
    No floating-point logarithms are used: these are discrete exponent indices.
    """
    from array import array
    from ._resources import checkpoint
    raw = object.__new__(Field)
    for key, value in (("q",q),("p",p),("degree",degree),("modulus",modulus),("_muls",None)):
        object.__setattr__(raw,key,value)
    object.__setattr__(raw, "_binary_modulus", sum(v << i for i, v in enumerate(modulus)) if p == 2 else 0)
    order, remaining, factors = q-1, q-1, []
    divisor=2
    while divisor*divisor<=remaining:
        if remaining%divisor==0:
            factors.append(divisor)
            while remaining%divisor==0:
                remaining//=divisor
        divisor+=1
    if remaining>1:
        factors.append(remaining)
    primitive=None
    for candidate in range(2,min(q,258)):
        checkpoint()
        if all(raw._power(candidate,order//factor)!=1 for factor in factors):
            primitive=candidate
            break
    if primitive is None:
        return None
    logs=array('H',[0])*q
    powers=array('H')
    value=1
    for exponent in range(order):
        if exponent%256==0:
            checkpoint()
        logs[value]=exponent
        powers.append(value)
        value=raw._mul(value,primitive)
    if value!=1:
        raise ArithmeticError("discrete-exponent table did not close its multiplicative cycle")
    powers.extend(powers)
    return memoryview(logs.tobytes()).cast('H'),memoryview(powers.tobytes()).cast('H')
