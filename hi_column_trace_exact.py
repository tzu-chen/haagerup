"""Exact scalar-completion certificates using a finite-algebra rank comparison.

Let E be the algebra defined by one Q column and the phase-root equation.
Multiplication by the scalar trace residual H presents E/(H). Its matrix
is computed over the exact number field. Reduction at an integral prime
gives an upper bound on dim E/(H). Separately, exact Singular calculations
compute the dimension after adjoining all Q equations. Equal bounds prove
that adjoining those equations changes no ideal. Cubics are then checked
against that same exact quotient. No numerical roots or HI seeds are used.
"""

import argparse
from collections import defaultdict
from pathlib import Path
import subprocess
import tempfile

import sympy as sp
from sympy.polys.matrices import DomainMatrix

from hi_shintani_ghost import cubic_representatives


def sources(n):
    if n < 3 or n % 2 == 0:
        raise ValueError("require odd n >= 3")
    nr = (n - 1) // 2
    d = sp.Symbol("d")
    names = [f"r{i+1}" for i in range(nr)] + ["w"]
    zero = (0,) * len(names)
    pref = [list(zero) for _ in range(n)]
    for a in range(2, n):
        pref[a] = pref[a - 1].copy()
        pref[a][min(a, n + 1 - a) - 2] += 1

    def B(g, h):
        g, h = g % n, h % n
        if g == h == 0:
            return {zero: d - 2}
        if not g or not h or g == h:
            return {zero: sp.Integer(-1)}
        a, b = sorted((g, h))
        sign = 1 if g < h else -1
        ex = tuple(sign * (pref[b][i] - pref[a][i] - pref[b-a][i])
                   for i in range(len(names)))
        return {ex: sp.Integer(1) if sign == 1 else d}

    def W(a):
        if a == 0:
            return {zero: sp.Integer(-1)}
        ex = [-v for v in pref[a]]
        ex[-1] = a
        return {tuple(ex): sp.Integer(1)}

    def mul(*args):
        result = {zero: sp.Integer(1)}
        for arg in args:
            new = defaultdict(lambda: sp.Integer(0))
            for ex, a in result.items():
                for ey, b in arg.items():
                    new[tuple(x+y for x, y in zip(ex, ey))] += a*b
            result = new
        return result

    def polynomial(terms):
        result = defaultdict(lambda: sp.Integer(0))
        for term in terms:
            for ex, coef in term.items():
                result[ex] += coef
        result = {ex: sp.rem(coef, d*d-n*d-1, d) for ex, coef in result.items()}
        result = {ex: coef for ex, coef in result.items() if coef != 0}
        if not result:
            return "0"
        minima = [min(ex[i] for ex in result) for i in range(len(names))]
        pieces = []
        for ex, coef in sorted(result.items()):
            monomial = "*".join(f"{name}^{e-minimum}" for name, e, minimum
                                in zip(names, ex, minima) if e > minimum)
            pieces.append("(" + str(coef).replace("**", "^") + ")"
                          + ("*" + monomial if monomial else ""))
        return "+".join(pieces)

    all_q, column_q = set(), set()
    for g in range(1, n):
        for h in range(1, n):
            q = polynomial([mul(B(g+a, h), B(h, a)) for a in range(n)])
            if q != "0":
                all_q.add(q)
                if h == 1:
                    column_q.add(q)
    ex = [0] * len(names)
    ex[-1] = n
    root = polynomial([{tuple(ex): sp.Integer(1)}, {tuple(pref[n-1]): -d}])
    terms = [mul(W(a), W(b)) for a in range(n) for b in range(n)]
    terms += [{zero: -2*(d-1)**2}]
    terms += [mul({zero: d-1}, B(a, 2*a)) for a in range(n)]
    trace = polynomial(terms)
    variables = ["w"] + names[:-1] + ["t"]
    header = [f"ring R=(0,d),({','.join(variables)}),(dp(1),dp({nr+1}));",
              f"minpoly=d^2-{n}*d-1;", "option(redSB);"]

    def initial(equations):
        return header + ["ideal I=" + ",".join(sorted(equations))
                         + ",t*" + "*".join(names[:-1]) + "-1;",
                         "ideal J0=std(I);"]

    base = initial(column_q) + ["I=J0," + root + ";", "ideal J=std(I);",
                               "ideal bb=kbase(J);", "int i;",
                               'print("DIM="+string(size(bb)));',
                               'for(i=1;i<=size(bb);i++){print("B="+string(bb[i]));}',
                               "poly H=reduce(" + trace + ",J);",
                               'for(i=1;i<=size(bb);i++){print("H="+string(reduce(H*bb[i],J)));}',
                               'print("BASE_FINISHED");', "quit;"]
    good = initial(all_q) + ["I=J0," + root + "," + trace + ";", "ideal J=std(I);",
                            'print("GOOD_DIM="+string(vdim(J)));',
                            "poly f;", "int failures=0;"]
    reps, coverage = cubic_representatives(n)
    for g, h, k, l in reps:
        terms = [mul(B(a, g+h), B(g, a+k), B(h, a+l)) for a in range(n)]
        terms += [mul({zero: 1-d}, B(g+l, k), B(h+k, l))]
        good += ["f=" + polynomial(terms) + ";",
                 "if(reduce(f,J)!=0){failures=failures+1;}"]
    good += ['print("C_FAILURES="+string(failures));', 'print("GOOD_FINISHED");', "quit;"]
    return "\n".join(base), "\n".join(good), variables, len(reps), coverage


def singular(source, path, timeout, marker):
    path.write_text(source + "\n")
    result = subprocess.run(["Singular", "-q", str(path)], capture_output=True,
                            text=True, timeout=timeout)
    output = result.stdout + result.stderr
    if result.returncode or "?" in output or marker not in output:
        raise ArithmeticError("Exact Singular calculation failed:\n" + output[-2000:])
    return output.splitlines()


def matrix_coefficients(lines, variables):
    btext = [line[2:] for line in lines if line.startswith("B=")]
    htext = [line[2:] for line in lines if line.startswith("H=")]
    N = int(next(line[4:] for line in lines if line.startswith("DIM=")))
    assert len(btext) == len(htext) == N
    symbols, d = sp.symbols(" ".join(variables)), sp.Symbol("d")
    local = {str(s): s for s in symbols}
    local["d"] = d
    ring = sp.QQ.poly_ring(d)
    basis = []
    for text in btext:
        poly = sp.Poly(sp.sympify(text.replace("^", "**"), locals=local), *symbols)
        assert len(poly.terms()) == 1 and poly.coeffs() == [1]
        basis.append(poly.monoms()[0])
    index = {ex: i for i, ex in enumerate(basis)}
    assert len(index) == N
    entries = []
    for j, text in enumerate(htext):
        poly = sp.Poly(sp.sympify(text.replace("^", "**"), locals=local),
                       *symbols, domain=ring)
        for ex, coef in poly.rep.to_dict().items():
            entries.append((index[ex], j, coef.to_dict()))
    return N, entries


def modular_rank(n, N, entries, wanted):
    prime = 32003
    for attempt in range(12):
        roots = sp.sqrt_mod(n*n+4, prime, all_roots=True)
        if roots:
            field = sp.GF(prime)
            residue = field.convert((n+int(roots[0])) * pow(2, -1, prime) % prime)
            matrix = [[field.zero for _ in range(N)] for _ in range(N)]
            integral = True
            for i, j, terms in entries:
                value = field.zero
                for ex, coefficient in terms.items():
                    numerator = int(sp.QQ.numer(coefficient))
                    denominator = int(sp.QQ.denom(coefficient))
                    if denominator % prime == 0:
                        integral = False
                        break
                    value += field.convert(numerator * pow(denominator, -1, prime) % prime) * residue**ex[0]
                if not integral:
                    break
                matrix[i][j] = value
            if integral:
                rank = DomainMatrix(matrix, (N, N), field).rank()
                assert N-rank >= wanted, "rank bound contradicts exact quotient dimension"
                if N-rank == wanted:
                    return prime, int(residue), rank
        prime = int(sp.nextprime(prime))
    raise ArithmeticError("no matching integral modular rank found; no certificate")


def run(n, timeout, directory):
    base, good, variables, reps, coverage = sources(n)
    good_lines = singular(good, directory / f"trace_good{n}.sing", timeout, "GOOD_FINISHED")
    size = int(next(line[9:] for line in good_lines if line.startswith("GOOD_DIM=")))
    failures = int(next(line[11:] for line in good_lines if line.startswith("C_FAILURES=")))
    assert size > 0 and failures == 0
    base_lines = singular(base, directory / f"trace_base{n}.sing", timeout, "BASE_FINISHED")
    N, entries = matrix_coefficients(base_lines, variables)
    if sp.isprime(n):
        assert N == n * sp.binomial(n-1, (n-1)//2)
    prime, residue, rank = modular_rank(n, N, entries, size)
    print(f"n={n}: exact base dimension={N}; exact full-Q-plus-trace dimension={size}", flush=True)
    print(f"  integral reduction p={prime}, d={residue}: exact rank={rank}, nullity={N-rank}", flush=True)
    print(f"  equal dimension bounds prove one-column-plus-trace = full-Q-plus-trace; "
          f"all {reps} cubic orbits vanish ({coverage} cross-free tuples)", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--source-dir", type=Path)
    args = parser.parse_args()
    print("EXACT SCALAR COMPLETION CERTIFICATES; only the listed orders are proved.", flush=True)
    with tempfile.TemporaryDirectory(prefix="hi_trace_exact_") as tmp:
        directory = args.source_dir or Path(tmp)
        directory.mkdir(parents=True, exist_ok=True)
        for n in args.orders:
            try:
                run(n, args.timeout, directory)
            except subprocess.TimeoutExpired:
                raise SystemExit(f"n={n}: timeout; no scalar completion certificate")
    print("ALL REQUESTED EXACT SCALAR COMPLETION CHECKS PASSED", flush=True)


if __name__ == "__main__":
    main()
