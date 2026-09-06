"""Exact small-order tests of whether the quadratic phase ideal implies C.

Run: python hi_quadratic_ideal.py
Composite check: python hi_quadratic_ideal.py --orders 9 --timeout 300
Larger experiment: python hi_quadratic_ideal.py --orders 11 --timeout 300
Requires Singular and sympy. The default cases are 3, 5, 7.

The ring is Q(d)[c_1,...,c_(p-1)], d^2=p*d+1, with c_0=-1.
The variables are c_g=sqrt(d)*b_g, so c_g*c_(-g)=d. The program
tests actual ideal membership, not just vanishing at numerical roots.
"""

from pathlib import Path
import argparse
import subprocess
import tempfile

from hi_beta_reductions import balanced_pair, beta_representatives


def singular_source(p):
    x = ["(-1)"]+[f"x{i}" for i in range(1, p)]

    def mon(indices):
        return "*".join(x[i % p] for i in indices)

    polys = [f"x{i}*x{p-i}-d" for i in range(1, (p+1)//2)]
    for g in range(1, p):
        for h in range(1, p):
            polys.append("+".join(mon((m, h-m, -m-g, m+g-h)) for m in range(p)))
    out = [f'ring R=(0,d),({",".join(x[1:])}),dp;',
           f"minpoly=d^2-{p}*d-1;", f'ideal I={",".join(polys)};',
           "option(redSB);", "ideal J=std(I);",
           'print("basis_size="+string(size(J)));',
           'print("quotient_dimension="+string(vdim(J)));',
           "poly f;", "int failures=0;"]
    reps, _ = beta_representatives(p)
    for quad in reps:
        a, c = balanced_pair(quad, p)
        S = "+".join(mon([m+t for t in a]+[-m+t for t in c]) for m in range(p))
        P = mon([i+j for i in a for j in c])
        out += [f"f=d^2*({S})-(d-1)*({P});",
                "if(reduce(f,J)!=0){failures=failures+1;}"]
    out += [f'print("beta_representatives={len(reps)}");',
            'print("membership_failures="+string(failures));',
            'if(failures==0){print("EXACT IDEAL MEMBERSHIP PASSED");}', "quit;"]
    return "\n".join(out)+"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", "--primes", dest="primes", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--source", type=Path, help="write the source for one odd order without running")
    args = parser.parse_args()
    if args.source:
        if len(args.primes) != 1:
            parser.error("--source requires exactly one odd order")
        args.source.write_text(singular_source(args.primes[0]))
        return
    for p in args.primes:
        with tempfile.TemporaryDirectory(prefix="hi_qideal_") as tmp:
            path = Path(tmp)/f"order_{p}.sing"
            path.write_text(singular_source(p))
            try:
                result = subprocess.run(["Singular", "-q", str(path)],
                                        capture_output=True, text=True, timeout=args.timeout)
            except subprocess.TimeoutExpired:
                raise SystemExit(f"n={p}: timeout; no implication has been established")
        output = result.stdout+result.stderr
        print(f"CASE n={p}\n{output}", end="")
        if result.returncode or "EXACT IDEAL MEMBERSHIP PASSED" not in output or "?" in output:
            raise SystemExit("The exact ideal-membership check did not pass")
    print("ALL REQUESTED QUADRATIC-IDEAL CHECKS PASSED")


if __name__ == "__main__":
    main()
