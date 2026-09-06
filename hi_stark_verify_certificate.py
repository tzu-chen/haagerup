"""Verify a saved odd-prime-power HI certificate independently of its construction.

Run: python hi_stark_verify_certificate.py hi_stark199_certificate.gp --jobs 16
Composite example: python hi_stark_verify_certificate.py hi_stark25_certificate.gp --jobs 8
Use --structure-only for all checks except the separately batched cubic stage.
Requires PARI/GP, sympy, and numpy (for the index enumeration module).
"""

from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--structure-only", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    path = args.certificate.resolve(strict=True)
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    print(f"certificate_sha256={digest}", flush=True)
    commands = r'''
{
iferr(
  [n,ell,P,d,s,phi,bar,vals,idx]=read(CERTIFICATE_PATH);
  B=matrix(n,n,g,h,vals[idx[g,h]]);
  cert_fac=factor(n);cert_prime=cert_fac[1,1];cert_exponent=cert_fac[1,2];
  hi_check("odd prime power and primitive scalar",n>2&&n%2&&matsize(cert_fac)[1]==1&&znorder(Mod(ell,n))==eulerphi(n));
  hi_check("irreducible monic absolute field",polisirreducible(P)&&pollead(P)==1);
  F=nfinit(P);hi_fast_auts=List();hi_cache_aut(phi);if(phi!=bar,hi_cache_aut(bar));
  hi_check("quadratic dimension",d^2-n*d-1==0);
  hi_check("scalar field automorphism fixes dimension",subst(P,y,Mod(phi,P))==0&&hi_aut(phi,d)==d);
  u=Mod(y,P);for(i=1,eulerphi(n)/2,u=hi_aut(phi,u));
  hi_check("scalar half-power is the stated involution",u==Mod(bar,P)&&hi_aut(bar,Mod(bar,P))==Mod(y,P));
  hi_check("primitive generator inverted by the involution",poldegree(minpoly(s))==poldegree(P)&&hi_aut(bar,s)==1/s);
  hi_check("involution fixed field is totally real",nfinit(minpoly(s+1/s)).sign==[poldegree(P)/2,0]);
  hi_check("all real places have negative dimension",#nfeltsign(F,d)>0&&vecmax(nfeltsign(F,d))==-1);
  hi_check("physical Hermitian symmetry",matrix(n,n,g,h,hi_aut(bar,B[g,h]))==mattranspose(B));
  hi_check("exceptional entries",B[1,1]==d-2&&vecmin(vector(n-1,g,B[1,g+1]==-1&&B[g+1,1]==-1&&B[g+1,g+1]==-1)));
  hi_check("generic norms",vecmin(vector(n^2,i,g=(i-1)\n;h=(i-1)%n;if(g==0||h==0||g==h,1,B[g+1,h+1]*B[h+1,g+1]==d))));
  hi_check("mirror first row",vecmin(vector(n-2,j,B[2,j+2]==B[2,n-j+1])));
  prefix=vector(n,i,1);for(h=2,n-1,prefix[h+1]=prefix[h]*B[2,h+1]);
  hi_check("coherent phase form throughout the upper triangle",vecmin(vector(n^2,i,g=(i-1)\n;h=(i-1)%n;if(g==0||g>=h,1,B[g+1,h+1]==prefix[h+1]/(prefix[g+1]*prefix[h-g+1])))));
  hi_check("rotation symmetry",vecmin(vector(n^2,i,g=(i-1)\n;h=(i-1)%n;B[g+1,h+1]==B[(-h)%n+1,(g-h)%n+1])));
  hi_check("scalar covariance",vecmin(vector(n^2,i,g=(i-1)\n;h=(i-1)%n;hi_aut(phi,B[g+1,h+1])==B[(ell*g)%n+1,(ell*h)%n+1])));
  cert_q_ok=1;Bc=mattranspose(B);
  for(cert_level=-1,cert_exponent-1,h=if(cert_level==-1,0,cert_prime^cert_level);
    for(g=0,n-1,if(sum(j=0,n-1,B[(g+j)%n+1,h+1]*Bc[j+1,h+1])!=(d-1)^2*((g==0)-(h==0)/d),cert_q_ok=0)));
  hi_check("every quadratic equation by scalar-stratum coverage",cert_q_ok);
  hi_compare_old_input(B);
  print("STRUCTURE_AND_QUADRATIC_PASSED n=",n),
  err,print(err);quit(1));
quit(0);
}
'''.replace("CERTIFICATE_PATH", json.dumps(str(path))).replace(r"\u005c", "\\")
    env = os.environ.copy()
    env["HI_STARK_LIBRARY"] = "1"
    result = subprocess.run(["gp", "-q", "-f", str(root/"hi_stark_seedless.gp")],
                            input=commands, text=True, capture_output=True, env=env)
    print(result.stdout, end="", flush=True)
    marker = "STRUCTURE_AND_QUADRATIC_PASSED n="
    if result.returncode or marker not in result.stdout:
        print(result.stderr, file=sys.stderr)
        raise SystemExit("Certificate verification failed")
    n = int(result.stdout.split(marker)[-1].strip())
    if args.structure_only:
        print("Cubic verification is a separate required stage.", flush=True)
        return
    subprocess.run([sys.executable, str(root/"hi_stark_cubic_batches.py"),
                    "--matrix", str(path), "--prime", str(n), "--jobs", str(args.jobs)], check=True)
    print(f"COMPLETE EXACT HI EXISTENCE CERTIFICATE PASSED n={n}", flush=True)


if __name__ == "__main__":
    main()
