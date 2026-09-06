"""Complete the cubic checks for a previously checked exact matrix checkpoint.

Example:
  HI_STARK_CASES='[199]' HI_STARK_MATRIX_CHECKPOINT=/tmp/hi199.bin \
    HI_STARK_STOP_AFTER_MATRIX=1 gp -q -f hi_stark_seedless.gp
  python hi_stark_cubic_batches.py --matrix /tmp/hi199.bin --prime 199 --jobs 16

This is the final stage of that construction, not a replacement for its
field, phase-form, covariance, and quadratic checks. All arithmetic is
exact. Independent local GP processes check disjoint complete index ranges.
"""

from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import tempfile
import time

from hi_beta_reductions import beta_representatives


def source(matrix, reps_file, p, start, end):
    return f"""
default(parisizemax,4000000000);
default(nbthreads,1);
default(threadsizemax,536870912);
data=read({json.dumps(str(matrix))});
if(#data==9,[n,ell,P,d,s,phi,bar,vals,idx]=data;B=matrix(n,n,g,h,vals[idx[g,h]]),[n,ell,P,d,s,phi,bar,B]=data);
if(n!={p},error("wrong matrix order"));
DD=lcm(denominator(B,1),denominator(d,1));
IB=DD*B;IBc=mattranspose(IB);ID=DD*(d-1);
if(type(DD)!="t_INT" || DD<1 || denominator(IB,1)!=1 || denominator(ID,1)!=1,error("denominators were not cleared"));
reps=read({json.dumps(str(reps_file))});
ci(q)={{my(g=q[1],h=q[2],k=q[3],l=q[4]);
  sum(j=0,n-1,IB[j+1,(g+h)%n+1]*IBc[(j+k)%n+1,g+1]*IBc[(j+l)%n+1,h+1])
  ==ID*IB[(g+l)%n+1,k+1]*IB[(h+k)%n+1,l+1]}};
{{iferr(for(i={start+1},{end},if(!ci(reps[i]),error(Str("failed at ",reps[i])))),
  err,print(err);quit(1));
print("EXACT BATCH PASSED {start}:{end}");quit(0);}}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, required=True)
    parser.add_argument("--prime", "--order", dest="prime", type=int, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    matrix = args.matrix.resolve(strict=True)
    digest = hashlib.file_digest(matrix.open("rb"), "sha256").hexdigest()
    reps, scalar_count = beta_representatives(args.prime)
    jobs = min(args.jobs, len(reps))
    print(f"n={args.prime}; matrix_sha256={digest}", flush=True)
    print(f"{scalar_count} enumerated cross-free tuples; {len(reps)} beta representatives; {jobs} batches", flush=True)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="hi_cubic_batches_") as tmp:
        root = Path(tmp)
        reps_file = root/"reps.gp"
        reps_file.write_text(str([list(q) for q in reps]))

        def run_batch(index):
            start, end = len(reps)*index//jobs, len(reps)*(index+1)//jobs
            path = root/f"batch_{index}.gp"
            path.write_text(source(matrix, reps_file, args.prime, start, end))
            result = subprocess.run(["gp", "-q", "-f", str(path)], capture_output=True, text=True)
            marker = f"EXACT BATCH PASSED {start}:{end}"
            if result.returncode or marker not in result.stdout or "***   at top-level" in result.stderr:
                raise RuntimeError(f"batch {index} failed\n{result.stdout}\n{result.stderr}")
            return start, end

        covered = []
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            futures = [pool.submit(run_batch, index) for index in range(jobs)]
            for future in as_completed(futures):
                start, end = future.result()
                covered.append((start, end))
                print(f"[ok] exact cubic range [{start},{end}); elapsed_s={time.monotonic()-started:.1f}", flush=True)
        covered.sort()
        assert covered[0][0] == 0 and covered[-1][1] == len(reps)
        assert all(left[1] == right[0] for left, right in zip(covered, covered[1:]))
    print("ALL CUBIC EQUATIONS CERTIFIED BY COMPLETE BALANCED-BETA ORBIT COVERAGE", flush=True)


if __name__ == "__main__":
    main()
