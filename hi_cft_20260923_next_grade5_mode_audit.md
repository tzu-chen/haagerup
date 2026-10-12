# Independent source audit of the grade-five lattice mode engine

23 September 2026. Read-only review; no computation or numerical job.
This note audits the formula in
[general_modes_v2](hi_cft_20260923_proof_general_modes_v2.py), before
the selected-target N5 pilot is executed. It is not an assertion that
any selected list exhausts the generated VOA.

For u=h_i(-n)u', the lattice normal-order identity is

    Y(u,z)=:(1/(n-1)!)*partial^(n-1)h_i(z) Y(u',z):.

The coefficient of h_i(k) is
(-1)^(n-1)*binomial(k+n-1,n-1), and the remaining mode is m-n-k.
This is exactly the implemented factor and recursive index. Creation
modes k<0 act after the remaining field; modes k>=0 act on the input
first. The generalized binomial routine is correct for negative k.
The apparent normal-order boundary ambiguity for the derivative field
causes no missing terms: the intervening coefficients vanish.

If the final output grade is T, a negative k intermediate has grade
T+k. Therefore k<-T contributes nothing and the range -T,...,-1 is
complete. For k>=0, h_i(k) lowers the input grade by k; k greater than
that grade contributes nothing. The recursive output grade is then T.
All recursive intermediate grades are consequently at most T, so a
ceiling of five does not truncate a nonzero intermediate needed for
a grade-five result.

The oscillator-free vertex routine has the usual cocycle, contraction
factor -(h_i,alpha), exponent shift by the contracted oscillator mode,
and exponential creation coefficient
prod alpha_i^multiplicity/(mode^multiplicity*multiplicity!). Its
remaining creation degree is at most the output grade, because both
the momentum energy and uncontracted oscillator energy are nonnegative.
The called creation/oscillator enumerators in
[proof_exact4](hi_cft_20260923_proof_exact4.py) have no hard grade-four
restriction despite that module's name. Thus those routines support
grade five without alteration. Each elementary input has one fixed
output momentum, and at grade five at most five oscillators, hence at
most32 contraction masks. No ambient grade-five basis is constructed.

One installation caveat must be handled by the caller: MAX_GRADE is
not part of the vertex cache key. Raising the ceiling after earlier
direct vertex calls could retain a cached empty result. A fresh process
must install grade five before all mode operations, or clear the
vertex/basis-mode caches when changing the ceiling. The selected pilot
must also preserve finite-field conversion and source-authentication
checks independently of this formula audit.

The bounded caches limit stored calls but not all high-level vector
lifetimes. A separate pilot review is still required for field sums,
normal-span rows, row reduction, decoded records and output assembly.
Source correctness does not replace the root-only safe launcher or
the permanent memory and thread limits.

## Selected N5 producer review

The canonical-triplet version of
[next_n5_selected_pilot](hi_cft_20260923_next_n5_selected_pilot.py)
also passes source review. It installs the grade-five engine before
the frozen input reader makes any mode calls, clears previous caches,
and rebinds both module-global recursive functions and the x aliases.
The creation/vertex/basis caches are capped at64/64/128 entries.

The selected targets are mode-zero products of chosen highest
weight-two operators with the three source-bound exact P4 fields.
The normal columns are every current(-1) and translation descendant
of the6007 saved raw N4 words plus the canonical triplet, and every
S2(-1)S3 product from the full120 by956 saved bases, filtered only by
the target Cartan weights. All mode/grade calculations give grade five.
Using all120 S2 rows avoids assuming that lowering within a selected
block captures fields descended from another block.

The P4 exact-control summary, compressed vector bundle and their full
source chains are authenticated. The original N4 SQLite database and
summary are also hash-bound and opened read-only after its writer has
closed. Each accepted column stores its raw vector, reduced vector,
pivot and source recipe. Each target stores its actual raw vector and
the reduction residual, so the experiment can be replayed separately.

The250000-term reduced-row LRU,120000 encountered-state cap,
40000-term row cap,16000000 saved-term cap and512MiB SQLite page cap
bound the growing structures. The32MiB decompression ceiling is
checked before parsing the P4 bundle. The source requires3GiB address
space or less, stops at1GiB process RSS at candidate boundaries, and
the alarm includes input construction. No grade-five ambient basis,
worker or detached process is created. Temporary mode output exists
before its row-cap check, so the hard launcher limit remains essential.

Checkpoint cursors and inserted rows commit atomically. A bounded stop
partway through candidate acceptance may commit additional encountered
state IDs with an unchanged cursor; these unused IDs cause no omitted
candidate on resume. A timeout rolls back the current transaction.

The scope is appropriately explicit. Early successful containment
needs no exhaustion of the column list. Exhaustion covers only the
displayed family, not every possible normal word or all of U5. A
surviving modular residual is not a proof of a new characteristic-zero
strong generator, and successful modular containment is not a
characteristic-zero relation or a properness theorem.

Final source changes were also reviewed: the producer checks target
containment immediately after target construction/resume, and defaults
to source operator7, the three-term highest field of K type(2,14).
Its weight(1,13), combined with the canonical triplet weights(0,2),
(0,0),(0,-2), selects blocks(1,15),(1,13),(1,11). Both changes preserve
the audited mathematics and bounds. The preparing agent froze source
hash9521db8e26e35262eaa6e6e19449776b5642331122d5a8c6951a03fb1ab7e2f1;
root remains responsible for execution and result validation.
