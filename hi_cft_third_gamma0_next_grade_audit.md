# Gamma0 next-grade current coefficients and mandatory descendants

Shared frozen engine: `hi_cft_third_gamma0_next_grade.py`.
Separate pair certificate: `hi_cft_third_gamma0_next_grade_check.py`.
Both use only the standard library. ROOT owns execution; this author
has run no numerical job and edited no existing numerical dependency.

## Exact coefficient formula

Let C0 be column0 of the published characteristic matrix CHI. Let C1 be
the next gamma0 character coefficient in each component, transcribed from
the unnumbered Haagerup display after
[EG equation(2.7)](https://arxiv.org/pdf/1006.1326):

`(120,1250,1377,1377,243,594,292,777,1623,229,347,441)`.

For a current normalized by kappa, write its leading index vector as
`Qlead`, the gamma0 particular vector as Qpart, and
`v=Qlead-Qpart_lead`. The modular calculation already proved

\[
H=q^\Lambda(v+(\mathrm{CHI}+240I)vq+\cdots).
\]

Since `Qpart=E2*chi0/12+D(chi0)/4`, its two relevant coefficients are

\[
B_{0i}=(1/12+\Lambda_i/4)C_{0i}-2\delta_{i0},
\]
\[
B_{1i}=(1/12+(\Lambda_i+1)/4)C_{1i}
       -2C_{0i}-6\delta_{i0}.
\]

The last terms are the contributions from the vacuum pole and the q
and q² coefficients of E2. Multiplying by the A1 level k, every next
ordinary trace index is therefore the exact linear form

\[
t_{{\rm next},i}=kB_{1i}+
\sum_j(\mathrm{CHI}_{ij}+240\delta_{ij})(t_j-kB_{0j}).
\]

Each leading t_j is already a linear form in `(k,tc1,td1,td4)`.
The engine produces and records all twelve next forms. As an independent
hand check, the c1 form reduces to `72k+12tc1`.

**Grade convention:** the vacuum component's C0 and C1 are grades1
and2, because it has a separate grade0 pole. For every nonvacuum
component these are its ground and next grade. The reader distinguishes
these cases explicitly.

## Mandatory affine grade1

A vector in a full module's ground is killed by every positive affine
mode. An integrable SU2_k ground irrep of dimension n has generated
grade1 representation

\[
3\otimes n-\mathbf1_{n=k+1}(n+2).
\]

The subtraction is the grade1 affine singular vector at the boundary
highest weight. For a joint ground `(n,m)` of SU2_k x SU2_l, sum the
grade1 descendants from each factor. With `I_n=n(n²-1)/6`, their
dimension and first-factor ordinary index are

\[
D_1=6nm-\delta_L(n+2)m-\delta_Rn(m+2),
\]
\[
T_{1L}=6mI_n+4nm-\delta_LmI_{n+2}
                         -\delta_R(m+2)I_n,
\]

and similarly with left/right exchanged. Here `deltaL` means `n=k+1`
and `deltaR` means `m=l+1`. The engine independently compares this
formula with Clebsch–Gordan decomposition over many small integrable
labels. Integrability and complete reducibility supply these affine
submodules; no positive coset-energy inequality is added.

The pair certificate knows every3/7/5 decomposition explicitly, so it
uses the exact generated affine grade1 for those grounds. It compares
their dimension and indices with the exact next-grade data. A negative
leftover dimension or trace excludes that witness.

For the vacuum, the correct comparison is grade2:

\[
D_2=27-5\mathbf1_{k=1}-5\mathbf1_{l=1},\quad
T_{2L}=36-20\mathbf1_{k=1},\quad
T_{2R}=36-20\mathbf1_{l=1}.
\]

This follows from six grade2 current generators plus the symmetric
square of the six grade1 currents, subtracting the dimension5 null
in each level1 vacuum module. ROOT independently checked this PBW
count and the `(3,3)` mixed contribution.

## Other ground representations are not fixed by one witness

The larger-ground support report stores only one d5/d6 existence
witness for each required index pair. It would be unsound to treat that
choice as the actual ground decomposition when its grade1 nulls depend
on the choice. The new reader does not do this.

Instead all remaining nonvacuum grounds receive universal lower bounds.
A left boundary constituent is impossible if either `d<k+1` or
`tL<I_(k+1)`. If it is possible, its maximal total dimension subtraction
is at most `d*(k+3)/(k+1)`; its first-index subtraction is at most
`tL*I_(k+3)/I_(k+1)` and its second-index subtraction at most
`tR*(k+3)/(k+1)`. The right boundary has the exchanged bounds.
Subtracting these independent maxima from `6d,6tL+4d,6tR+4d` gives safe
lower bounds, rounded upward to integers and clipped at zero.

These relax correlations between null supports and cannot overstate
the mandatory contribution. If neither boundary is possible, the
three formulas are exact independently of the decomposition. Small
irreps provide direct controls against the exact engine. Nonnegative
remaining indices are necessary, not a representation-existence test.

## Input scope, resources and commands

The reader accepts only a completed d5/d6 report, checks its counts,
role-index table and unchanged producer sources, and preserves the
original energy/parity premises. It adds no new nonvacuum energy
assumption. Input JSON is at most2MiB, with at most400 level pairs and
1000 witnesses; actual orthogonal input has30. There are only twelve
small linear forms and per-witness arithmetic, with no large-grade DP.
Conservative process estimate below100MiB;128MiB guard and30second
alarm. Source/input hashes are rechecked before a new output is promoted.

ROOT independently passed the complete shared engine, coefficient
formula, grade1 null subtractions and vacuum grade2 count. Uniform
independently passed the reader, including the relaxed null-support
bounds and the distinction between a stored existence witness and an
exhaustive ground decomposition.

ROOT executed the orthogonal-input certificate successfully; its actual
output is `hi_cft_third_gamma0_next_grade_results.json`. All30 level pairs
and witnesses survive. Thus this next-grade necessary test adds no
exclusion and does not improve the finite-only lower bound67/22. The
commands below give optional explicit output names; they are not claims
that both named files were executed.

## Why repeating the level-one branching test cannot improve this list

For any level-one factor, the positive leading identity is
`4+9*t_c1+t_d1+3*t_d4=4`. Nonnegative finite indices therefore force all
three free leading indices to zero. The uniqueness calculation for the
quadratic-current modular form then fixes its entire series, independently
of the other commuting current factor. It is exactly the level-one series
already tested by `hi_cft_third_rank3_current_series.py`. Consequently,
repeating that one-factor theta-character inversion on these pairs adds
no new criterion. A joint current moment or another coupling to the second
factor would be new information; extending the identical one-factor
series alone would not resolve that distinction.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_next_grade_check.py --input hi_cft_third_gamma0_d56_orthogonal_results.json --output hi_cft_third_gamma0_next_grade_orthogonal_results.json
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_next_grade_check.py --input hi_cft_third_gamma0_d56_energy_orthogonal_results.json --output hi_cft_third_gamma0_next_grade_energy_results.json
```
