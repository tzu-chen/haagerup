# Complete gamma0 ground-trace coordinates

This is algebra from the already executed three-dimensional M2 basis,
not a new modular-form approximation or numerical fit. Coordinates are
in the fixed order0,b,a,c0,c1,c2,d1,d2,d3,d4,d5,d6. The first coordinate
is the vacuum's weight-one trace; all other coordinates are actual
lowest-grade traces in gamma0.

Write A=Q_c1/κ, B=Q_d1/κ and C=Q_d4/κ. The three homogeneous basis
coefficients x,y,z are exactly

    x=3/2−6A,
    y=9/4−B−3C,
    z=−2/13−B+2C.

Substitution into the exact particular solution gives:

| Module | Ground dimension | Conformal weight | Normalized current trace |
|---|---:|---:|---|
|0, grade1|6|1|4−9A−B−3C|
|b|80|1|20−9A+B+3C|
|a|81|1|18+9A|
|c0|81|1|18+9A|
|c1|3|1/3|A|
|c2|27|2/3|6−6A|
|d1|7|6/13|B|
|d2|42|11/13|10+B−4C|
|d3|119|15/13|30+9C|
|d4|5|5/13|C|
|d5|13|7/13|4−B−3C|
|d6|14|8/13|2−B+2C|

Ground dimensions and weights are read from the unnumbered Haagerup
character display following Eq(2.7), printed page22 of
[Evans–Gannon](https://arxiv.org/pdf/1006.1326). In particular d3 in
gamma0 starts at15/13, whereas gamma1 has the additional lower polar
state. The table is a gamma0 statement and must not mix these cases.

For an A1 factor at level k, let a,b,c denote its ordinary finite
Dynkin indices on c1,d1,d4, using t(n)=n(n²−1)/6. Multiplying the table
by k and imposing the vacuum trace4 gives

    4+9a+b+3c=4k,
    t_b=20k−9a+b+3c,
    t_a=t_c0=18k+9a,
    t_c2=6k−6a,
    t_d2=10k+b−4c,
    t_d3=30k+9c,
    t_d5=4+9a,
    t_d6=2k−b+2c=4−2k+9a+5c.

These formulas hold for each factor in A1×A1 simultaneously. Existence
of a representation of the indicated total dimension with the required
pair of indices is necessary. Checking each module independently is
still a relaxation: neither fusion compatibility nor consistent affine
branching across grades is asserted. Nonnegative traces immediately
give a≤k and the other displayed inequalities, including t_d6≥0.

The [odd-grade bilinear argument](hi_cft_third_odd_ground_bilinear.md)
requires symmetric finite representations for every displayed nonvacuum
module except b on the currently used character-coefficient evidence.
For d2 and d6 this follows from their next-grade dimensions777 and441.
Thus each SU2×SU2 irrep(n,m) with n+m odd has even multiplicity in those
modules. The constraints remain finite-representation statements; energy
inequalities require the separate module-positivity premise.

Status: hand substitution completed against every entry of the executed
basis and particular vector. Uniform independently reproduced the three
solved coordinates and all twelve table entries, with PASS. No new code
or numerical job is part of this note.
