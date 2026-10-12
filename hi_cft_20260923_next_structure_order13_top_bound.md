# All U-module tops lie below weight two

23 September 2026. The actual order-thirteen core A_L constructed in
the preceding note gives the exact universal bound

\[
 \boxed{0\le h\le\frac{17}{10}<2}
\]

for every simple U-module. Only U itself has h=0. The new bound implies
that B=V_(E6+A2) is either U or U plus exactly one irreducible U-module
whose lowest space is the complementary 80-dimensional current space.
It does not choose between these alternatives.

## Actual tops of the fourteen A_L modules

Label the simple A_L modules by epsilon=1,tau and a=0,...,6, where
the corresponding even affine label of PF13 is i=2a. Its local
A=T tensor PF13 constituents have pointed charges (j,k) with
k=-5j modulo 13. The order-thirteen extension acts freely on these
thirteen charges, so each pair (epsilon,a) gives one simple local
module and no fixed-point resolution is necessary.

For the representative |k|<=6 the actual PF13 lowest weight is

\[
 h_{PF}(a,k)=\frac{a(a+1)}{15}-\frac{k^2}{13}
                         +\max(0,|k|-a).
\]

This is the usual integrable-affine charge formula: a charge 2k inside
the finite sl2 top costs no affine grade, while |k|>a costs |k|-a.
It is also obtained by substituting the field-identification labels
in the ALY actual-top formula quoted in the preceding notes. PF13
module tops are one-dimensional.

Minimize h_T(epsilon,j)+h_PF(a,-5j) over j modulo13. The table gives
the result and *all* minimizing absolute j values. For j>0 both signs
occur, with the complete T-top characters from the earlier sharp-bound
note.

| label | lowest weight | minimizing absolute j |
|---|---|---|
| x0=(1,0) | 0 | 0 |
| x1=(1,1) | 2/15 | 0 |
| x2=(1,2) | 2/5 | 0,3 |
| x3=(1,3) | 4/5 | 0,2,3,6 |
| x4=(1,4) | 1/3 | 6 |
| x5=(1,5) | 1 | 1,4,6 |
| x6=(1,6) | 4/5 | 4 |
| y0=(tau,0) | 2/5 | 0 |
| y1=(tau,1) | 8/15 | 0,5 |
| y2=(tau,2) | 4/5 | 0,2,3,5 |
| y3=(tau,3) | 1/5 | 2 |
| y4=(tau,4) | 11/15 | 1,2,4,6 |
| y5=(tau,5) | 2/5 | 1,4 |
| y6=(tau,6) | 1/5 | 4 |

Let E be a U-module's lowest space. Regularity gives E⊂Omega_(A_L)(M),
and zero-mode stability makes E a direct sum of complete A_L tops.
Write x_a,y_a for their nonnegative integer multiplicities. This is
the same different-conformal-vector argument audited in the preceding
top-bound notes: every A_L field has its internal weight equal to its
ambient U weight, so all its lowering modes kill E.

## Exact traces and two necessary sl2 inequalities

For each listed top define d=dimension, L=Tr omega_left, Q=Tr H(0)^2,
P=Tr p_1, and Z=Tr z_1. A row's contribution to the U stress trace is

\[
 W=L+\frac{83}{6084}Q+\frac{25}{6}P+\frac{25}{26}Z.
\]

This formula is valid after summing over a complete right-sl2
representation: the affine Sugawara trace is (3/164)Q and its coefficient
in the original positive stress identity is 3403/4563. The displayed
W need not itself be an eigenvalue of an operator on one isolated
A_L top; it is its contribution to the linear trace sum.

An independent check is

\[
 Z=h_{A_L}d-L-Q/156-P,\qquad
 W=\frac1{26}L+\frac7{936}Q+\frac{125}{39}P
                                  +\frac{25}{26}h_{A_L}d.
\]

The exact resulting table is:

| label | d | L | Q | P | 4680 W |
|---|---:|---:|---:|---:|---:|
| x0 | 1 | 0 | 0 | 0 | 0 |
| x1 | 1 | 0 | 0 | 0 | 600 |
| x2 | 5 | 1 | 36 | 0 | 10440 |
| x3 | 9 | 1 | 116 | 4/3 | 56640 |
| x4 | 2 | 0 | 72 | 0 | 5520 |
| x5 | 14 | 2 | 720 | 4 | 148560 |
| x6 | 6 | 1 | 356 | 4/3 | 54240 |
| y0 | 1 | 0 | 0 | 2/5 | 7800 |
| y1 | 7 | 1 | 228 | 4/5 | 36960 |
| y2 | 15 | 2 | 472 | 8/3 | 110880 |
| y3 | 2 | 0 | 8 | 2/15 | 4080 |
| y4 | 14 | 2 | 312 | 8/5 | 81480 |
| y5 | 6 | 1 | 36 | 2/5 | 18240 |
| y6 | 2 | 0 | 32 | 2/15 | 4920 |

Two right-sl2 character inequalities suffice. The multiplicity of H
charge 10 is y2, while that of charge 12 is x5. The multiplicity of
charge 7, after dividing out the common left doublet, is y4; that of
charge 9 is x5+x6. Complete finite sl2 characters therefore imply

\[
 y_2\ge x_5,\qquad y_4\ge x_5+x_6.
\]

Put D=dim E and write W_total for the sum of the table's contributions
with the actual multiplicities. Direct coefficient comparison gives

\[
\begin{aligned}
4680\left(\frac{17}{10}D-W_{total}\right)
={}&8460(y_2-x_5)+28716(y_4-x_5-x_6)\\
 &+7956x_0+7356x_1+29340x_2+14964x_3+10392x_4\\
 &+22212x_6+156y_0+18732y_1+11832y_3\\
 &+1188y_4+29496y_5+10992y_6.
\end{aligned}
\]

Every term is nonnegative. The stress identity gives W_total=hD,
proving h<=17/10. The independent, tiny exact checker
`hi_cft_20260923_next_structure_order13_top_check.py` reconstructs the
table from the lattice/Potts and PF formulas and verifies every dual
coefficient; it must be run under the permanent safe launcher.

## Conditional rank-two branching is now rigorous

Strong rationality makes B a finite semisimple U-module. Its summands
have integer lowest weights. The bound leaves only weights 0 and 1;
the unique weight-zero module is U, occurring once because B_0=C.

The earlier exact current audit gives U=B or U_1 equal to the six
known affine currents. In the second case B_1/U_1 has dimension 80,
and the zero modes of the certified U fields act irreducibly on it.
Every nonvacuum U-summand must have a nonzero top in this quotient.
Irreducibility forces exactly one such simple summand, with multiplicity
one. Thus

\[
 \boxed{U=B\quad\text{or}\quad B=U\oplus X,
       \quad X\text{ simple},\quad h_X=1,\quad\dim X_1=80.}
\]

The remaining properness problem is real: this argument does not prove
that the 80 currents are absent from U itself. It does remove all
possible hidden summands starting in grades two or higher.
