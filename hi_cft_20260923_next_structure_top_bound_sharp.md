# A finite top bound from complete rational-core tops

23 September 2026. This sharpens the earlier bound h<7 to

\[
 \boxed{0\le h\le \frac{938}{169}<6}
\]

for every simple ordinary U-module. It is an exact analytic linear
inequality, with an explicit nonnegative dual certificate; no numerical
job or linear-program solver is needed. The lower bound and uniqueness
of the h=0 module were proved in the preceding top-bound note. Strong
rationality is now established in the separate rationality note.

## Complete T tops and right sl2 compatibility

Let E be the actual finite lowest space of a simple U-module. As proved
in `hi_cft_20260923_next_structure_top_bound.md`, E is contained in
Omega_T(M), is stable under all T zero modes, and is therefore a direct
sum of complete simple Zhu-T modules. This uses regularity of T as a
weak-module statement, even though its conformal vector differs from
omega_U. E is also a finite representation of the left and right sl2
zero modes. The left representation on a T top is trivial at an even
H charge m, and the doublet at an odd m.

The following table gives all actual T-top charge strings. A row with
j>0 denotes a conjugate pair j and -j. It lists the absolute H charges,
the left multiplicity at each charge, and the Potts lowest weight at
each charge. The dimension is for the whole conjugate pair. The
notation 1 and tau specifies the Fibonacci label of T.

| T label | absolute H charges | left multiplicities | Potts weights | pair dimension |
|---|---|---|---|---|
| (1,0) | 0 | 1 | 0 | 1 |
| (tau,0) | 0 | 1 | 2/5 | 1 |
| (1,1) | 1,12 | 2,1 | 2/3,0 | 6 |
| (tau,1) | 1 | 2 | 1/15 | 4 |
| (1,2) | 2 | 1 | 2/3 | 2 |
| (tau,2) | 2 | 1 | 1/15 | 2 |
| (1,3) | 3 | 2 | 0 | 4 |
| (tau,3) | 3,10 | 2,1 | 2/5,1/15 | 6 |
| (1,4) | 4,9 | 1,2 | 2/3,0 | 6 |
| (tau,4) | 4 | 1 | 1/15 | 2 |
| (1,5) | 5,8 | 2,1 | 2/3,2/3 | 6 |
| (tau,5) | 5,8 | 2,1 | 1/15,1/15 | 6 |
| (1,6) | 6 | 1 | 0 | 2 |
| (tau,6) | 6,7 | 1,2 | 2/5,1/15 | 6 |

These are obtained by minimizing

\[
 \frac{m^2}{156}+\frac{\delta_{m\text{ odd}}}{4}
       +h_P(\epsilon,m\bmod3),\qquad m\equiv j\pmod {13}.
\]

The previous note proves it is enough to check |m|<=12. In particular
the tau sectors restore charges 7 and 10; omitting them gives an invalid
bound on the right sl2 highest weight.

For a bound we may average multiplicities with their j -> -j conjugates.
This preserves dimension and the energy traces, and preserves the
nonnegative sl2 character cone. Multiplicities in what follows may
therefore be nonnegative real numbers. Group the rows into variables

\[
\begin{array}{c|ccccccccccc}
\text{variable}&A&B&C&D&E_6&F&G&H&J&I&K\\\hline
\text{rows}&(1,1)&(\tau,3)&(1,4)&(*,5)&(\tau,6)&(1,6)
 &(\tau,4)&(1,3)&(\tau,1)&(*,2)&(*,0).
\end{array}
\]

Here E_6 is a multiplicity variable, distinct from the vector space E.
The two rows merged in D or I have identical K characters; the same
holds for the two rows merged in K. To maximize the Potts trace we may
put all of D and I in Fibonacci label 1, and all of K in label tau.
This is a relaxation, and hence gives a valid upper bound.

Nonnegative right-sl2 multiplicities give the two chains

\[
 K\ge I\ge C+G\ge F+E_6\ge D\ge B\ge A\ge0,
\]
\[
 A+J\ge H+B\ge D\ge E_6\ge C\ge0.
\]

For example, the first compares multiplicities at successive even H
charges 0,2,4,6,8,10,12; the second compares odd charges 1,3,5,7,9
after dividing out the common left-doublet multiplicity.

## Exact trace bound

Put d=dim(E), Q=Tr_E H(0)^2, L=Tr_E omega_left, and P=Tr_E p_1.
The table gives

\[
 d=K+2I+6C+2G+2F+6E_6+6D+6B+6A+4J+4H,
\]
\[
 L=A+B+C+D+E_6+H+J,
\]
\[
 Q=8I+356C+32G+72F+268E_6+228D+236B+292A+4J+36H,
\]
\[
 P\le \frac25K+\frac43I+\frac43C+\frac2{15}G
 +\frac{16}{15}E_6+4D+\frac{26}{15}B+\frac83A+\frac4{15}J.
\]

On a right sl2 representation of highest weight j,
Tr H(0)^2/d=j(j+2)/3, while the right affine Sugawara zero mode
is j(j+2)/164 on the affine top. Thus the original positive stress
identity implies

\[
 h\le \frac{L+\frac{83}{6084}Q+\frac{25}{6}P}{d}
                 +\frac{25}{26}\frac{42}{13}.
\]

Haar averaging does not change these traces. The factor 83/6084 is
exactly (3403/4563)(3/164). The PF13 maximal actual lowest weight is
42/13, as established from the parafermion module formula in the
preceding note.

Here is an explicit dual certificate for the remaining optimization.
Replace P by the displayed upper bound, and write

\[
 R=6084\left(\frac{413}{169}d
               -L-\frac{83}{6084}Q-\frac{25}{6}P\right).
\]

Direct coefficient comparison gives

\[
\begin{aligned}
R={}&4728(K-I)+8712(B-A)\\
 &+26316(F+E_6-D)+10884(H+B-D)\\
 &+2556(C+G-F-E_6)\\
 &+39516H+46296J+17220C+10080E_6+21144G.
\end{aligned}
\]

Every term is nonnegative by the character chains. Therefore

\[
 L+\frac{83}{6084}Q+\frac{25}{6}P\le\frac{413}{169}d,
\qquad
 h\le\frac{413}{169}+\frac{525}{169}=\frac{938}{169}<6.
\]

The relaxed trace inequality is optimal: K=I>0 and all other variables
zero makes R=0. This does not assert that such a T-top configuration
and the maximal PF13 weight occur simultaneously in a U-module.

## Consequence and remaining limitation

B is a finite semisimple U-module. Its irreducible summands have integer
lowest weights, so they start at grades 0 through 5. Thus B is generated
as a U-module by B_0 through B_5, and restriction of U-endomorphisms to
those grades is injective. The same real conformal-weight bound applies
to all nine lattice-sector restrictions.

This reduces a finite all-weight branching target by one grade. It
does not prove that a generation calculation truncated at grade 5 is
complete: excursions above grade 5 can still impose lower-grade
relations. Properness requires an additional invariant submodule,
projection, presentation, or other all-weight certificate.
