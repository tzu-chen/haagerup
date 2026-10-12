# Sixth current moments after the two exact survivors

`hi_cft_third_gamma0_sixth_check.py` is a separate, moment-only exact
certificate. It uses the actual E8 placement and the unique full W2
finite representation obtained by the executed factored certificate.
It does not change any earlier producer or run a representation search.

## Normalization and the complete modular space

For SU2 Cartan eigenvalues `1-n,3-n,...,n-1`, put

\[
I_n=\operatorname{Tr}h^2/2,\quad
S_n=\operatorname{Tr}h^4/4,\quad
U_n=\operatorname{Tr}h^6/8
=\frac{n(n^2-1)(3n^4-18n^2+31)}{168}.
\]

The script independently checks these identities by literal finite
Cartan-weight sums for every n from1 through40. Write `S_ab` for
`Tr(h_left^a h_right^b)/8`, where a+b=6. For left/right levels k,l,
the Jacobi Gaussian completion gives

\[
H_{60}=S_{60}-\frac{5k}{4}E_2S_{40}
+\frac{5k^2}{16}E_2^2I_L-\frac{5k^3}{576}E_2^3\chi,
\]

\[
H_{42}=S_{42}-\frac{k}{2}E_2S_{22}
-\frac{l}{12}E_2S_{40}
+\frac{k^2}{48}E_2^2I_R+\frac{kl}{24}E_2^2I_L
-\frac{k^2l}{576}E_2^3\chi.
\]

Here the lower-degree moments retain their earlier normalizations,
`S40=Tr h_left^4/4` and `S22=Tr h_left² h_right²/4`.
The other two polarizations exchange left and right. These identities
are Taylor coefficients of the same Gaussian Jacobi correction used
in the audited quadratic and quartic tests.

Let D_w=D-wE2/12. The particular form uses

\[
P_3=D_4D_2D_0\chi
=D^3\chi-\tfrac12E_2D^2\chi
+(E_2^2/24+E_4/72)D\chi.
\]

Its vacuum polar, weight-one, and weight-two coefficients are
`-1/9,14/9,1276/3`. An independent three-step Serre convolution in
the source checks all three. Therefore the respective particular
forms are `(5k^3/64)P3` and `(k²l/64)P3`.

The complete remaining holomorphic weight-six space is

\[
H_{\rm hol}=(\Delta/E_6)\Xi v,
\qquad (B_i+864I)v=0.
\]

It has dimension6. The E6 denominator has a simple zero at the order-two
elliptic point; the displayed eigencondition selects the matching
vanishing component of Xi. There is no denominator zero at the
order-three elliptic point. At the cusp, Delta cancels the allowed
single pole of Xi. The same fundamental-matrix principal-part argument
as in the earlier M2/M4 certificates proves completeness.
Its first next coefficient is `(chi_matrix+480I)v`.

## Fixed rows and remaining freedom

For each of four polarizations, impose exactly six independently
known representation rows: vacuum weight one, c1/d1/d4 grounds,
the actual b ground, and the unique full W2 representation. The
last includes its affine-vacuum descendants. Its earlier dimension,
both quadratic indices and three quartic moments are recomputed
before its sixth moment is used.

The exact RREF acts directly on twelve components of v together
with the M6 eigencondition. It does not presume the six extra rows
are independent. An inconsistency is a necessary-condition failure;
otherwise every remaining free coefficient is retained in each
predicted ground sixth moment. No selected support witness for
another module is promoted to its exact representation.

The vacuum weight-two quasimodular coefficients include
`E2*S4=S4_next-24*8`, `E2²*I=I_next-48*4`, and
`E2³*chi=120-72*6+1512`. The mixed quartic vacuum weight-one
moment is zero, so its E2 correction vanishes at this step.

## Binding and resources

The two supplied JSON records and the intermediate grade-two moment
record are bound by SHA256. The intermediate record must refer to
the exact supplied quartic bytes. All transitive producer hashes
must match current frozen sources. Input/source bytes are rechecked
before atomic output promotion; existing outputs are refused.

Only eight small exact rational systems are solved. Each has twelve
unknowns and eighteen rows; no tensor, numerical linear algebra,
large-grade partition enumeration, or broad support DP is involved.
The reviewed profile is128MiB with a thirty-second alarm. Each input
is at most2MiB and each source at most128KiB. The author has executed
no numerical job; ROOT owns the numerical slot.

ROOT executed the certificate successfully at22:22:41UTC in
`hi_cft_third_gamma0_sixth_results.json`. Both pairs passed all four
polarizations, with **zero free coefficients** in every system.
Thus all ground sixth moments are fixed under the stated premises.
This does not by itself show that the other module grounds admit
representations with those moments; the separate orbit-support
certificate checks that question exhaustively within explicit caps.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_sixth_check.py --quartic hi_cft_third_gamma0_quartic_results.json --factored hi_cft_third_gamma0_grade2_factored_results.json --output hi_cft_third_gamma0_sixth_results.json
```
