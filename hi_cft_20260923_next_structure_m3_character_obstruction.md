# Harmonic-theta obstructions for both Izumi--Xu center orientations

23 September2026. This note treats precisely the ribbon category
Rep(G2,3 tensor A2,1), with c=8 and the known rank-two extension to
B=V_(E6+A2). The opposite ribbon orientation is treated separately
at the end. The explicit modular matrix identification below shows
that any such VOA V with positive nonvacuum lowest
weights satisfies

\[
 \boxed{\dim V_1=15+A+10B\ge15,}
\]

where A and B are the nonnegative dimensions of the possible module
tops at weights2/7 and1/7, respectively. Thus this orientation cannot
be the proper U, whose current dimension would be six.

## Exact character labels and polar terms

Use the six G2,3 labels1,7,27,77,14,64, with conformal weights
0,2/7,2/3,8/7,4/7,1. These are labels for the modular representation;
the unknown VOA's actual lowest weights may differ by nonnegative
integers from the positive representatives of these twists. Tensor
with the A2,1 vacuum and its two conjugate nonvacuum labels of weight
1/3. Characters of conjugate modules agree. Only the vacuum and the
two labels (7,0),(77,0) can have exponents below zero at c=8. Their
possible negative terms are

\[
 q^{-1/3},\qquad A q^{-1/21},\qquad B q^{-4/21}.
\]

Nonvacuum twist-zero sectors have positive integer lowest weights,
so they do not add poles. A or B is zero when the corresponding
actual lowest weight is larger by at least one.

The extension object B is1 plus(64,0), with the nonvacuum label
uniquely determined by its quantum dimension and twist. Hence the
sum of the1 and64 vacuum-A2 characters is the known B vacuum
character. This is the only branching identity needed below.
The displayed S block gives a modular projection from any actual
character vector onto the complementary four-dimensional G2
representation, tensored with the two-dimensional A2 character
representation. Apply this projection directly, then subtract the
projected affine character vector. No identity for the nonvacuum
B-sector branching characters is assumed.

## The Weil normalization and its important factor two

Put

\[
 v_0=\chi_1-\chi_{64},\quad
 v_1=-\chi_{77},\quad v_2=-\chi_{14},\quad v_3=-\chi_7.
\]

The r labels0,1,2,3 have quadratic values r squared/7 modulo one.
Multiplication by eta^6 identifies this G2 complementary modular
representation with the even Weil representation of the binary
lattice L7 with Gram matrix[[2,1],[1,4]]. For example its S matrix
is−i/sqrt7 times the Fourier matrix on Z7, restricted to even
functions; in collapsed coordinates the nonzero columns have the
factor2 cos(4 pi r s/7). In the G2 matrix before eta^6, this reads

\[
 S_{00}=-1/\sqrt7,\quad S_{0r}=-2/\sqrt7,
 \quad S_{r0}=-1/\sqrt7,\quad
 S_{rs}=-2\cos(4\pi r s/7)/\sqrt7.
\]

The G2 block decomposition is displayed in
[Abhishek--Grover--Jatkar--Singh, Eq.(3.9)](https://arxiv.org/pdf/2312.00275).
The elementary checks S_(1,1)-S_(1,64)=−1/sqrt7 and
S_(1,r)-S_(64,r)=2/sqrt7 fix the signs and normalization above.

After including A2 and multiplying by eta^8, the resulting Weil
representation belongs to the positive rank-four lattice

\[
 L=L7\oplus A2,
 \qquad D_L=\mathbb Z_7(r^2/7)\oplus\mathbb Z_3(s^2/3).
\]

The alternative generator3r gives the equivalent convention2r^2/7.
For an actual-minus-affine character difference delta, its zero
coordinate is2 delta chi_1, because the sum chi_1+chi_64 is fixed.
The three nonzero G2 coordinates are minus their character
differences. Omitting this factor two reverses the resulting current
bound and is an error.

## Two exact harmonic theta series

Write u,v for the L7 basis, so u squared=2, v squared=4, (u,v)=1.
Set w=v-u/2, of norm7/2 and orthogonal to u. For an L7 vector
x=p u+t w, put

\[
 a(x)=p^2,\qquad b(x)=7t^2/4,
\]

and write c(y)=(y,y)/2 for y in A2. The two homogeneous harmonic
quadratics on the four-dimensional Euclidean space are

\[
 H_1=a-b,\qquad H_2=a+b-c.
\]

For each discriminant coset let Theta_H be its theta series with
the summand H(x,y). Poisson summation gives a holomorphic vector
valued modular form of weight4 for the same Weil representation.
The zero-coset constant term vanishes. Dividing by eta^8 therefore
gives weight-zero forms with no vacuum pole.

Their needed coefficients are obtained from the shortest vectors:

| coset and exponent | Theta_H1 | Theta_H2 |
|---|---:|---:|
| r1,s0 at q^(1/7) | −1/7 | 1/7 |
| r3,s0 at q^(2/7) | 3/7 | 4/7 |
| r0,s0 at q^1 | 2 | −4 |
| r0,s1 at q^(1/3) | 0 | −1 |

For the first row the unique shortest vector is2w/7. For the second
row the two shortest vectors have a=1/4,b=1/28. The vacuum row
counts the two L7 roots and six A2 roots. The last row counts three
shortest vectors of A2's nontrivial coset. Root's exact enumeration
uses quadratics2H1 and2H2, so its stored table is twice this table.

## Pole cancellation gives completeness without a dimension formula

Choose scalars lambda,mu so that

\[
 \eta^8\delta v=\lambda\Theta_{H_1}+\mu\Theta_{H_2}
\]

has the required two nonvacuum polar coefficients. Their2 by2
coefficient matrix is invertible. Subtract the right-hand side,
divided by eta^8, from the actual character difference. Every
component is now holomorphic at infinity and throughout the upper
half plane, since eta never vanishes there. The transformation law
makes it holomorphic at every cusp of the finite-index kernel.
A holomorphic weight-zero modular function on that compact modular
curve is constant.

There is no constant invariant vector in this complementary
representation. In the representation before multiplication by
eta^8, the only T-fixed line is r0 tensored with the nonvacuum A2
character; the Fourier S transformation does not preserve this line.
Thus the remainder is zero. This proves the displayed equality
without a Riemann--Roch dimension computation or an assumed
completeness of a theta basis.

## Extract the vacuum coefficient

The affine reference has seven states in the h2/7 top and no h1/7
top. The sign convention gives the exact equations

\[
 (-\lambda+\mu)/7=-B,\qquad
 (3\lambda+4\mu)/7=-(A-7).
\]

Hence

\[
 \lambda=7-A+4B,\qquad \mu=7-A-3B.
\]

The vacuum q^1 coefficient on the theta side is2 lambda-4 mu.
On the character side it is2(dim V1-22), because the affine model
G2,3 tensor A2,1 has22 currents. Therefore

\[
 \dim V_1=22+\lambda-2\mu=15+A+10B.
\]

Both A and B are nonnegative integers, proving the obstruction.

## The opposite ribbon orientation: at least fourteen currents

Conjugate both ribbon factors. The same real S block and the
conjugated twists now identify eta^8 v with the Weil representation
of the negative discriminant form

\[
 D^- =\mathbb Z_7(-r^2/7)\oplus\mathbb Z_3(-s^2/3).
\]

The eta multiplier has the correct central-charge shift: the VOA
under consideration still has c=8. Besides its vacuum, only the
conjugate pair (14,A2-nonvacuum) can have negative character
exponents; its positive twist representative is h=2/21. Let A be
that top dimension, allowing A=0 when its lowest weight is larger.
Conjugate modules again have identical characters.

The form D^- is realized by the positive rank-four lattice with
tridiagonal Gram matrix

\[
 G=\begin{pmatrix}2&-1&0&0\\-1&2&-1&0\\
 0&-1&2&-1\\0&0&-1&6\end{pmatrix},\qquad\det G=21.
\]

Its dual generator eta=G^(-1)e1=(16,11,6,1)/21 has energy8/21.
The map(r,s)→(9r+7s)eta identifies its discriminant form with D^-.
The first three roots span A3. Let P be the harmonic quadratic
norm_(A3) minus3 norm_(A3-perpendicular). The character representation
is even separately under r→−r and s→−s; the lattice theta series
need only be even under their simultaneous reversal. Therefore
project both the ordinary and harmonic theta series to the
separately even subspace, by averaging their (r,s) and (−r,s)
coordinates. Write Theta and Theta_P for these projected series.
This projection commutes with S and T. The modular derivative

\[
 D_2\Theta=q\frac{d}{dq}\Theta-\frac16 E_2\Theta
\]

has weight four for the same Weil representation. Put F=−6D2Theta.
Its zero-coset constant is one, matching eta^8 v0.

There are twelve roots, all in A3. The exact coefficients needed are

| coset and exponent | F | Theta_P |
|---|---:|---:|
| vacuum at q0 | 1 | 0 |
| vacuum at q1 | −84 | 24 |
| polar coset(r2,s1) at q^(2/21) | 3/14 | −2/7 |

Before projection, the class(r2,s1), or4eta, has the unique shortest
vector (1,2,3,4)/21, perpendicular to A3, with norm4/21. Its
polynomial value is−4/7 and its derivative coefficient is
−6(2/21−1/6)=3/7. The paired class(−r2,s1), or10eta, has no vector
of this norm: its fourth coordinate is10/21 modulo integers, so
its perpendicular norm alone is at least
(21/4)(10/21)^2=25/21. Averaging therefore halves both polar
coefficients. The vacuum coordinate is unchanged. For the vacuum row,
Theta0=1+12q+..., so D2Theta0=−1/6+14q+....

The only character pole after the vacuum has coefficient−A in v,
because v's three nonzero G2 components have the minus sign fixed
above. Therefore pole matching requires

\[
 \eta^8v=F+c\Theta_P,\qquad c=(3+14A)/4.
\]

Pole cancellation proves this equality exactly as before, without
assuming the theta series span a whole modular-form space. The
relevant weight-zero representation has no constant invariant. The
original complementary
character exponents are -1/3-r squared/7-s squared/3; none is zero
modulo one for(r,s)=(0..3,0..1), so in this reverse case there is
actually no T-fixed coordinate at all.

The known extension still has86 currents, so the q coefficient of
eta^8(chi1-chi64) is2 dim V1−94. Comparison gives

\[
 2\dim V_1-94=-84+24c,
 \qquad\boxed{\dim V_1=14+42A\ge14.}
\]

Thus this orientation also cannot have six currents.

## Scope still to audit for the near-group alternative

The C-star Izumi--Xu classification has two conjugate choices; see
[Grossman--Jordan--Snyder, Remark4.10](https://ems.press/content/serial-article-files/36806).
Both of their expected center orientations are addressed above.
A classification stated only for C-star categories does not silently
classify every pseudounitary fusion category. These are explicit
remaining scope questions before excluding the entire m=3 boundary
fusion alternative.
