# The remaining commutant is not K(sl3,7)

23 September 2026. This is an analytic argument using the existing exact
stress certificates. No numerical job was launched. The permanent one-job,
6 GiB address, 8 GiB group RSS, 32 GiB host reserve and two-thread limits
remain in force; the September 15 exception is expired.

Put A = T tensor K(sl2,13), with its already certified embedding in U,
and C = Com(A,U). Its conformal vector s has central charge 18/5. The
certified mutually commuting fields q,r in C satisfy s=q+r and
c(q)=32/19, c(r)=182/95. This note rules out a conformal identification
of C with K(sl3,7). It does not rule out a proper conformal subalgebra
K(sl3,7) inside a larger C, because q need not lie in that subalgebra.

## The weight-two algebra, derived without a classification citation

For K=K(sl3,k), k>=2, let e1,e2,e3 be the parafermion stresses associated
to the three positive-root lines of A2. The root stress formula, root
parafermion embeddings, and Weyl action are established in
[Dong–Wang, Sections 3–4, especially (3.3) and Proposition 4.5](https://arxiv.org/html/0909.3872).
In standard normalization,

\[
 e_\alpha=\frac{-k h_\alpha(-2)-h_\alpha(-1)^2
          +2k x_\alpha(-1)x_{-\alpha}(-1)}{2k(k+2)},
 \qquad c(e_i)=\frac{2(k-1)}{k+2}.
\]

At affine grade two the Cartan-zero PBW space has dimension eight:
two Cartan derivatives, three Cartan quadratic monomials, and three
opposite-root products. The rank-two Heisenberg vacuum space contributes
five of these dimensions. Since K1=0, the Heisenberg decomposition gives
dim K2=3. No integrable affine null relation occurs below grade k+1, so
this argument applies at k=7. The three e_i are linearly independent
because each has a different nonzero opposite-root coefficient. Thus
they form a basis of K2.

The Sugawara formula and sum over the three root lines give

\[
 \omega_K=\frac{k+2}{k+3}(e_1+e_2+e_3).
\]

The Weyl action induces all permutations of these three vectors. The
product x*y=x_1 y is commutative because K1=0. For distinct i,j,l,
symmetry therefore forces

\[
 e_i*e_j=a(e_i+e_j)+b e_l.
\]

Use e_i*e_i=2e_i and omega_K*e_i=2e_i. The e_i coefficient gives
((k+2)/(k+3))(2+2a)=2, while the other coefficients give a+b=0.
Consequently

\[
 \boxed{e_i*e_j=\frac{e_i+e_j-e_l}{k+2}}.
\]

This derives the required multiplication directly from the affine
realization and symmetry, with no assumption about a proposed commutant.

## Complete idempotent calculation at k=7

Every Virasoro vector v in K2 obeys v*v=2v. Write
v=x1 e1+x2 e2+x3 e3. The coefficient equations are

\[
 x_i^2+\frac{x_i(x_j+x_l)-x_jx_l}{9}=x_i.
\]

Subtracting two equations gives

\[
 (x_i-x_j)\left(x_i+x_j+\frac29x_l-1\right)=0.
\]

All three coefficients cannot be distinct: the three corresponding
linear factors would force them equal. If all are equal, the equation
is (10/9)x^2=x, yielding v=0 or omega_K. Otherwise reorder them as
(a,b,b), with a!=b. The b equation is (10/9)b^2=b, so b=0 or 9/10;
the difference equation gives a+(11/9)b=1. The two possibilities are
(a,b)=(1,0) and (-1/10,9/10). Thus the complete list of solutions is

\[
 \boxed{0,\quad\omega_K,\quad e_i,\quad\omega_K-e_i
          \quad(i=1,2,3)}.
\]

These are all actual Virasoro vectors, since the complementary coset
stresses commute with e_i. Their possible central charges are

\[
 \boxed{0,\quad\frac{18}{5},\quad\frac43,\quad\frac{34}{15}}.
\]

Under a conformal isomorphism C=K(sl3,7), the exact field q would map
to a weight-two Virasoro vector with central charge 32/19. This is absent
from the complete list, a contradiction. The same contradiction follows
from r. Hence C is not K(sl3,7).

This obstruction is stronger than a central-charge comparison and
independent of the irrational current spectra used to exclude PF17
and the diagonal SU(2) coset. It still does not establish properness,
rationality or the representation category of U.
