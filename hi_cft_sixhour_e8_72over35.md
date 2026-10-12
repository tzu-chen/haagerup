# A proper-current \(E_8\) construction at \(c=72/35\)

This example shows why the
[all-current gap](hi_cft_sixhour_e8_subalgebras.md)
cannot be applied to every proper current denominator.
It also has an exact low-spectrum test.

Start with the conformal embedding chain
\[
 E_{8,1}\supset E_{6,1}\otimes A_{2,1},
 \qquad E_{6,1}\supset G_{2,1}\otimes A_{2,2},
 \qquad G_{2,1}\supset A_{1,1}\otimes A_{1,3}.
\]
The exceptional embedding and its indices occur in
[Bernard–Thierry-Mieg, Table 10](https://www.ncbi.nlm.nih.gov/ieb/research/acembly/Articles/1987Bernard.pdf);
the current-subalgebra data above independently checks the
ambient embedding indices. The conformal charges agree in
each step, so unitarity makes these conformal embeddings.
Embed \(A_{1,4}\) principally in the external \(A_{2,1}\);
let \(H_2\) be the Cartan of the internal \(A_{2,2}\).
Then the nineteen-current algebra
\[
 H=G_{2,1}\otimes A_{1,4}\otimes H_2,\qquad
 c_H=\frac{34}{5},
\]
contains the proper denominator
\[
 A=A_{1,3}\otimes
       \operatorname{diag}(A_{1,1},A_{1,4})_5\otimes H_2.
\]
Its Sugawara charge and the ambient residual charge are
\[
 c_A=\frac95+\frac{15}{7}+2=\frac{208}{35},
 \qquad c_{\operatorname{Com}(A,E_8)}=\frac{72}{35}.
\]
The internal Sugawara difference is \(c_H-c_A=6/7\),
an allowed unitary minimal charge. These are actual embeddings;
the premise that \(H\) is the entire fixed-current algebra of a
Haagerup action remains unconstructed.

The affine branching also identifies the ambient commutant.
Under \(G_{2,1}\otimes A_{2,2}\), the \(E_6\) vacuum branches as
\((1,1)\oplus(7,8)\), while the nontrivial \(27\) branches as
\((7,3)\oplus(1,\overline6)\), with the conjugate rule for
\(\overline{27}\). The latter branches have nonzero internal
\(A_2\) triality, so no zero Cartan charge survives from the
nonvacuum \(E_6\) branches of \(E_8\).
The displayed affine branches can be checked without assuming
that a finite-dimensional branching extends automatically:
enumerate the integrable modules and their conformal weights.
For the \(E_6\) vacuum only \((1,1)\) and \((7,8)\) have
integral weight; the current count
\(78-14-8=56=7\cdot8\) fixes the latter multiplicity.
At weight \(2/3\), the two indicated branches have total ground
dimension \(21+6=27\).

Under \(A_{1,1}\otimes A_{1,3}\), the \(G_2\) vacuum branches
as labels \((0,0)\oplus(1,3)\); the \(7\) branches as
\((1,1)\oplus(0,2)\). Only the first vacuum branch supplies
an \(A_{1,3}\)-vacuum module. Removing \(A_{1,3}\) and \(H_2\)
therefore leaves
\[
 K(A_2,2)\otimes A_{1,1}\otimes A_{2,1}.
\]
Finally \(A_{2,1}=L_{A_1}(4,0)\oplus L_{A_1}(4,4)\).
The diagonal \(A_{1,5}\) commutant of the first summand is
the unitary Virasoro model \(M(6,7)\), and the second summand
contributes its weight-five simple current \((r,s)=(5,1)\).
Thus the ambient current coset is
\[
 \operatorname{Com}(A,E_{8,1})
 \cong K(A_2,2)\otimes M(6,7)^{D},
\]
where the second factor is the tricritical three-state Potts
chiral algebra. This is a rational construction; it is not a
construction of the required Haagerup action or a choice of
the physical full-CFT completion.

The executed proper-current catalog shows that this is the
**only ambient current commutant at \(72/35\)** in the audited
class, not merely one convenient realization. There is exactly
one denominator row, number174,
\(A_{1,3}\otimes A_{1,5}\oplus U(1)^2\), and exactly one
possible full-current host, number379,
\(A_{1,4}\otimes G_{2,1}\oplus U(1)^2\).
[The exact host witnesses](hi_cft_sixhour_e8_proper_current_results.json)
record both.

The semisimple denominator's Lie centralizer has exact
dimension eight and rank two, hence is \(A_2\).
[The rank certificate](hi_cft_sixhour_e8_subalgebra_refined_results.json)
and [the dimension calculation](hi_cft_sixhour_e8_subalgebra_results.json)
are independent finite checks. The two abelian currents
therefore form a full Cartan of that centralizer. Every such
choice is conjugate by its connected group, fixing the
semisimple denominator pointwise. The only exceptional
linear-equivalence class that splits under conjugacy in
\(E_8\) is a simple \(A_2\), so it does not affect this
\(A_1^2\) embedding.
[Minchenko, Corollary 3](https://pi.math.cornell.edu/~andreim/semsimC.pdf).
This establishes uniqueness of the ambient Heisenberg-current
coset, including its toral choice, within the enumerated scope.

There is an extension-independent necessary spectral test as
long as the displayed chiral subalgebra is retained. The eight
\(K(A_2,2)\) modules have weights \(0\), three copies of \(1/2\),
three copies of \(1/10\), and \(3/5\).
[Kakashvili–Ardonne, §VII](https://link.aps.org/accepted/10.1103/PhysRevB.85.115116).
They can also be obtained from
\(SU(2)_1^3/SU(2)_3\) with center parity and field identification.
The \(M(6,7)\) weights follow from
\[
 h_{r,s}=\frac{(7r-6s)^2-1}{168},\quad
 1\leq r\leq5,\quad1\leq s\leq6,\quad
 (r,s)\sim(6-r,7-s).
\]
Add the two sets modulo one. For any local scalar with
\(\Delta<2\), its chiral weight is \(\Delta/2<1\), so it must
belong to this finite sum set. This includes any non-diagonal
full invariant or local chiral extension retaining both
factors; such operations cannot invent new fractional weights.
The resulting forbidden intervals are
\[
 \boxed{\frac2{21}<\Delta<\frac{16}{105}},\qquad
 \boxed{\frac{33}{140}<\Delta<\frac27}.
\]
They contain respectively the proposed continuum
\(\Delta_\phi\simeq0.13\) and \(\Delta_\epsilon\simeq0.26\).
The exact residue enumeration in
[the checker](hi_cft_sixhour_e8_72over35.py)
has passed under128MiB; [the output](hi_cft_sixhour_e8_72over35_results.json)
records all eight parafermion labels, fifteen Virasoro labels,
and36 distinct chiral residues. It independently verifies both
open intervals.
These are conditional exclusions using continuum limits:
finite-chain gap estimates do not constitute a rigorous
determination of either limit.

This last scope restriction is material. The other commutant
\(\operatorname{Com}(A,W)\) inside a hypothetical Haagerup
fixed VOA can be a proper subalgebra of the ambient coset.
Neither that subalgebra nor a full-CFT gauging is required to
retain \(K(A_2,2)\otimes M(6,7)\). The residue proof therefore
excludes the unique ambient-current realization under the
stated retained-chiral and continuum-spectrum premises; it
does not exclude every conceivable fixed or gauged theory of
the same central charge.
