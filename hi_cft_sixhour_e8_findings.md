# What the \(E_8\) subalgebra enumeration establishes

The enumeration produces a finite central-charge constraint
and two concrete coset tests. It does not yet determine the
physical Haagerup-chain central charge.

The precise conditional result is
\[
 \boxed{\frac{13}{7}<c<\frac{72}{35}\ \Longrightarrow\ c=2}
\]
if the physical theory comes from subtracting a reductive
current subalgebra inside the putative \(c=8\) Haagerup fixed
VOA in \(E_{8,1}\). Neither that chain-to-coset construction
nor a controlled continuum interval of this strength has
been proved. Arbitrary noncurrent VOA subalgebras are outside
this finite enumeration.

The starting theorem is conditional too: a strongly rational
unitary \(c=8\) VOA with Haagerup-center representation category
must be obtained using a rank-two hypergroup acting on
\(A_{2,1}\otimes E_{6,1}\). Its weight-one dimension is six or
nineteen. This is a characterization, not an existence
construction.
[Gannon–Rayhaun, §4.3](https://arxiv.org/html/2606.05279v1).

We enumerated all1183 semisimple \(E_8\) embedding classes in
the de Graaf/SLA database, computed their actual affine levels,
and retained the full Sugawara-charge list. A denominator of
charge six was not assumed.
[de Graaf](https://arxiv.org/abs/1004.1972),
[GAP/SLA data](https://gap-packages.github.io/sla/doc/chap6.html).
Exact centralizer-rank, low-character, unitary-Virasoro and
quantum-dimension-field filters reduce345 possible full
weight-one algebras to157 necessary candidates. An additional
exact search constructs compatible order-three fixed-algebra
placements for136 of them; its21 failures are unresolved,
not exclusions.

Allowing proper current subalgebras leaves209 denominator
rows in the charge window corresponding to
\(3/2\leq c\leq5/2\):

| Possible full fixed-current algebra | Denominator rows | Proper rows |
|---|---:|---:|
| Dimension6 | 14 | 0 |
| Dimension19 | 204 | 187 |

Nine rows admit both host types, so the union has209 rows.
These count embeddings and toral ranks, not CFTs. The
six-current branch is complete for current denominators
with residual charge below three: a proper current algebra
has dimension at most five and hence Sugawara charge at
most five. The nineteen-current branch admits proper
denominators and gives the upper endpoint \(72/35\) in the
boxed implication.

Two nearby possibilities have now been examined explicitly:

| Residual charge | Ambient current coset | Exact result and remaining premise |
|---|---|---|
| \(65/31\simeq2.09677\) | \(D_{5,1}/A_{1,60}\) | Exact branching through grade6 confirms two stresses and excludes the tempting scalar \(8/31\). The denominator double commutant is the constructed extension \(A_{1,60}\oplus J_{60}\). Coset \(C_2\)-cofiniteness and full category identification remain open here. |
| \(72/35\simeq2.05714\) | \(K(A_2,2)\otimes\) tricritical Potts | This is the unique ambient current coset at that charge in the audited class. All full completions retaining its displayed chiral subalgebra have scalar gaps containing the proposed \(\Delta_\phi\simeq0.13\) and \(\Delta_\epsilon\simeq0.26\). |

For the second row the forbidden open intervals are
\[
 \frac2{21}<\Delta<\frac{16}{105},
 \qquad
 \frac{33}{140}<\Delta<\frac27.
\]
They follow from the exact parafermion and minimal-model
conformal weights; the parafermion field content is also
tabulated in the primary literature.
[Kakashvili–Ardonne, §VII](https://link.aps.org/accepted/10.1103/PhysRevB.85.115116).
Using these gaps to exclude the physical chain requires the
stated continuum limits, not merely finite-size estimates.
Moreover, the commutant inside the Haagerup-fixed VOA can
be smaller than the ambient \(E_8\) commutant and need not
retain the same chiral algebra.

At exact \(c=2\), the catalog initially has42 denominator rows.
An embedding-specific centralizer check removes three impossible
host placements. Every remaining actual ambient current coset
has nonzero weight one. This does not rule out the chain:
the noninvertible Haagerup action can remove ambient currents
from its invariant algebra. The distinction is necessary even
at the most promising charge. The complete39-row necessary
list and fixed-current test are in
[the exact-two audit](hi_cft_sixhour_e8_c2_current_audit.md).

Every executed check uses exact integers or rational
arithmetic and passed in a coordinated128MiB guarded process.
The full reproducible calculations, input hash, coverage
qualifications and source derivations are in
[the enumeration report](hi_cft_sixhour_e8_subalgebras.md),
[the \(65/31\) audit](hi_cft_sixhour_d5_principal_coset.md),
and [the \(72/35\) audit](hi_cft_sixhour_e8_72over35.md).
