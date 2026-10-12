# Enumerating the \(E_8\) current-subalgebra route

This audit enumerates actual finite-dimensional semisimple embeddings in
\(E_8\), with their induced affine levels. It does **not** assume a
denominator of charge six. The first exact scan covers all 1,183 entries
of de Graaf's database and saves their Sugawara charges; the subsequent
filters concern a hypothetical Haagerup fixed VOA and its current
algebra. Neither calculation identifies the physical \(H_3\) chain.

## 1. Objects that must remain distinct

Write
\[
 V=V_{E_8},\qquad W=V^{\mathrm{Hg}},\qquad
 A=\langle W_1\rangle.
\]
The existence of a unitary, strongly rational \(W\) with
\(\operatorname{Rep}W\simeq Z(\mathrm{Hg})\) at \(c=8\) is an assumption.
Conditional on existence, the character data give
\[
 \dim W_1=6+13\gamma,\quad
 \dim W_2=120+78\gamma,\quad
 \dim W_3=956+351\gamma,\qquad \gamma=0,1.
\]
The intrinsic invertible subgroup acts by the unique nonanomalous
order-three action on \(V_{E_8}\); consequently
\[
 W\subset V^\alpha=(A_2)_1\otimes(E_6)_1.
\]
The remaining action is a rank-two hypergroup, rather than an ordinary
automorphism of this affine algebra.
[Gannon–Rayhaun, §4.3, (4.50), (4.54)–(4.55)](https://arxiv.org/html/2606.05279v1).

The two commutants
\[
 C_{\mathrm{fixed}}=\operatorname{Com}(A,W),\qquad
 C_{\mathrm{ambient}}=\operatorname{Com}(A,V_{E_8})
\]
have the same Sugawara complement charge
\[
 c_C=8-c_{\mathrm{Sug}}(A).
\]
Only the first is automatically current-free: every weight-one state
of \(W\) already belongs to \(A\), and the positive current metric
prevents such a state from commuting with \(A\). The ambient
commutant may have additional centralizer currents. A relationship
between either commutant, a full nonchiral CFT, and the specific chain
still needs construction. Finite gauging alone does not subtract
central charge.

## 2. Coverage of the exact enumeration

[de Graaf, Table1 and §1](https://arxiv.org/abs/1004.1972)
classifies proper semisimple \(E_8\) subalgebras up to linear
equivalence: 1,183 classes, of155 abstract Lie types. The
[GAP/SLA database and documentation](https://gap-packages.github.io/sla/doc/chap6.html)
provide sparse generators and the maximal-inclusion graph.
The downloaded input is
\(\texttt{/tmp/hi_cft_sla_sssdb.dat}\), with SHA256

    ecc3908c8803e43624dff0549bb2d409e092f424b30fb1bd3f6ee1952dbba3a2

The scan uses the actual stored simple coroots \(h_i\). In the
normalization where long \(E_8\) roots have square length two, each
simple factor has induced level
\[
 k=\frac12\min_i(h_i,h_i).
\]
This agrees with SLA's DynkinIndex implementation, including the
minimum-coroot convention for nonsimply laced factors. Thus
\[
 c_{\mathrm{Sug}}(\mathfrak k)=
 \sum_j\frac{k_j\dim\mathfrak k_j}{k_j+h_j^\vee}.
\]
The computed Gram matrices independently reconstruct integral Cartan
matrices. Controls include \(A_{1,1}\) with \(E_7\) centralizer,
principal \(A_{1,1240}\) with zero Lie centralizer, and the conformal
\((F_4)_1(G_2)_1\) embedding.

The first scan is in
[the exact parser](hi_cft_sixhour_e8_subalgebra_scan.py) and
[its output](hi_cft_sixhour_e8_subalgebra_results.json).
It passed under the128MiB safe-run guard, with sampled peak RSS
0.031GiB. It retains the complete semisimple list and a **superset**
of reductive completions:928 entries in the denominator interval
\([11/2,13/2]\), and345 entries with total current dimension six or
nineteen. Merely using \(r\leq8-\operatorname{rank}\mathfrak k\) for
an added \(\mathfrak u(1)^r\) overcounts. The refinement below
explicitly corrects that issue.

Linear equivalence is not silently replaced by conjugacy.
[Minchenko, Corollary3, p245](https://pi.math.cornell.edu/~andreim/semsimC.pdf)
states that the only \(E_8\) semisimple-subalgebra exception is a
simple \(A_2\) S-embedded in \(E_6+A_2\), whose linear class splits
into two conjugacy classes. This exception cannot be the
semisimple part of a six- or nineteen-dimensional reductive current
algebra: dimension nineteen would require eleven extra abelian
directions. The full-\(W_1\) filtering therefore has no missing
conjugacy branch from this issue. The broader denominator list must
retain that qualification.

## 3. Exact centralizer and character filters

The additional certificates are implemented in
[the refinement](hi_cft_sixhour_e8_subalgebra_refine.py), with
[exact results](hi_cft_sixhour_e8_subalgebra_refined_results.json).
The refinement passed under the128MiB guard. It certifies795
centralizer ranks and finds563 semisimple entries contained in the
regular \(E_6+A_2\) entry879. An independent agent audited the
centralizer proof and the source conventions.

For a stored embedding \(K\), let \(S\) be the subspace of the
ambient Cartan commuting with every stored raising and lowering
generator. Its rational basis is computed by imposing the root
supports of those generators. The positive-root ordering is
reproduced from GAP's actual construction and checked against
every simple-root weight of every stored generator; coefficients
in cyclotomic fields are never evaluated.

For \(\dim K\leq19\), the exact Lie-centralizer dimension is the
trivial multiplicity of the restricted adjoint:
\[
 \dim Z_{\mathfrak e_8}(K)
 =[e^0]\operatorname{ch}(\mathfrak e_8|_K)
       \prod_{\beta>0}(1-e^{-\beta}).
\]
There are at most eight positive roots of these small \(K\), so this
is a small finite integer calculation. Repeating it on the
zero-\(S\)-weight subspace computes
\(\dim Z_{Z_{\mathfrak e_8}(K)}(S)\). If that dimension equals
\(\dim S\), then \(S\) is self-centralizing in a reductive Lie
algebra and is its Cartan subalgebra. This proves the actual
centralizer rank, rather than guessing it from ambient rank.
Where the certificate does not close, both lower and upper rank
bounds are retained.

The inclusion graph imposes that the semisimple part of \(W_1\)
can occur inside the regular \(A_{2,1}E_{6,1}\) subalgebra. A torus
certified somewhere in \(E_8\) is not automatically certified in
that same fixed algebra. The subsequent
[order-three certificate](hi_cft_sixhour_e8_alpha_certificate.py)
and [its exact output](hi_cft_sixhour_e8_alpha_results.json)
resolve simultaneous containment positively for136 of the157
final rows. The checker enumerates all \(3^8=6561\) ambient
Cartan elements modulo three. Exactly2240 have78 fixed roots,
with fixed-root system \(E_6+A_2\); stored generator supports
and the explicit commuting Cartan torus give a simultaneous
witness. All arithmetic is integral. The other21 rows are
**unresolved by this sufficient search**, not excluded.
The certificate constructs an intrinsic-\(\alpha\) action
fixing the current algebra, not a noninvertible Haagerup action.

For \(m=\dim W_1\), a grade-two character test is
\[
 \dim A_2=\frac{m(m+3)}2-
       \sum_{j:k_j=1}\dim V_{2\theta_j}.
\]
The subtraction is the first integrable affine vacuum null
representation. For the only simple factors of dimension at most
nineteen, the relevant dimensions are
\[
 A_1:5,\quad A_2:27,\quad B_2=C_2:35,\quad G_2:77,\quad A_3:84.
\]
When \(c_C>0\), its independent stress tensor adds one more state
at grade two. The resulting lower bound must not exceed120 or198.

Finally, unitarity of the commuting residual Virasoro algebra
requires
\[
 c_C=0,\qquad c_C\geq1,\qquad\hbox{or}\qquad
 c_C=1-\frac6{m(m+1)},\quad m\geq3.
\]
This excludes nonminimal values strictly between zero and one
without an assumption about chain central charge.

The
[grade-three and quantum-dimension checker](hi_cft_sixhour_e8_character_filter.py)
and [its exact output](hi_cft_sixhour_e8_character_results.json)
also passed under128MiB. Grade-three affine vacuum characters use
root-lattice or even-fermion counts at level one, the first
\(V_{3\theta}\) null at level two, and PBW counting at higher levels.
For \(G_{2,1}\) only a conservative lower bound was used.
The remaining169 entries all pass this grade-three test, so no
additional exclusion is claimed from it.

There is a stronger categorical test when the residual charge is
zero or below one. The canonical decomposition theorem supplies a
conformal subalgebra consisting of the affine simple factors,
a lattice completion of the abelian radical, and a current-free
commutant.
[Mason, Theorem3](https://arxiv.org/html/1110.0544).
At the residual values that survive here, the residual Virasoro
factor is absent, Ising, or the unitary \(c=4/5\) minimal VOA;
it is rational. Thus \(W\) is a finite conformal extension of
the affine, lattice, and Virasoro factors.

Let \(F\) be the field generated by the quantum dimensions of that
product category. For an extension algebra \(B\), any simple local
module \(M\) satisfies
\[
 d_{\mathrm{local}}(M)
 =\frac{d_{\mathrm{product}}(\operatorname{Forget}M)}
        {d_{\mathrm{product}}(B)}\in F.
\]
Consequently a finite local extension cannot enlarge the field of
quantum dimensions. Lattice factors have dimensions one, regardless
of their discriminant or twist conductor. For all twelve remaining
rows with residual \(c=0,1/2,4/5\), the Weyl-sine formula and the
minimal-model sine formula place \(F\) in a cyclotomic field whose
conductor is prime to13. It cannot contain \(\sqrt{13}\), while
\(Z(\mathrm{Hg})\) has dimensions generating that quadratic field.
These twelve rows are therefore excluded under the assumed
strong rationality and unitarity of \(W\).

## 4. Exact residual-charge consequences of these filters

The successive full-current counts are345 before refinement,
169 after centralizer, intrinsic-\(\alpha\), unitarity, and grade-two
tests, unchanged by grade three, and157 after the small-residual
quantum-dimension test. They comprise131 six-current and26
nineteen-current embedding candidates. Every final row has an
explicit commuting torus of the needed rank in \(E_8\), though its
simultaneous placement in the same \(E_6+A_2\) fixed algebra has
only been certified for136 rows by the sufficient search above.

The residual charges in the interval \([3/2,5/2]\) are:

| \(\dim W_1\) | Necessary residual charges |
|---:|---|
| 6 | \(2,\ 65/31,\ 80/37,\ 35/16,\ 68/31,\ 11/5,\ 52/23,\ 25/11,\ 19/8,\ 12/5,\ 17/7,\ 32/13,\ 5/2\) |
| 19 | \(3/2,\ 8/5,\ 17/10,\ 7/4,\ 9/5,\ 13/7,\ 2,\ 11/5,\ 5/2\) |

These are a necessary catalog, not existence claims for Haagerup
fixed algebras. The nearest non-two value is \(65/31\), at distance
\(3/31\), for six currents; for nineteen currents it is \(13/7\),
at distance \(1/7\).
In particular, the following conditional rigidity statement is
exact:
\[
 \boxed{\quad \frac{13}{7}<c_C<\frac{65}{31}
 \quad\Longrightarrow\quad c_C=2\quad}
\]
provided \(C\) is the all-current commutant of the hypothetical
unitary \(c=8\) Haagerup fixed-VOA construction above.
Neither the all-current-coset premise nor a controlled physical
central-charge interval of this strength has been established for
the chain. This is therefore an analytic conditional constraint,
not a determination of its central charge.

## 5. What would constitute a central-charge result

The full-\(W_1\) list gives a finite set of necessary residual
charges for the **specified all-current commutant route**. It
does not restrict every possible noncurrent VOA subalgebra of
\(E_8\), every proper subalgebra of \(W_1\), or every CFT carrying
Haagerup symmetry. To identify the physical chain requires an
explicit hypergroup action, a symmetry-compatible coset/full-CFT
construction, and a comparison with its low spectrum or dynamics.

In the six-current branch this coverage extends further. Any
reductive current subalgebra \(A'\subset W_1\) satisfies
\(c_{\mathrm{Sug}}(A')\leq\dim A'\). If its residual charge
\(8-c_{\mathrm{Sug}}(A')<3\), then
\(c_{\mathrm{Sug}}(A')>5\), forcing
\(\dim A'\geq6=\dim W_1\). Thus \(A'=W_1\).
The six-current catalog therefore covers **every reductive
current denominator with residual charge below three**, not
only a voluntarily chosen all-current subtraction. This does
not cover noncurrent VOA subalgebras. The nineteen-current
branch still permits proper current denominators near two.

There is already a warning against inferring exact two from a
near-two residual charge. A principal \(A_1\) in a regular \(D_5\)
has index60. Three commuting toral directions are available
along the regular \(D_5+A_3\) embedding, while the embedding can
also be placed inside \(E_6+A_2\). Therefore the six-current
possibility
\[
 (A_1)_{60}\oplus\mathfrak u(1)^3,\qquad
 c_{\mathrm{Sug}}=\frac{183}{31},\qquad
 c_C=\frac{65}{31}\simeq2.096774
\]
is an actual current-subalgebra possibility. It is not a
constructed Haagerup fixed algebra. Additional character,
branching, or categorical constraints are needed to remove it.

The previous
[bounded \(c=6\) audit](hi_cft_c6_cosets.md)
is a special slice of the present problem; its direct torus and
standard affine commutants remain useful conditional comparisons.
Its counterexample involving a proper diagonal subalgebra of
\((A_1)_1^6U(1)\) remains relevant: removing all possible proper
denominators by a current-count argument alone is invalid.

There is nevertheless a useful complete statement for a **purely
Cartan six-current denominator**, even when it is proper in \(W_1\).
Let \(H_6\subset W_1\) be six commuting currents, so its Sugawara
charge is six. Put \(R=\operatorname{rank}W_1\). The Lie centralizer
\(Z_{W_1}(H_6)\) is reductive of rank \(R\), and
\[
 \operatorname{Com}(H_6,W)_1
   =Z_{W_1}(H_6)\cap H_6^\perp.
\]
The zero-mode equation gives the centralizer condition; the
first-mode equation gives orthogonality. Since \(H_6\) is central
in its Lie centralizer, the displayed algebra is reductive of
rank \(R-6\).

If \(\dim W_1=19\), then \(R\) is odd because dimension minus rank
is the number of roots. Since \(6\leq R\leq8\), necessarily
\(R=7\). The remaining weight-one Lie algebra has rank one:
\(\mathfrak u(1)\) or \(\mathfrak{su}(2)\), of real dimension one
or three. These are Haagerup-invariant currents. A commuting
ordinary order-three shift has a nonzero fixed vector on this
odd-dimensional real space. Thus the continuum premise that
the chain has no jointly Haagerup- and shift-invariant current
excludes this entire nineteen-current, pure-Cartan subtraction
route. This uses preservation of the indicated invariant sector
by the physical shift, not an unproved identification of every
current with a lattice operator.

With \(\dim W_1=6\), containing \(H_6\) instead forces
\(W_1=\mathfrak u(1)^6\). Hence the pure-Cartan-six route, under
that no-current premise, reduces exactly to the six-current
abelian branch. It still does not exclude proper nonabelian
denominators or identify the remaining coset's full CFT.

An executed exact refinement treats these proper current
denominators explicitly:
[the inclusion checker](hi_cft_sixhour_e8_proper_current_catalog.py)
starts with the 928 denominator rows and pairs them with
surviving full-\(W_1\) hosts. For \(A'\subset H=W_1\), its
semisimple part must lie in the stored inclusion-graph downset
of \(H_{\mathrm{ss}}\), and
\[
 \operatorname{rank}A'\leq\operatorname{rank}H,\qquad
 \dim A'\leq\dim H.
\]
There is an additional exact conformal constraint:
\[
 c_H-c_{A'}=0,\quad c_H-c_{A'}\geq1,\quad\text{or}\quad
 c_H-c_{A'}=1-\frac6{m(m+1)},\qquad m\geq3.
\]
Indeed the difference of the two Sugawara tensors is a
commuting unitary Virasoro tensor. Every retained row records
its possible host and this residual charge. These tests are
necessary only: the graph does not certify that a prescribed
abelian completion can be placed simultaneously inside that
host. The full-current gap around two must not be transferred
to the proper nineteen-current route without examining this
separate catalog.

The checker passed under the128MiB guard.
[Its exact output](hi_cft_sixhour_e8_proper_current_results.json)
retains209 distinct denominator rows. There are14 rows with a
six-current host, all equal to that host, and204 with a
nineteen-current host, of which187 are proper and17 all-current.
Nine denominator rows admit both host types:
\(14+204-9=209\). These are counts of database-embedding and
abelian-rank rows, not numbers of distinct CFTs.

For the nineteen-current branch, the full necessary charge list
in \([3/2,5/2]\), including proper denominators, is
\[
 \frac32,\frac85,\frac{17}{10},\frac74,\frac95,\frac{13}7,
 2,\frac{72}{35},\frac{21}{10},\frac{13}6,\frac{11}5,
 \frac94,\frac{52}{23},\frac{34}{15},\frac{25}{11},
 \frac{23}{10},\frac{33}{14},\frac{12}5,\frac{17}7,
 \frac{86}{35},\frac{32}{13},\frac{37}{15},\frac52.
\]
Combining it with the six-current list gives the broader
conditional implication
\[
 \boxed{\quad \frac{13}{7}<c_C<\frac{72}{35}
       \quad\Longrightarrow\quad c_C=2\quad}
\]
for **any reductive current denominator inside the putative
\(W_1\)**. This follows from a necessary superset, so unresolved
simultaneous toral placements do not invalidate the implication.
The physical chain-to-current-coset premise and a controlled
continuum interval are still needed. Arbitrary noncurrent VOA
denominators are outside this finite catalog.

There is an actual counterexample to transferring that gap.
The proper denominator
\[
 A_{1,3}\otimes\operatorname{diag}(A_{1,1},A_{1,4})_5
       \otimes U(1)^2
\]
inside \(G_{2,1}\otimes A_{1,4}\otimes U(1)^2\) gives
residual charge \(72/35\simeq2.05714\), strictly inside the
all-current gap. Its ambient commutant is
\(K(A_2,2)\otimes M(6,7)^D\), with the tricritical-Potts
extension on the second factor.
[The explicit branching and scalar test](hi_cft_sixhour_e8_72over35.md)
shows that this particular rational construction has forbidden
scalar intervals containing the proposed continuum phi and
epsilon dimensions. It demonstrates the value of testing
proper current embeddings individually while preserving the
distinction between an actual ambient coset and an
unconstructed Haagerup fixed-current algebra.
The output contains only one \(72/35\) denominator row and one
host. Its semisimple centralizer is \(A_2\), whose full Cartan
is unique up to conjugacy. Thus this is the unique ambient
current realization at that charge in the audited class.
The same conclusion does not identify its hypothetical
Haagerup-fixed subalgebra.

## 6. A concrete test at the closest alternative, \(65/31\)

For entry33, the checker certifies index60 and centralizer rank
three. Use the full Cartan of the regular \(A_3\) factor in
\(D_{5,1}A_{3,1}\subset E_{8,1}\) as the abelian part. The lattice
commutant is \(V_{D_5}\), so the resulting ambient coset is exactly
\[
 C_{65/31}=\operatorname{Com}\bigl((A_1)_{60},(D_5)_1\bigr).
\]
This constructs a definite VOA commutant, without asserting its
rationality or a Haagerup action. Ten real free fermions restrict
under the principal \(A_1\) as spin four plus a singlet.
That gives a small exact branching calculation, prepared in
[the character checker](hi_cft_sixhour_d5_principal_coset.py).
It has now passed through numerator grade six under128MiB;
[the output](hi_cft_sixhour_d5_principal_coset_results.json)
gives vacuum coset coefficients \(1,0,2,2,5,7,15\) and confirms
that the tempting scalar match \(8/31\) is absent at the only
required vacuum grade four and affine label30.

There is a useful symmetry qualification. In \(SO(10)\), the
centralizer of the irreducible-nine-plus-one representation of
the principal \(A_1\) is \(\{\pm I\}\); its lift to \(Spin(10)\)
is a two-group. Therefore an inherited order-three element
centralizing the full denominator acts torally and trivially on
the vacuum coset VOA. This observation does **not** by itself
exclude a nontrivial ordinary symmetry on a full CFT: an
invertible line can fix the vacuum chiral algebra and still act
on other modules. A specified GKO full completion and its module
action are needed to make that exclusion.
