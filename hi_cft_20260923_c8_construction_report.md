# Explicit fields for the c=8 Haagerup candidate

23 September 2026. This continuation follows the user's request to stop
expanding the exclusion search and work constructively on c=8 if the
chain spectrum does not suggest a fresh, credible short list.

**New result:** explicit fields in the lattice VOA
\(B=V_{E_6\oplus A_2}\), over \(\mathbb Q(\sqrt{13},\sqrt{-3})\),
span a 120-dimensional weight-two space with the required current
representations. Its second- and third-pole OPE closure is verified by
exact arithmetic. The entire space can be generated exactly from the
six currents, the ambient stress, and **one explicit three-vertex field**.
The two required commuting coset Virasoro fields are
actual vectors, with charges \(2400/1271\) and \(70/31\). The next-grade
product span has **exact dimension 956**, matching the proposed vacuum
character. Both number-field and independent finite-field calculations
verify this next-grade result.

This constructs concrete generators for a candidate conformal subalgebra.
It does **not** yet prove that the subalgebra they generate has the full
Haagerup character, is strongly rational, or has representation category
\(Z(\mathcal H_3)\). Nor does c=8 identify the continuum limit of the
earlier lattice Hamiltonian, whose estimates were near c=2.

## Why change direction

The expectation that low-lying dimensions can identify a familiar CFT
is reasonable when several precise dimensions, multiplicities, symmetry
assignments, and currents are available together. Here the most useful
scalar is only approximately 0.26, while the central-charge estimates
and proposed current/stress identifications still drift. The exact
defect data principally constrain spins; they do not fix the scaling
dimensions needed for a unique spectral fingerprint.

The immediately suggested guesses have already been tested:
SU(2)_4 offers a scalar of dimension 1/4; Potts products offer 4/15;
tricritical-Ising products offer 11/40. Their further low-lying states
or current content disagree with the current numerical interpretation.
Those comparisons remain conditional on that interpretation and on the
specified construction, rather than global exclusions of their central
charges. See [continuum candidates](hi_cft_continuum_candidates.md),
[product candidates](hi_cft_product_candidates.md), and the
[preceding research report](hi_cft_20260922_research_report.md).
No additional high-confidence shortlist was found this turn.

The c=8 target has considerably more algebraic structure. The literature
places a hypothetical strongly rational Haagerup realization inside
\(E_{6,1}\otimes A_{2,1}\), as the fixed algebra of an appropriate
hypergroup action. This is a conditional characterization, not an
existence theorem: [Gannon–Rayhaun, section 4.3](https://arxiv.org/html/2606.05279v1#S4.SS3).
The repo's [embedding analysis](hi_cft_third_e8_hosts125_187.md)
leaves two current embeddings. This construction treats the one with
\(K=A_{1,1}\otimes A_{1,39}\), previously called host125.

## Ambient algebra and exact conventions

Use eight simple lattice vectors, indexed 0 through 7, with diagonal
Gram entries 2 and off-diagonal -1 on edges
\((0,1),(1,2),(2,3),(3,4),(2,5),(6,7)\).
The lattice cocycle is

\[
 \epsilon(a,b)=(-1)^{\sum_i a_i b_i+
                         \sum_{i>j}a_i b_jG_{ij}}.
\]

The root A1 in E6 has root
\(a_0=(-1,-2,-3,-2,-1,-2,0,0)\).
The other A1 is the diagonal of the principal A1 in A5, of level 35,
and the principal A1 in A2, of level 4. This realizes level 39.

For the exact formulas, use unnormalized simple-root Heisenberg
oscillators. A torus change of basis makes the principal raising
operator \(\sum_i e^{\alpha_i}\) and its lowering operator
\(-\sum_i c_i e^{-\alpha_i}\), with
\(c=(5,8,9,8,5,0,2,2)\). The torus scales the simple-root vertices
by \((1/\sqrt5,1/\sqrt8,1/3,1/\sqrt8,1/\sqrt5,1,
1/\sqrt2,1/\sqrt2)\).

The lattice spaces have dimensions 1, 86, and 1370 through weight two;
there are 78 roots and 702 norm-four vectors. Independent floating
current commutators, adjoints, affine highest-weight multiplicities,
and the four-dimensional commutant stress algebra reproduce the prior
representation-theoretic calculations. The subsequent exact engine
uses rational lattice coordinates and no floating arithmetic.

## Located fields and their CFT data

Let \(e,f\) be the two commuting coset Virasoro fields. Exactly,

\[
 c_e=\frac{2400}{1271},\qquad c_f=\frac{70}{31},\qquad
 \omega_B=\omega_{A_{1,1}}+\omega_{A_{1,39}}+e+f,
\]
\[
 1+\frac{117}{41}+\frac{2400}{1271}+\frac{70}{31}=8.
\]

In addition to the 22-dimensional affine vacuum space at weight two
and the two coset stresses, take the following eight affine highest
vectors and their finite current multiplets. Here \((n,m)\) denotes
finite SU(2) representation dimensions. Every row has total ambient
weight two; each indicated multiplet occurs once.

| Current representation | \(e_1\) weight | \(f_1\) weight |
|---|---:|---:|
| (1,5) | 798/1271 | 38/31 |
| (1,9) | 200/1271 | 42/31 |
| (1,9) | 1512/1271 | 10/31 |
| (1,13) | 420/1271 | 20/31 |
| (2,2) | 192/1271 | 49/31 |
| (2,6) | 1830/1271 | 3/31 |
| (2,8) | 752/1271 | 24/31 |
| (2,14) | 180/1271 | 13/31 |

These contribute 96 states, giving \(22+2+96=120\).
The complementary weights follow from
\(h_f=2-(n^2-1)/12-(m^2-1)/164-h_e\).

One particularly short generator is the (2,14) highest vector:

\[
 u=e^{(0,0,0,0,0,-1,1,1)}
 +\frac{\sqrt{13}+3\sqrt{-3}}{20}
     e^{(0,0,0,1,1,-1,0,0)}
 +\frac{\sqrt{13}-3\sqrt{-3}}{20}
     e^{(1,1,0,0,0,-1,0,0)}.
\]

This formula uses the preceding torus gauge. All eight highest vectors
and e are fully specified in
[the exact field file](hi_cft_20260923_c8_exact_fields.json).
Each coefficient is encoded as two pairs \([a,b],[c,d]\), meaning
\(a+b\sqrt{13}+c\sqrt{-3}+d\sqrt{-39}\).
The other fields are obtained by the explicit current modes and
\(f=\omega_B-\omega_K-e\); no fitting parameters remain.

In the ordinary unitary lattice basis, the same u, up to overall scale,
is the equal-magnitude sum
\(e^a+\zeta e^b+\overline\zeta e^c\), with the three momenta displayed
above and
\[
 \zeta=\frac{\sqrt{13}+3i\sqrt3}{\sqrt{40}},\qquad
 |\zeta|=1,\qquad
 \zeta^2=\frac{-7+3i\sqrt{39}}{20}.
\]
Thus the candidate has a particularly concrete lattice description:
a specified current embedding and a specified relative phase among
three weight-two vertex operators.

More strongly, the [minimal-generator certificate](hi_cft_20260923_c8_minimal_generators.json)
constructs the full 120-dimensional space using only K, the ambient
stress, and the displayed three-term u. Starting with affine vacuum
states, omega, and u, it closes under current zero modes and \(u_1\).
The process reaches dimension 120 and contains every independently
located highest vector and the coset stress e. This construction uses
no numerical field file or coefficient recognition; the saved exact
fields are read only afterward to verify equality. Thus a concise
definition of the candidate is

\[
 U=\langle A_{1,1}\otimes A_{1,39},\ \omega_B,\ u\rangle
       \ \subset\ V_{E_6\oplus A_2}.
\]

The initial continuous problem selected lines in seven real
two-dimensional multiplicity spaces and one three-dimensional space.
Thus nine real angles remained after fixing the stress eigenspaces.
Requiring the unwanted 80 currents to have zero matrix elements within
the proposed weight-two space gave a solution. This was a construction
in one spectral ansatz; neither uniqueness nor exhaustion is claimed.

## What was verified exactly

[The final exact certificate](hi_cft_20260923_c8_exact_unitary_certificate.json)
uses [an independent rational-field mode engine](hi_cft_20260923_c8_exact.py).
It verifies:

- The exact 120-dimensional span and all stated affine-primary and
  stress-eigenvalue identities.
- \(e_1e=2e\), \(e_2e=0\), \(e_3e=1200/1271\), and the corresponding
  complement charge and vanishing mixed modes.
- \(u_1v\) lies in the proposed weight-two space and \(u_2v\) lies in
  the six retained currents. All 768 pairs consisting of one of the
  eight charged highest vectors and any of the 96 charged states are
  checked. Current covariance extends these checks to the full charged
  multiplets. The affine descendants and stress blocks are controlled
  by the exact primary and eigenvalue identities.
- Preservation by the gauge-conjugated ambient PCT operation. In this
  gauge it sends \(e^a\) to \(\prod_i\tilde c_i^{a_i}e^{-a}\), conjugates
  \(\sqrt{-3}\), and changes the sign of each Heisenberg oscillator,
  where \(\tilde c=(5,8,9,8,5,1,2,2)\).

The separate [trace certificate](hi_cft_20260923_c8_trace_certificate.json)
checks three necessary modular predictions exactly:

\[
 \operatorname{Tr}_{S_2}e_1=\frac{67200}{1271},\quad
 \operatorname{Tr}_{S_2}(e_1H_{L,0}^2/2)=\frac{19900}{1271},\quad
 \operatorname{Tr}_{S_2}(e_1H_{R,0}^2/2)=\frac{792900}{1271}.
\]

The exact checks supersede the initial floating fits. Repeated lowering
amplified floating errors; unitary rotations improved the field frame.
Algebraic-number guessing also produced two wrong stress coefficients
that were numerically extremely close. Exact current-annihilation
constraints corrected them, and all final identities were recomputed
without tolerances. Earlier `attempt`, `refined`, `recognize`, and
`seed` files are exploratory records, not final certificates.

## The next-grade test and remaining proof obligations

The ambient weight-three space has dimension 11586. The
[numerical span calculation](hi_cft_20260923_c8_grade3_span.json)
starts with current and translation descendants (dimension 634), adds
the simple-pole products of the located fields, and closes under the
finite current algebra. Its dimension reaches 902 after the (1,5)
generator and 956 after the first (1,9) generator. All other generators
leave it at 956, with the required raising/lowering covariance.
The smallest accepted relative rank residual was about \(9.8\times10^{-5}\);
the largest rejected one was \(2.7\times10^{-9}\).

The [number-field certificate](hi_cft_20260923_c8_grade3_exact_v2.json)
then verifies dimension 956 exactly, including every Cartan-weight
multiplicity. It uses sparse unnormalized oscillator states over
\(\mathbb Q(\sqrt{13},\sqrt{-3})\), with a different ordering of the
generators. Its successive ranks are 634, 924, 953, and 956; all
remaining products preserve that rank. The complete run took about
535 seconds and sampled below 0.2 GiB RSS.
An [independent split-prime calculation](hi_cft_20260923_c8_grade3_modular.json)
at p=1000003 gives the same weight-resolved ranks. That finite-field
calculation alone would prove only a characteristic-zero lower bound;
the number-field run supplies the exact dimension.

The first number-field run completed all generator products at rank
956 but hit its 600-second alarm during an additional raising audit,
before saving its final JSON. The repeated run retained the original
sparse field vectors, reordered generators, and saved the completed
span before any optional redundant audit. The original producer is
archived as `hi_cft_20260923_c8_exact_grade3_v1.py`. No resource caps
were increased.

There is also a direct covariance argument for the construction of this
span. Current zero modes are derivations. For a charged highest vector u,
\(E_0(u_0v)=u_0(E_0v)\), so the initial product span is stable under
raising. Its closure under lowering is consequently stable under the
whole finite current algebra. Moreover,
\((F_0u)_0v=F_0(u_0v)-u_0(F_0v)\), so this closure contains products
with every charged descendant in the first entry. Products with e or f
in the first entry reduce, by skew symmetry, to the tested reversed
products and translation descendants. Products with affine vacuum
states reduce to current and translation descendants. The additional
computer check of raising covariance is therefore an independent audit,
rather than an assumption needed for this argument.

Finally, the [generator-action test](hi_cft_20260923_c8_grade3_action.json)
applies the single three-vertex u to every vector in the numerical
956-dimensional space. It checks
\(u_1S_3\subset S_3\), \(u_2S_3\subset S_2\), and
\(u_3S_3\subset K_1\). Total leakage norms are respectively
\(4.2\times10^{-10}\), \(1.6\times10^{-10}\), and
\(6.1\times10^{-11}\) or smaller. These stability checks are
numerical; the 956-dimensional product-span rank above is exact.

Let U be the vertex subalgebra of B generated by these exact fields and
the six currents. This is now a specified mathematical object with the
ambient conformal vector and inherited unitary structure. Its OPE
associativity and Jacobi identities come from B; they are not an
additional conjecture about abstract structure constants. What remains
is to prove that arbitrary
iterated products do not enlarge the proposed low-weight spaces, and
to control the whole algebra. In particular, neither a finite truncation
nor a matching first few character coefficients proves that U is the
desired proper subalgebra.

The constructive next steps are to prove strong rationality or finite
index, determine the full branching of B over U, and establish the
Haagerup modular category or equivalent relative defect junctions.
An explicit action must satisfy more than the rank-two hypergroup
polynomial: [the earlier bridge analysis](hi_cft_hypergroup_bridge.md)
explains the missing categorical coherence. The second surviving
current embedding was not investigated in this continuation.

## Reproduction and resources

Final exact verification:

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_exact_check.py --closure --output /tmp/c8-exact-recheck.json
```

The output path must be new. This checks the saved explicit coefficients;
it does not depend on rerunning the numerical search or recognition.
The shorter construction can be independently reproduced by

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_minimal_generators.py --output /tmp/c8-generators-recheck.json
```

The complete exact grade-three span can be reproduced with

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- python hi_cft_20260923_c8_exact_grade3.py --output /tmp/c8-grade3-recheck.json
```

It takes several minutes. Its optional `--audit-raising` check is
redundant with the covariance argument and runs after the result is
saved. The default retains the 600-second computation cap.

The exact trace check is in
[hi_cft_20260923_c8_trace_certificate.py](hi_cft_20260923_c8_trace_certificate.py).
All numerical and symbolic jobs used the permanent safe launcher, one
job at a time, at most two CPUs/threads, a 2 GiB or smaller address cap,
and the 32 GiB host reserve. The temporary September 15 exception was
not used. See [the allocation review](hi_cft_20260923_c8_resource_review.md).
The user's existing tracked changes were left untouched.
