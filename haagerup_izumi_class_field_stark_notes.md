# Haagerup–Izumi \(\mathbb Z_n\): transparent \(F\)-symbols, class fields, and Stark-unit route

## Purpose

This is a research handoff summarizing the current working picture for cyclic Haagerup–Izumi fusion categories in the transparent gauge, with emphasis on:

1. reducing the \(F\)-symbol system to one core matrix \(A\);
2. the exact algebraic reconstruction for the \(\mathbb Z_{17}\) Q-system branch;
3. evidence that the generic \(F\)-symbol field is a ray class field of
   \[
   K_p=\mathbb Q\!\left(\sqrt{p^2+4}\right);
   \]
4. the candidate relation between normalized \(F\)-symbols and Stark units;
5. reproducible PARI/GP tests and the remaining analytic construction problem;
6. exact construction without HI seeds, uniform cocycle/sign reductions,
   and an infinite family of arithmetic inputs over one quadratic field.

Some statements below are exact consequences of the transparent-gauge identities or exact algebraic manipulations. Others are computational conjectures based on reconstruction from published Evans–Gannon numerical seeds and should be independently verified. The progress entries record their status when written; the latest theorem in Section 111 supersedes the earlier statements that infinitude is unresolved.

> **Infinitude of complex categorifications (2026-09-07).** Section 111 proves existence of cyclic Haagerup--Izumi spherical fusion categories for every \(n=2^m+1\), \(m\ge1\), and more generally whenever \(-1\in\langle2\rangle\) modulo n. A four-gamma contour difference proves the admitted Fourier components of C; induction eliminates the remaining consecutive frequency block. A signed ordered normal form and the exact Frobenius action then cover every cubic. Algebraic conjugation gives pseudo-unitary categorifications as well. **Unitarity is not proved.** The proof has exact Laurent and combinatorial audits, with separate numerical normalization checks.

> **The first lift equations have a precise character law (2026-09-07).** Section 109 expresses the first Q-lift error as a Witt carry plus squared formal derivatives of Q. Before imposing Frobenius, its summands have different cyclic character weights; an explicit order-3 example shows that vanishing in the canonical gauge does not imply vanishing after character twists. Thus Fourier projection cannot supply extra lift equations without an additional argument. Adding the actual lift equations gives shorter replayed certificates at 7, 9 and 11, but an exact separator rules out multiplier degree 2 already at 13. No uniform completion identity, and no infinitude theorem, is established.

> **Frobenius certificates and a uniform lower bound (2026-09-07).** Section 108 uses the full finite norm/Frobenius coordinate algebra. Every cross-free cubic orbit through odd order 13 has a replayed Q certificate with phase-multiplier degree at most 3. Degree 3 fails at 15, with a one-coordinate separating functional; a bounded degree-4 run certifies 83 of 86 orbits without completing the level. A uniform theorem shows that, at every \(n=2^r-1\), \(r\ge11\), the cubic \((1,5,13,41)\) cannot have a Q certificate of multiplier degree at most 4 even modulo norm and Frobenius. Its nine-factor product occupies nine independent orbit coordinates. This limits the certificate strategy; it does not refute Q-to-C. Infinitude remains unproved.

> **Degree six does not suffice for all cubics (2026-09-07).** Section 107 strengthens the certificate audit from one selected cubic to every cubic orbit at a fixed order. At 13, all 30 cross-free orbits have independently replayed Laurent certificates with multiplier degree at most 6. At 15, an explicit 328-monomial functional annihilates every allowed degree-at-most-6 multiple of Q but takes value 1 on the balanced residual for \(C(1,1,1,1)\). Thus a uniform Q-only bound of 6 is false in this certificate form. This does not refute Q-to-C or category existence. Since this failed target is a diagonal cubic, already implied by Q plus the analytic candidate's proved Frobenius relations, Section 108 begins the certificate search with those additional hypotheses.

> **The specified Lagrangian algebra would force HI (2026-09-07).** Section 106 proves the full conditional reconstruction step for the modular route. If a unitary modular category realizes (105.10) and the object (105.12) has an actual connected commutative separable algebra structure, its module category automatically has the cyclic HI fusion rules and untwisted pointed subcategory. Adjunction fixes its rank at \(2n\); an integral dimension argument forces \(n\) invertibles and \(n\) simples of dimension \(d\), and the central image forces inversion covariance. Thus no separate module fusion-rule hypothesis remains. Constructing the category and algebra uniformly is still unresolved; infinitude is not proved.

> **Recognition and the two monodromy quadratic forms (2026-09-07).** Section 104 proves a conditional odd-order recognition criterion: an actual rank-two Q-system with a free cyclic orbit and inversion covariance forces the full HI fusion rule and principal graph. Section 105 extends the lattice comparison in Section 59 to the quadratic forms: the quotients by \(n\) and by the different of \(\mathbb Z[d]\) give the two proposed twist sectors, with Gauss sums \(+1,-1\). The modular matrices admit an explicit invariant vector of the required dimension. Neither the required bimodule covariance nor a categorical algebra realizing that vector has been constructed uniformly. Infinitude remains unproved.

> **Lower-degree lift equations and a bounded-certificate test (2026-09-07).** Section 103 replaces the degree-15 first-Q lift obstructions by equivalent degree-11 polynomials, using an explicit identity valid even away from Q. The lower-degree formulas have coefficients in the prime field. A separate Laurent-linear-algebra search produces replayable certificates for one chosen cubic at orders through 15; an explicit separating functional proves that multiplier degree 5 is insufficient at order 13. These are finite certificate tests, not a uniform cubic identity. Infinitude remains unproved.

> **Q forces an extra norm digit, and its first lift errors are explicit (2026-09-07).** Section 102 proves that the convolution update's norm defect is twice a paired sum of Q residuals. Every canonical residue Q solution therefore preserves norms modulo 4 automatically. More generally, on the exact convolution lift the minimum norm-defect valuation exceeds the minimum Q-defect valuation by at least one. Explicit degree-at-most-15 polynomials over the residue field now compute all first Q lift errors. The analytic candidate satisfies these additional equations at every odd order. Their uniform implication to C is a new sufficient target, still unproved; infinitude remains unestablished.

> **The norm-only completion target is false (2026-09-07).** Section 101 gives exact two-value phase counterexamples at primes 43,67,131,4099: their convolution lifts preserve norms modulo 8,16,32,1024 respectively, yet their residue cubics fail. For the Legendre ansatz at \(p=8k+3\), a uniform theorem computes the norm-defect valuation as \(1+v_2(k(k-1))\) on the relevant branch, proving that finite-precision norms cannot uniformly imply exact norms at any fixed precision. These examples fail Q. The completion criterion with all residue Q retained remains unresolved and sufficient for infinitude; HI infinitude is not established.

> **A finite etale algebra and an exact ideal target (2026-09-07).** Section 100 proves that the entire quartic convolution algebra is finite etale of rank \(4^n\) over the unramified quadratic 2-adic base, at every odd order. Its splitting turns the modulo-8 completion criterion into an equivalent family of polynomial ideal containments, with a separate version retaining residue Q. Exact ideal calculations establish the stronger containments at 3,5,7. Complete censuses also validate the norm-only test through odd order 21 and at 27; the order-27 census covers 85,197,125 tuples. Section 101 disproves the norm-only criterion at larger finite orders. The uniform containment with residue Q, and infinitude, remain unproved.

> **An explicit two-step lifting target (2026-09-07).** Section 99 proves an exact identity relating the convolution update's norm defect to the zero Fourier mode of Q, an extra-digit estimate for the origin, and a residue quartic detecting the first norm obstruction. Exhaustive tests show that the quartic alone is insufficient at order 15: eight false points preserve norms modulo 4 and fail modulo 8. The modulo-8 test succeeds at the finite orders in Section 100, but Section 101 disproves its all-odd-order completion claim without Q. The analytic construction supplies inputs passing this two-update test and all Q at every odd order; completion with Q retained is still unproved. Separate characteristic-zero ideal calculations prove that norms plus the exact convolution imply all Q at orders 3,5,7; the bounded order-9 calculation did not finish.

> **All phases descend to one row at every odd order (2026-09-07).** Section 98 combines the exact central Frobenius of Section 95 with the cyclic character ambiguity to prove \(K(W_1,\ldots,W_{n-1})=K(A_{g,h}:g,h)=K(B_{1,2},\ldots,B_{1,n-1})\) for the canonical analytic candidate at every odd n. Frobenius acts on an odd-order character value by its fourth power, whereas doubling the label gives its square; centrality forces the value to be 1. This removes the remaining phase-field extension at composite as well as prime orders, without assuming C or a ray-class identification. Infinitude still requires the unproved interior cubic identities.

> **The boundary cubics recover precisely the phase factorization (2026-09-07).** Sections 96--97 distinguish the remaining phase-specific completion problem from a false matrix-level version. At every prime \(p\equiv7\pmod8\), an explicit Legendre-symbol matrix satisfies Q, the inverse products, Frobenius covariance, and every diagonal cubic, but fails other cubics. Under Q and the normalized matrix hypotheses, the cubics with one zero index are equivalent to the cocycle law for a patched core; at cyclic order this is exactly existence of normalized phases. With Frobenius covariance the phases are recovered over the original field by \(W_a=(\delta-1)A_{a/2,a}^{-2}\) for nonzero a. This explains the counterexamples and retains the correct completion hypothesis. The interior cubics, and HI infinitude, remain unproved.

> **Exact Frobenius and a unique convolution lift (2026-09-07).** Section 95 proves that the phase field is unramified above 2 and that arithmetic Frobenius over the quadratic base acts exactly by \(W_a\mapsto W_{2a}\), not merely after reduction. This automorphism is central in the normal closure. A contraction lifts each characteristic-two Frobenius tuple uniquely to the quartic convolution system, gaining at least one binary digit per step. Exact checks modulo \(2^{24}\) preserve all Q and C for the known order-3 and two order-9 certificates; a negative control shows that convergence by itself does not preserve the norm or category equations. Uniform cubic completion, and infinitude, remain unproved.

> **All quadratics and canonical reductions now exist uniformly (2026-09-07).** Sections 93--94 evaluate every nonzero column's finite Fourier transform by a hyperbolic beta integral, retaining and cancelling every extra residue. Reflection then proves all quadratic identities for the double-sine candidate at every odd order. This also identifies the candidate with the unique maximizer of Section 53 and proves its algebraicity. A further convolution identity proves the scalar H condition and shows that every phase is a unit at every prime above 2; reduction therefore gives canonical characteristic-two Q solutions, with \(W_{2a}=W_a^4\), at every odd order. At primes, H also puts every phase in its row field. The cubic identities are still unproved uniformly. In particular these Q solutions alone do not establish HI categories or infinitude.

> **Growth and a stronger correction bound (2026-09-06).** Sections 91--92 prove that the largest generic ghost entry is asymptotic to \(3^{-1/4}n^{-1/2}e^{\kappa n}\), where \(\kappa\approx0.3230659472\). An exact product invariant prevents removing this exponential growth by any fusion-basis gauge. The normalized cup stacks nevertheless have squared norm below 3, giving the stronger sufficient pentagon bound \(q\le1/[3776(2M_0)^{12}]\). Together these results reduce analytic infinitude to an explicit sufficient Q/C error bound of order \(n^{-9}e^{-14\kappa n}\). That error estimate is not proved; infinitude remains open.

> **Certified analytic existence by correction (2026-09-06).** Section 90 proves that every entry of the full transparent pentagon defect is Q, C, \(Q/\sqrt\delta\), or zero, with explicit indices. Fourier coefficients of core rows bound all associators and their inverses; the unit-channel balance is exact before imposing Q or C. These uniform reductions turn the existing interval calculations into a sufficient existence test. With nine extrapolation levels, FLINT/Arb verifies the test at orders 3, 7, and 11, independently replayed with rational arithmetic. These are known finite orders, and the corrected associators need not equal the analytic candidates. Proving the sufficient inequality at unbounded orders, and hence infinitude, remains open.

> **Correction also applies without unitarity (2026-09-06).** Section 89 extends the correction argument to invertible complex associators and signed dimension weights. If the algebraic unit-channel products are balanced, \(M_0\) bounds the matrices and their inverses, and \(S=\sum_a|\delta_a|^2/|\sum_a\delta_a^2|\), then full pentagon error \(q\le1/[870S^2(2M_0)^{14}]\) suffices for convergence. An explicit unit-coefficient margin preserves rigidity. The HI ghost dimensions have \(S=1\), so negative dimensions do not prevent using certified residuals for an existence proof. The required full associator bounds have not yet been supplied for an unbounded family; infinitude remains unproved.

> **Uniform error bounds for the analytic candidate (2026-09-06).** Section 80.7 gives an elementary exponential-series formula and a real-axis extrapolation theorem for every odd order. The logarithmic extrapolation error is bounded independently of n by an explicit quantity decaying as \(2^{-p^2-5p}\). A FLINT/Arb implementation includes this remainder, the series tail, and rounding errors; it encloses every Q and C residual at orders 3, 7, and 11. At order 11 all cubic residuals have magnitude below \(3.15\times10^{-28}\). These bounds certify approximation to the analytic candidate and finite residual bounds. A uniform proof of the required cancellations, and infinitude, remains missing.

> **An exact reduced construction and its extension obstruction (2026-09-06).** Section 88 constructs unitary associators for every cyclic order after omitting the invertible summand from each noninvertible product. At odd orders the reduced pentagons force every monomial associator to have this same permutation support, even without assuming an affine formula. Restoring the HI channels gives explicit balanced unitary trials, but an invertible-output pentagon has operator error at least \(2\cos(\pi/(2n))\), even after arbitrary changes of phases or of the augmented blocks. Thus this entire class of reduced constructions cannot supply the accurate trials required by Section 87. Infinitude remains unproved.

> **Uniform correction without a separate linear certificate (2026-09-06).** Section 87 proves that multiplicity-free unitary trial associators with balanced unit-channel magnitudes and full pentagon operator defect at most \(1/130\) converge to exact associators by explicit partial-trace updates. For HI, also requiring \(q\le1/(4d)\) preserves rigidity and establishes a category of that order. The proof gives \(e_{\mathrm{new}}\le\mu e+57e^2\) and bounds the drift of the scalar imbalance. An unbounded family of balanced trials with \(q_n=o(1/n)\) would therefore prove infinitude. Such a family has not been constructed; infinitude remains unproved.

> **Partial-trace error bound (2026-09-06).** Section 86 proves that the dimension-weighted handle identity has completely bounded error at most \(4q+\mu\) before coherence, where q is the full pentagon operator defect and mu is an explicit scalar imbalance in unit-channel magnitudes. Standard unit-channel magnitudes make mu zero, including for the multiplicity-free HI rules. Exact binary-tree certificates also bound reassociation errors on up to seven tensor factors independently of fusion rank. Section 87 completes the correction estimate; an unbounded family of accurate HI trial associators is still missing.

> **Quantitative pentagon correction (2026-09-06).** Section 85 proves a sufficient test for correcting approximate unitary associators, using operator bounds checked at a single trial point. An exact five-object boundary relation gives a quadratic compatibility bound, and explicit rank-independent constants guarantee convergence when a linear correction certificate and a small full pentagon error are available. The criterion does not assume an existing exact solution. Its hypotheses, including rigidity, have not been certified for an unbounded HI family; infinitude remains unproved.

> **An operator gap for the Alltop approximation (2026-09-06).** Section 84 proves that the cubic Alltop phases, adjusted to the HI amplitude, have quadratic operator error tending to zero but normalized squared cubic-polynomial error tending to 2 along primes \(p\equiv2\pmod3\). An exact torus character sum gives the comparison operator's fifth trace. Every physical HI transfer operator remains asymptotically at least \(\sqrt2/11\) away in operator norm. This rules out that particular vanishing-operator-perturbation strategy; it does not assert HI nonexistence or establish infinitude.

> **Cayley coordinates and order 33 (2026-09-06).** Section 83 gives a uniform projective-line parametrization of all canonical inverse-norm/Frobenius data at \(n=2^r+1\), r odd. The complete order-33 search exhausts 5,384,453,125 such assignments and finds exactly 100 quadratic solutions in five scalar-reindexing orbits. Every orbit passes all quadratics and cubics independently over \(\mathbb F_{2^{20}}\), establishing complex categorification at this additional finite order. The count agrees with the arithmetic prediction \(20h(1093)=100\). Constructing a full additive solution for unbounded r remains open; infinitude is not established.

> **Cayley formula obstruction and an interpolation trap (2026-09-06).** Section 83.6 excludes a single semilinear nonlinear feature at order 33 even when its Frobenius-compatible function is arbitrary, using a relative-trace and affine-line criterion. Section 83.7 proves that a tested union of short two-feature formulas covers every one of the \(2^{32}\) finite normalized Cayley functions, although only 80 satisfy Q. Thus the successful two-feature fits impose no additional HI constraint at that order. Neither result proves infinitude.

> **Canonical finite-sum targets (2026-09-06).** Section 79 proves that every cross-free quadratic or cubic has balanced integer lifts for which all summands agree with their canonical cyclic samples, with no origin corrections. The cubic Gaussian signs cancel exactly. The full existence problem for the analytic candidate therefore reduces to two unweighted finite identities involving the ordinary double sine, with no remaining sign choices or collision equations. Those two identities remain unproved uniformly; infinitude is not established.

> **Rational shift formula (2026-09-06).** Section 78 expresses the n-shift of the quadratic and cubic double-sine kernels using rational functions of degree two and three, respectively. Their divided differences are controlled by nonsingular matrices of sizes two and three whenever the external residues are cross-free. These sizes are independent of n. The resulting weighted identities do not yet give the required unweighted finite sums; infinitude remains unproved.

> **Exact quadratic period primitive (2026-09-06).** Section 80.4 constructs a rational multiple of every cross-free quadratic kernel whose B-shift difference is exactly the kernel. A dual formula works for the reciprocal kernel under the A shift. Section 80.5 proves that the cubic kernel admits no rational B-shift primitive of this form, of any degree. The quadratic primitive shifts by B rather than by one, so its finite integer sum still requires an additional argument. Infinitude remains unproved.

> **One vertical contour for the quadratic sum (2026-09-06).** Section 80.6 uses the quadratic primitive and a difference of cotangents to replace the real-interval term by one absolutely convergent vertical integral and an explicit boundary pair. The desired Q identity is exactly the equality of that integral and the boundary pair. A numerical check away from real multiplication gives a nonzero finite sum and verifies that all terms are retained. The uniform evaluation, and infinitude, remain unproved.

> **One double sine per phase (2026-09-06).** Sections 75--77 prove that the analytic candidate is exactly \(W_a=-(-1)^{a(a+n)/2}d^{-1/2}\operatorname{Sin}_2(1+da/(d+1);d,1)\). This removes the square root of a special-function value. Its meromorphic interpolation has a single exceptional jump on integer translates. The full lens product also factors into two ordinary double sines away from the sampling line, with an explicit origin residue. Four period shifts give a correctly balanced, convergent beta integral containing the desired six sine factors, with explicit sine denominators and the same normalization as the finite cubic target. Converting that integral to the finite sum, including its origin and derivative corrections, remains unresolved. Infinitude is not proved.

> **Complete finite counts and overorders (2026-09-06).** Sections 72--73 give exhaustive characteristic-two phase classifications at every odd order through 31, with new exact workspace certificates at 15, 21, 23, and 31. Every candidate orbit passes all Q and C independently. Magma also completes the full characteristic-two Q-to-C implication at 17. The counts agree with the sum of ray-class degrees over all quadratic orders containing \(\mathbb Z[d]\), including the extra contributions at 11 and 29. This corrects the nonfundamental-discriminant prediction: at \(3^8\) the proposed count is \(b_8=480\), not 384. The uniform count or any sufficient positive lower bound remains unproved.

> **Forced Frobenius gauge (2026-09-06).** Section 71 proves uniformly that Q plus the diagonal cubics forces \(A_{2a,2b}=A_{a,b}^4\), and that every full characteristic-two phase solution has a unique character normalization with \(W_a^4=W_{2a}\). The full phase scheme is finite etale. At \(n=3^k\), every solution has matrix field exactly \(\mathbb F_{2^{4n/3}}\); its canonical coordinate algebra is a product of \(b_k\) copies of this field. Earlier searches now give the complete phase counts \(b_1=1,b_2=2,b_3=3\). Proving \(b_k>0\) for unbounded k, and hence infinitude by this route, remains open.

> **Trace reduction and characteristic-two completion (2026-09-06).** Section 69 proves that at every order \(n=3^k\), only \((n-1)/2\) quadratic orbits need checking and each quadratic is a relative trace with \((n-1)/2\) summands. Exact off-solution checks reach order 81. Section 70 proves full \(Q\Rightarrow C\) over characteristic two at all odd orders through 13 by ideal membership, without imposing Frobenius covariance or selecting saved solutions. The smaller SAT searches have not produced an order-81 certificate. Uniform nonemptiness and infinitude remain unproved.

> **Linear elimination of lower phases (2026-09-06).** Section 68 proves that, at every \(n=3^k\), fixing the top Frobenius seed turns the first quadratic into an affine binary linear system with \(2n/3-2\) unknowns and \(2n/3\) target coordinates. For each of the six saved certificates, this system together with the lower inverse norms recovers exactly the saved lower phases. The first-Q count 24 at order 9 is independently reproduced by linear elimination. At order 81 the same construction has 52 unknowns; sampled top seeds yield affine solutions but no norm-compatible full candidate. This supplies a uniform elimination step, not the missing infinitude proof.

> **Patched rational formulas (2026-09-06).** Section 67 proves that even after omitting both exceptional consecutive ratios, a characteristic-two Frobenius-covariant quadratic solution requires rational ratio degree at least \((n-3)/4\). Thus a fixed number of rational cyclic factors cannot give an infinite family by separately patching the origin. Exact interpolation gives minimum degrees 4 at order 9 and 12 at order 27. Section 66.3 also excludes every stationary cubic rational recursion on a single known branch. These are restrictions on proposed constructions; infinitude remains unproved.

> **Two-quadratic reduction and false inflations (2026-09-06).** Section 66 proves, by exhaustive finite-field searches, that the first two phase quadratics plus the full first-phase field degree imply every cubic at orders 3, 9 and 27. At 27 the two quadratics have 72 solutions: 54 of full degree, all valid, and 18 of smaller degree. A uniform inflation identity explains 12 of the false solutions and produces false two-quadratic candidates at infinitely many larger orders. The counts \(2,12,72\) do not arise from a single degree-six rational recursion over \(\mathbb F_4\): all 20 possible maps are rejected exactly. Uniform completion and nonemptiness remain unproved.

> **Forced field degree and cubic norm lifts (2026-09-06).** Section 65 proves that at every \(n=3^k\), a Frobenius-covariant quadratic solution has \(W_1\), and already \(R_2\), of degree exactly \(2n/3\) over \(\mathbb F_4\). One designated quadratic excludes every smaller field. A second uniform theorem gives an explicit cubic lift of any prescribed normalized relative norm and counts its irreducible trace choices. Thus the proposed coupled norm towers can always be constructed with the required field growth; making their additive equations vanish is still unresolved.

> **Uniform small-field obstruction (2026-09-06).** Section 64 proves that no nontrivial odd abelian group has a Frobenius-covariant phase solution of all quadratics over \(\mathbb F_4\). The proof turns a quadratic trace identity into an impossible additive closure. It also excludes, over every characteristic-two extension, constructions whose phases are constant on the nonzero cosets of a proper nontrivial subgroup. The next-smallest-field search at order 43 exhausts 125 assignments over \(\mathbb F_{16}\) and finds none. These statements close two construction routes; they do not establish infinitude.

> **Conjugate-norm obstruction (2026-09-06).** Section 64.4 treats a characteristic-two involution interchanging delta and delta squared. Full quadratic solutions cannot have every nonzero phase of relative norm one under that involution, or every phase in the corresponding fixed-field line. An explicit identity for the diagonal residual proves this uniformly. It also rejects a quadratic-character/Möbius construction at every prime congruent to 7 modulo 8, despite its automatic inverse norms and Frobenius covariance. This restricts the construction; it does not assert HI nonexistence or prove infinitude.

> **Twisted norm branches (2026-09-06).** Section 63 proves that at \(n=3^k\) the conjugate prime above 3 has class order exactly \(k\) in the quadratic order of discriminant \(n^2+4\), and its \(k\)-th ray-class power is Frobenius at \((2)\). The saved order-9 and order-27 phases satisfy the corresponding norm laws across different branches, including the required Frobenius twist. This corrects the failed same-branch norm prescription. At order 81 the arithmetic gives two cycles of four branches; existence of HI solutions on those cycles is not proved.

> **Full quadratic completion at 13 (2026-09-06).** Section 62 proves \((Q)\Rightarrow(C)\) for every order-13 phase solution, using a modular upper bound of 12 on the full row quotient and a matching exact cubic orbit. No scalar H condition is imposed. The row algebra is one degree-12 field over \(\mathbb Q(\delta)\); the phase algebra has dimension 156. This extends the finite implication theorem, without proving it in unbounded order.

> **Elliptic parametrization (2026-09-06).** Section 61 realizes every norm-normalized, Frobenius-covariant phase sequence at \(n=3^k\) using a rational function on the single curve \(y^2+y=x^3+\omega\) over \(\mathbb F_4\). The curve's Frobenius is exactly doubling. A concrete rational-function recurrence supplies complete certificates at 3, 9 and 27, but exhaustive testing of its three order-81 candidates rejects all of them at the first quadratic. The parametrization is uniform; the recurrence is not a construction of an infinite HI family.

> **Characteristic-2 pentagon criterion (2026-09-06).** Section 60 proves that, for any full-Q phase candidate, an explicit rank-three correction \(\mathcal P=R(I+D)\) satisfies \(\mathcal P^5=I\) exactly when every cubic equation holds. This uses polynomial identities, without positivity. At a full characteristic-2 solution the uncorrected transfer operator has order exactly 30, with a prescribed rank-two square-zero part in its fifth-power defect. Exact checks cover both order-9 branches, and a spectral obstruction excludes one branch from any adjoint-matrix construction. The corrected pentagon still needs a construction for unbounded orders.

> **Finite-field construction (2026-09-06).** Section 58 proves that a complete normalized cubic certificate in characteristic \(\ell\nmid n(n^2+4)\) implies complex categorification by algebraic reconstruction and categorical lifting. Characteristic 2 works at every odd order. In that characteristic, inverse norms and Frobenius covariance imply the scalar H equation uniformly. A search with no HI or Stark seeds finds complete certificates at 3, 9 and 27; all three order-27 Frobenius orbits pass every cubic. The six independent JSON certificates are saved. Nonemptiness at unbounded orders, and hence infinitude, remains unproved.

> **Scalar completion (2026-09-06).** Section 55 introduces one scalar equation involving the phase sum and \(\operatorname{Tr}\mathcal R\). Exact finite-algebra certificates in Sections 55 and 57 show that it completes one quadratic column to the full system at orders 3, 5, 7, 11, and 13. At every odd prime, a real phase lift satisfying the scalar equation already lies in its row field; this implication is proved uniformly. The canonical phase sum has a numerical period-40 formula, and 508 sign-chamber tests show no disagreement between scalar acceptance and full-Q acceptance. Neither scalar completion in unbounded order nor the canonical scalar identity is proved.

> **Uniform one-column classification (2026-09-06).** Section 54 proves that the entire one-column algebra is finite and reduced at every odd order, with all its points real above the negative dimension embedding. At each odd prime \(p\), its exact length modulo character gauge is \(\binom{p-1}{(p-1)/2}\); composite counts include 58 at order 9 and 2492 at order 15. Consequently the full quadratic and cubic schemes in the phase ansatz are also finite and reduced, but their nonemptiness is still unproved uniformly. This strengthens the algebraic setting for the convex construction without asserting infinitude.

> **Convex construction (2026-09-06).** Section 53 proves that a strictly concave logarithmic optimization problem has a unique interior maximizer for every odd \(n\), and that this maximizer gives real algebraic phase data satisfying one complete quadratic column. The prescribed chamber recovers the signs of Section 51. This construction numerically reproduces the double-sine candidates and passes all quadratics at orders 51 and 101 as well; only sampled cubics were checked at those two larger orders. An exact counterexample shows why one column by itself is insufficient. The remaining conjecture is that the uniquely selected maximizer satisfies the full cubic system. **Infinitude remains unproved.**

> **Analytic continuation (2026-09-06).** Sections 51–52 give an explicit product of \(n\) double sines and a fixed quadratic sign formula, with no fitted roots or signs. Its real, negative-dimension matrices pass numerical Izumi checks through order 31. The continued-fraction formula, cancellation of its modular phases, and inverse-pair relation are proved uniformly. A separate exact residual identity shows that the cubic equations imply the quadratic and quartic reconstruction equations in the normalized \(\omega=1\) setting. Consequently a proof of the proposed analytic cubic identity would already produce nonunitary fusion categories; algebraicity would then follow from rigidity, without assuming Stark algebraicity first. **Neither this analytic identity nor infinitude is proved.** Unitary existence additionally requires the appropriate positive-embedding condition.

> **Further continuation (2026-09-06).** Sections 41–50 give a weighted-design formulation, uniform isolation of the flat Alltop solutions, exact HI amplitude components at orders 5 and 7, and a uniform quotient of the phase equations by the cyclic character gauge. An exact physical counterexample shows that diagonal quadratics plus Galois covariance are insufficient; its arithmetic field fails both the one-root and prescribed conductor conditions. The quadratic-to-cubic ideal theorem now also holds at \(n=11\), certified by an independent homogeneous Hilbert comparison. A further uniform degree bound excludes bounded-order nonsingular cyclic hypergeometric phase formulas. New norm theorems give ray-field norm elements at every odd order and explicit integral norm units whenever \(n\equiv3\pmod4\), including infinitely many primes. An exact half-lattice reduction produces a second construction route, with complete finite Izumi checks at 3, 5, 7, 11, 13, 17, 29, and 199. A uniform operator theorem identifies the full cubic residual norm with a fifth-order defect of a unitary operator. Infinitude remains unproved: physical quadratic solutions and the cubic implication still need a construction or proof for unbounded orders.

> **Further continuation (2026-09-05).** Sections 34–40 prove that the full phase-ansatz Izumi system is equivalent to one balanced finite beta identity, including its collision corrections. They extend sign descent to composite orders and show that its stabilizer obstruction always vanishes at odd prime powers under the stated root/phase hypotheses. Complete exact constructions now also pass at \(n=19,25,199\); the latter belongs to the fixed-\(\mathbb Q(\sqrt5)\) Lucas family. The order-19 polynomial recognition is discharged as well. Saved coefficient data and independent verifiers accompany all three cases. The prime-power construction now uses one Kummer root, twisted norm descent, and a rational linear system for the signs. The quadratic-to-cubic ideal containment is verified at orders 3, 5, 7, and 9. Infinitude remains unproved; Sections 37–40 specify what a uniform proof still requires.

> **Existence continuation (2026-09-04).** Sections 28–33 go beyond field comparisons. A cocycle argument determines every generic fourth power from the labeled doubling orbit. The new `hi_stark_seedless.gp` constructs complete matrices directly from PARI Stark polynomials, with no numerical HI seeds, and verifies every Izumi equation exactly for \(n=7,11,13,17,29\). It also identifies the previously recognized \(n=13\) polynomial and all three \(n=17\) polynomials with the certified matrices. Their numerical-recognition qualifications in the earlier historical sections are therefore removed by this continuation. Infinitude is **not** proved: Section 32 supplies an unconditional infinite family of arithmetic inputs over the fixed field \(\mathbb Q(\sqrt5)\), and Section 33 specifies the uniform identities still needed.

> **Update (2026-09-04).** The PARI tests have now been completed for \(p=7,11,13,17,19\). For \(p=7\), and conditional on the initial numerical recognition for \(p=13,17\), the normalized HI square generates the same ray field as PARI's distinguished Stark unit and is the exact group-ring transform \(s^{2-\operatorname{Frob}_{(2)}}\), rather than the same distinguished generator. At \(p=19\), the ray group is \(C_{18}\times C_2\), and the two published HI branches are the two Hilbert-class conjugate halves of its full degree-36 orbit. See Sections 21–27 and the reproducible GP scripts listed at the end.

---

# 1. Fusion rules and notation

Let
\[
G=\mathbb Z_N,\qquad N\text{ odd},
\]
with invertible simple objects \(\alpha^a\), \(a\in\mathbb Z_N\), and noninvertibles
\[
\rho_a:=\alpha^a\rho.
\]

The fusion rules are
\[
\alpha^a\alpha^b=\alpha^{a+b},
\]
\[
\alpha^a\rho_b=\rho_{a+b},
\qquad
\rho_a\alpha^b=\rho_{a-b},
\]
and
\[
\rho_a\rho_b=\alpha^{a-b}+\sum_{c\in\mathbb Z_N}\rho_c.
\]

The Frobenius–Perron dimension of \(\rho\) is
\[
d=\frac{N+\sqrt{N^2+4}}2,
\qquad
d^2=Nd+1.
\]

For the prime-order discussion below I write \(N=p\).

---

# 2. Transparent gauge: all noninvertible \(F\)-symbols from one matrix

The transparent-gauge structure strongly suggests that all \(F\)-symbols are determined by:

- universal values \(1,d^{-1/2},d^{-1}\) when invertible channels occur;
- one \(N\times N\) core matrix
  \[
  A_{a,b}
  :=
  \left(F^{\rho,\rho,\rho}_{\rho_a}\right)_{\rho,\rho_b}.
  \]

A useful reconstruction formula obtained from the transparent translation identities is

\[
\boxed{
\left(
F^{\rho_{a_1},\rho_{a_2},\rho_{a_3}}_{\rho_{a_4}}
\right)_{\rho_{a_5},\rho_{a_6}}
=
A_{\,
a_4+a_2-a_1-a_3,\,
a_5+a_6-a_1-a_3
}
}
\]
with all indices modulo \(N\).

In particular,
\[
\boxed{
\left(F^{\rho,\rho,\rho}_{\rho_a}\right)_{\rho_e,\rho_f}
=
A_{a,e+f}.
}
\]

Thus for fixed \(a\), the noninvertible block of
\[
F^{\rho,\rho,\rho}_{\rho_a}
\]
is anti-circulant.

This is the main structural reason the enormous pentagon system should reduce to a much smaller algebraic problem.

---

# 3. Identification with the Izumi / Evans–Gannon \(A\)-matrix

For known examples, the transparent \(F\)-core appears to coincide with the Izumi/Evans–Gannon structure matrix \(A_{g,h}\).

The standard symmetries include
\[
A_{g,h}
=
A_{-h,g-h}
=
A_{h-g,-g}.
\]

For a unitary solution,
\[
A_{h,g}=\overline{A_{g,h}}.
\]

The maps
\[
R(g,h)=(h-g,-g),
\qquad
S(g,h)=(h,g)
\]
generate
\[
S_3\simeq W(A_2).
\]

For real solutions, \(A\) is constant on the \(S_3\)-orbits in \(\mathbb Z_N^2\). For complex unitary solutions, reflections can act by complex conjugation.

For \(3\nmid N\), the number of \(S_3\)-orbits in \(\mathbb Z_N^2\) is
\[
\frac{(N+1)(N+2)}6.
\]

---

# 4. Q-system phase parametrization

For the unitary Q-system branch, the generic entries can be written in terms of phases \(j_g\).

Set
\[
z_g=e^{ij_g}.
\]

For generic \(g,h\),
\[
A_{g,h}
=
\frac{\sqrt d}{d-1}
e^{i(j_h-j_g-j_{h-g})}
=
\frac{\sqrt d}{d-1}
\frac{z_h}{z_gz_{h-g}}.
\]

The exceptional values are
\[
A_{0,0}=1-\frac1{d-1},
\]
and
\[
A_{g,0}=A_{0,g}=A_{g,g}
=
-\frac1{d-1}
\qquad (g\neq0).
\]

This phase form should be viewed as a discrete multiplicative second derivative of the one-dimensional sequence \(z_g\).

A major possible route to a uniform construction is to Fourier-transform the Izumi equations in the \(z_g\) variables.

---

# 5. The explicit \(\mathbb Z_{17}\) setup

For \(p=17\),
\[
d=\delta
=
\frac{17+\sqrt{293}}2.
\]

Define
\[
B_{g,h}:=(\delta-1)A_{g,h}.
\]

Then
\[
B_{0,0}=\delta-2,
\]
\[
B_{g,0}=B_{0,g}=B_{g,g}=-1
\qquad(g\neq0),
\]
and for generic entries
\[
|B_{g,h}|=\sqrt{\delta}.
\]

The ratios \(t=h/g\in\mathbb F_{17}\setminus\{0,1\}\) split into three \(S_3\)-orbits:
\[
\mathcal O_2=\{2,9,16\},
\]
\[
\mathcal O_3=\{3,6,8,10,12,15\},
\]
\[
\mathcal O_4=\{4,5,7,11,13,14\}.
\]

Therefore the \(289\) core positions split into only five algebraic types:

- \(A_{0,0}\);
- the common axis/diagonal value;
- generic type \(\mathcal O_2\);
- generic type \(\mathcal O_3\);
- generic type \(\mathcal O_4\).

---

# 6. Exact algebraic reconstruction for \(\mathbb Z_{17}\)

Starting from the published numerical Evans–Gannon phase seed and refining it to high precision, one obtains degree-\(16\) orbit polynomials over
\[
K_{17}=\mathbb Q(\delta)
=
\mathbb Q(\sqrt{293})
\]
for the scaled generic entries \(B\).

For the three ratio classes there are irreducible degree-\(16\) polynomials
\[
P_2,\quad P_3,\quad P_4
\in K_{17}[X].
\]

The corresponding actual \(A\)-entries have minimal polynomials over \(K_{17}\)
\[
Q_t(X)
=
\frac{P_t((\delta-1)X)}{(\delta-1)^{16}}.
\]

After eliminating \(\delta\), the generic \(A\)-entries have irreducible degree-\(32\) polynomials over \(\mathbb Q\).

The special values satisfy:
\[
A_{g,0}=A_{0,g}=A_{g,g}
\quad\Longrightarrow\quad
17X^2-15X-1=0,
\]
and
\[
A_{0,0}
\quad\Longrightarrow\quad
17X^2-49X+31=0.
\]

The exact Sage data from the previous reconstruction is in:

`z17_haagerup_izumi_minpolys.sage`

This includes:

- the three \(P_t\) over \(K_{17}\);
- the three degree-\(32\) rational polynomials;
- irreducibility checks;
- the special transparent values.

---

# 7. Class-field hypothesis

For prime \(p\), define
\[
K_p
=
\mathbb Q(\delta),
\qquad
\delta=\frac{p+\sqrt{p^2+4}}2.
\]

Since
\[
N_{K_p/\mathbb Q}(\delta)=-1,
\]
one has
\[
N(\delta-1)=-p,
\qquad
N(\delta+1)=p.
\]

Define the degree-one prime
\[
\mathfrak p_+=(\delta-1)
\]
above \(p\).

The natural narrow ray modulus suggested by the physical embedding is
\[
\boxed{
\mathfrak m_p=\mathfrak p_+\infty_+,
}
\]
where \(\infty_+\) is the real place with
\[
\delta>0.
\]

If:

1. \(h(K_p)=1\);
2. \(\delta\) is a fundamental unit;

then the ray class group should have order
\[
p-1
\]
and in favorable cases
\[
\operatorname{Cl}_{\mathfrak m_p}(K_p)
\simeq
\mathbb F_p^\times
\simeq
C_{p-1}.
\]

This matches the observed generic entry-field degrees for \(p=7,13,17\).

---

# 8. Computational class-field evidence

## \(p=7,13,17\)

For the principal branch, the reconstructed generic entry field has degree

\[
p-1
\]
over \(K_p\).

A polynomial transformation implementing
\[
u\mapsto gu
\]
for a primitive root \(g\bmod p\) was reconstructed and checked algebraically to permute the roots.

This indicates
\[
\operatorname{Gal}(L_p/K_p)
\simeq
C_{p-1}
\simeq
\mathbb F_p^\times.
\]

A Frobenius / Artin comparison was then performed at many split primes, using the expected ray character arising from
\[
\mathfrak m_p=(\delta-1)\infty_+.
\]

The observed Frobenius permutations matched the predicted ray-class action in all tested cases for \(p=7,13,17\).

The polynomial discriminants also fit the ray-class prediction after dividing by perfect-square index factors.

Expected relative field discriminant:
\[
\boxed{
\mathfrak D_{L_p/K_p}
=
\mathfrak p_+^{p-2}.
}
\]

This is consistent with a conductor-\(\mathfrak p_+\) abelian extension.

### Status

The ray groups, conductors, discriminants, and field identifications have now been reproduced with exact PARI class-field routines for \(p=7,13,17\). The \(p=7\) HI input is exact; the \(p=13,17\) conclusions remain conditional only on their numerical-to-exact HI polynomial reconstructions. Independent Magma replication would still be useful.

---

# 9. The \(p=11\) exception

Here
\[
K_{11}
=
\mathbb Q(\sqrt5).
\]

Let
\[
\epsilon=\frac{1+\sqrt5}{2}.
\]

Then
\[
\delta
=
\frac{11+5\sqrt5}{2}
=
\epsilon^5.
\]

Thus \(\delta\) is **not** the fundamental unit.

This changes the ray-class calculation.

The simple modulus
\[
(\delta-1)\infty_+
\]
has ray class group of order \(2\), not \(10\).

Evans–Gannon have two \(\mathbb Z_{11}\) Q-system branches.

For the second branch, the apparent degree-\(10\) orbit collapses to five copies of one quadratic polynomial over \(K_{11}\):
\[
Q(X)
=
X^2
+
\frac{5+3\sqrt5}{2}X
+
\frac{11+5\sqrt5}{2}.
\]

Its discriminant is
\[
\operatorname{disc}Q
=
-(\delta-1).
\]

This looks exactly like the quadratic ray field of conductor
\[
(\delta-1)\infty_+.
\]

The principal degree-\(10\) \(p=11\) branch is arithmetically different. The continuation in Section 22.2 identifies the conductor of its reconstructed unit field as
\[
(\delta-1)\mathfrak q_5^2\infty_+
=5(\delta-1)\infty_+,
\]
where \(\mathfrak q_5\) is the ramified prime above \(5\).

### Important lesson

The correct global statement is probably **not**
“every generic HI entry field is always the simple \((\delta-1)\infty_+\) ray class field.”

Instead, HI branches seem naturally organized by ray class arithmetic, with unit-index and class-group effects causing exceptional splitting and alternate conductors.

---

# 10. The \(p=19\) class-group phenomenon

For
\[
K_{19}
=
\mathbb Q(\sqrt{365}),
\]
the class group is exactly \(C_2\), and \(19-\delta=-\delta^{-1}\) is a fundamental unit.

The simple ray modulus
\[
(\delta-1)\infty_+
\]
has ray class group
\[
\operatorname{Cl}_{(\delta-1)\infty_+}(K_{19})
\simeq C_{18}\times C_2,
\]
of order \(2(19-1)=36\).

Evans–Gannon give two \(\mathbb Z_{19}\) Q-system branches.

For either branch separately, the 18-element set
\[
\{B_{u,2u}:u\in\mathbb F_{19}^\times\}
\]
does not form a degree-\(18\) polynomial over \(K_{19}\).

However, combining the 18 values from **both branches** gives an irreducible degree-\(36\) polynomial over \(K_{19}\).

Numerical reconstruction followed by exact conductor and Hilbert-class calculations proves, conditional only on recognition of the phase polynomial, that

\[
\boxed{
\text{the two \(p=19\) HI branches are two halves of one ray-class Galois orbit,}
}
\]
with the nontrivial ideal class exchanging the branches. Section 26 gives the exact field data and isolates the remaining numerical recognition step; an independent Magma replication would still be useful.

---

# 11. Stark-unit candidate

This is the most promising new observation.

For \(p=17\), define
\[
U_{g,h}
=
\frac{B_{g,h}}{\sqrt{\delta}}.
\]

For generic entries,
\[
|U_{g,h}|=1
\]
under the physical embedding.

On the \(t=2\) orbit, define
\[
\boxed{
\varepsilon_u
=
-U_{u,2u}^{\,2}
=
-\frac{B_{u,2u}^2}{\delta}.
}
\]

Observed properties of \(\varepsilon_u\):

1. \(\varepsilon_u\) is an algebraic unit.
2. It has degree \(16\) over \(K_{17}\).
3. It generates the same field as \(B_{u,2u}\).
4. Its minimal polynomial over \(K_{17}\) is reciprocal.
5. One has
   \[
   \varepsilon_{-u}=\varepsilon_u^{-1}.
   \]
6. The Galois action is
   \[
   \sigma_a(\varepsilon_u)=\varepsilon_{au}.
   \]
7. Under the conjugate real embedding of \(K_{17}\), all 16 Galois conjugates of \(\varepsilon_1\) are positive real numbers.

These are exactly the qualitative features expected from a rank-one Stark / Shintani unit orbit for the ray extension
\[
K_{17}^{(\delta-1)\infty_+}/K_{17}.
\]

The initial working conjecture was:

\[
\boxed{
-\frac{B_{u,2u}^2}{\delta}
\quad\text{is a Stark unit, or a fixed integral power of a canonical Stark unit.}
}
\]

Equivalently,
\[
\boxed{
U_{u,2u}
=
\pm i\sqrt{\varepsilon_u}.
}
\]

The appearance of the square root is notable because recent SIC-POVM constructions from real quadratic ray class fields also express unit-modulus overlap phases in terms of square roots / powers of Stark units.

The exact comparison in Section 21 refines this statement. The HI unit is not itself a root of PARI's Stark polynomial, nor a pure power orbit of such a root. It does, however, lie in the same ray field and satisfies, after compatible choices of roots and a cyclic Galois generator \(\sigma\),

\[
\boxed{
\varepsilon_{\mathrm{HI}}^2
=
\frac{s^2}{\sigma^2(s)},
}
\]

where \(s\) is a root of PARI's `bnrstarkunit` polynomial. Thus the robust conjecture is the broader one: normalized HI phases are roots of short products or quotients of Stark conjugates.

---

# 12. PARI/GP Stark-unit test

This test was completed with PARI/GP 2.17.4; full results are in Section 21.

For \(p=17\), construct

\[
K=\mathbb Q(\delta),
\qquad
\delta^2-17\delta-1=0.
\]

Then construct the ray class field for
\[
\mathfrak m=(\delta-1)\infty_+.
\]

Schematic GP:

```gp
bnf = bnfinit(y^2 - 17*y - 1, 1);

\\ inspect real embeddings first
polrootsreal(y^2 - 17*y - 1)

\\ prime ideal generated by delta - 1
pp = idealhnf(bnf, y - 1);

\\ PARI orders the roots increasingly, so [0,1] selects delta > 0
bnr = bnrinit(bnf, [pp, [0,1]], 1);

bnr.clgp
S = bnrstarkunit(bnr);
lift(S)
```

Important implementation details:

- `[0,1]` is the infinite-place bit for the positive embedding \(\delta>0\); `[1,0]` gives a ray group of order \(8\), not \(16\);
- construct \(\mathfrak p_+\) from `delta-1`, rather than relying on the ordering returned by `idealprimedec`;
- inspect the ray class group;
- compare the returned Stark polynomial with the exact minimal polynomial of
  \[
  \varepsilon_1=-B_{1,2}^2/\delta.
  \]

Possible outcomes:

### A. Exact polynomial match

Then the normalized HI phase is literally a square root of the canonical Stark unit, up to inversion and a root of unity.

### B. Same field, polynomial related by a power map

Then
\[
\varepsilon_{\mathrm{HI}}
=
\varepsilon_{\mathrm{Stark}}^k
\]
for some integer \(k\), which is still excellent.

### C. Same field but unrelated unit-lattice class

Then class-field theory remains relevant, but the strong Stark-unit hypothesis is false.

### Actual outcome: same field and a short Stark-orbit quotient

The two polynomials are unequal and there is no pure-power orbit relation, but the fields are \(K_{17}\)-isomorphic and an exact two-conjugate relation exists:

\[
\varepsilon_{\mathrm{HI}}^2
=
\frac{s^2}{\sigma^2(s)}.
\]

This is stronger than outcome C and points toward a multiplicative-difference or cocycle formula.

---

# 13. Independent Magma replication

The analogous PARI calculations are now complete for \(p=7,11,13,17,19\). The following remains a useful independent verification plan.

For each \(p=7,13,17,19\):

1. Construct
   \[
   K_p=\mathbb Q(\sqrt{p^2+4}).
   \]

2. Compute:
   - ring of integers;
   - unit group;
   - class group;
   - factorization of \(p\);
   - prime ideal \(\mathfrak p_+=(\delta-1)\).

3. Construct the ray class group for
   \[
   \mathfrak p_+\infty_+.
   \]

4. Construct the corresponding class field.

5. Compare:
   - degree;
   - discriminant;
   - ramification;
   - Galois group;
   - Artin action at small primes.

6. For \(p=17\), reproduce the exact identification of the reconstructed \(B_{1,2}\) field with the class field.

7. Reproduce the test that
   \[
   \varepsilon=-B_{1,2}^2/\delta
   \]
   is not a pure power of one Stark conjugate but satisfies the exact Frobenius quotient relation.

For \(p=19\), independently reproduce the \(C_{18}\times C_2\) ray group, the Hilbert class field \(\mathbb Q(\sqrt5,\sqrt{73})\), and the exact Hilbert-conjugate factorization of the recognized HI polynomial.

For \(p=11\), independently verify the PARI result that the principal degree-\(10\) branch has conductor \(5(\delta-1)\infty_+\).

---

# 14. Higher-priority structural problem: derive all generic entries from one Stark orbit

The exact relation for
\[
\varepsilon_u=-B_{u,2u}^2/\delta
\]
as a Frobenius quotient of Stark conjugates gives only the ratio class \(t=2\).

For \(p=17\), we still have the other two generic orbit types:
\[
t\in\mathcal O_3,
\qquad
t\in\mathcal O_4.
\]

The next task is to ask whether these can be expressed using products or quotients of Stark conjugates.

Try relations of the form
\[
U_{g,h}^{\,2}
\stackrel{?}{=}
-\varepsilon_{a}^{m}
\varepsilon_{b}^{n}
\varepsilon_{c}^{r},
\]
where \(a,b,c\) are simple linear or cross-ratio functions of \(g,h\).

More natural tests:

\[
\frac{U_{1,t}^2}{U_{1,2}^2},
\]
\[
\frac{U_{1,t}U_{1,1-t}}{U_{1,2}},
\]
\[
U_{g,h}U_{h,g},
\]
\[
U_{g,h}U_{-h,g-h}U_{h-g,-g}.
\]

Search for multiplicative relations in the unit group of the ray field using:

- Magma `UnitGroup`;
- PARI `bnfisunit`;
- integer relations among logarithmic embeddings.

If all generic \(U_{g,h}\) can be expressed as products of square roots of one Stark-unit Galois orbit, then the entire transparent associator may admit a direct class-field construction.

---

# 15. Fourier / cocycle route

The phase parametrization
\[
U_{g,h}
=
\frac{z_h}{z_gz_{h-g}}
\]
suggests that \(U\) is a multiplicative second difference.

A major goal is to find \(z_g\) directly in class-field terms.

Possible ansatz:
\[
z_g
=
\frac{Q_p(\zeta_p^g)}
     {Q_p(\zeta_p^{-g})},
\]
or a variant built from:

- Gauss sums;
- Jacobi sums;
- Gaussian periods;
- Stark/Shintani units;
- Shintani–Faddeev cocycle values at real multiplication points.

If \(z_g\) can be produced directly, all \(U_{g,h}\) follow automatically.

Then the Izumi equations should be Fourier transformed. Since they contain cyclic convolution sums, Fourier space may turn them into lower-dimensional multiplicative identities.

---

# 16. Potential Shintani–Faddeev route

The real quadratic number
\[
\delta=\frac{p+\sqrt{p^2+4}}2
\]
is the fixed point of
\[
x\mapsto p+\frac1x,
\]
represented by
\[
\begin{pmatrix}
p&1\\
1&0
\end{pmatrix}.
\]

This makes \(\delta\) a natural real-multiplication point.

The modulus
\[
(\delta-1)
\]
has norm \(p\), suggesting rational characteristics of denominator \(p\).

A first plausible formula was schematically
\[
U_{u,2u}
=
\zeta\,
{}^{\mathbf r_u}[\delta],
\]
where
\[
\mathbf r_u\in \frac1p\mathbb Z^2/\mathbb Z^2
\]
indexes the ray class and the right-hand side is a Shintani–Faddeev / real-multiplication cocycle value.

The exact comparisons show that a single Stark value is too restrictive. The revised target is a quotient of a value and its Frobenius-at-\((2)\) translate, whose square matches
\[
U_{u,2u}^4
=
\frac{s_u^2}{s_{2u}}
\]
up to the fixed signs and normalizations described in Sections 21–27.

This could eventually provide an explicit nonnumerical construction.

---

# 17. Long-term existence strategy

The numerical-to-algebraic reconstruction should be treated as a discovery tool only.

A viable infinite-family proof would ideally look like one of the following.

## Strategy A: direct ray-class / Stark formula

Construct canonical Stark representatives \(s_u\) in
\[
K_p^{(\delta-1)\infty_+}
\]
and define the HI units by the Frobenius quotient
\[
e_u^2=s_u^2/s_{2u},
\]
then define \(F\)-symbols algebraically from suitable roots and products of these units.

Then prove the Izumi equations by class-field or cocycle identities.

## Strategy B: analytic Shintani–Faddeev formula

Define the \(F\)-symbols from explicit special-function values at the RM point \(\delta\).

Prove the Izumi identities analytically.

Since an isolated solution of polynomial equations over a number field has algebraic coordinates, algebraicity could then follow from rigidity rather than from direct Stark algebraicity.

## Strategy C: finite field + Hensel lifting

Define the Izumi solution modulo suitable primes using character sums.

Prove the mod-\(\mathfrak q\) solution is smooth.

Prove a lifting criterion for the full system over the local integer
ring, then Hensel-lift. Smoothness of the special fiber alone does not
exclude a vertical component: relative smoothness, or an equivalent
flatness and Jacobian argument, is needed. A zero-dimensional lift has
algebraic coordinates; a positive-dimensional \(p\)-adic point need not.

For unitary existence, also prove that a complex embedding realizes the
formal involution as complex conjugation and satisfies positivity. A
formal norm relation over a \(p\)-adic field does not supply this real
condition. With these additional steps, the approach could prove
existence without explicitly computing complex minimal polynomials.

---

# 18. Concrete next-step checklist

## First priority: verify the Stark comparison at \(p=17\)

- [x] Reconstruct / load exact \(P_2(B)\).
- [x] Compute exact minimal polynomial of
  \[
  \varepsilon=-B^2/\delta.
  \]
- [x] Run `bnrstarkunit` for
  \[
  K_{17},\quad(\delta-1)\infty_+.
  \]
- [x] Compare polynomials exactly: unequal, but the relative fields are exactly \(K_{17}\)-isomorphic.
- [x] Test power relations
  \[
  \varepsilon_{\mathrm{HI}}=\sigma(\varepsilon_{\mathrm{Stark}})^k.
  \]
  No pure-power relation occurs; an exact short orbit relation does.
- [x] Identify the quotient automorphism as arithmetic \(\operatorname{Frob}_{(2)}\) by exact reduction modulo \(2\).

## Second priority: repeat at \(p=7,13\)

- [x] Complete the \(p=7\) comparison from Evans–Gannon's exact algebraic solution.
- [x] Complete the \(p=13\) comparison from its reconstructed numerical branch.
- [x] Formulate the sharpened Stark-orbit quotient conjecture suggested by all three cases.
- [x] Verify the Frobenius-at-\((2)\) identification in both cases.

## Third priority: \(p=19\)

- [x] Identify the degree-\(36\) ray class field and its group \(C_{18}\times C_2\) exactly.
- [x] Verify, after numerical polynomial recognition, that the combined HI orbit defines this full ray field.
- [x] Identify the Hilbert class field and prove that its involution interchanges the exact branch factors.
- [x] Compare with the full Stark orbit: the fields agree exactly, and a separated numerical search finds a branchwise generator-of-\(\langle\operatorname{Frob}_{(2)}\rangle\) quotient law.

## Fourth priority: \(p=11\)

- [x] Confirm the second branch equals the quadratic simple ray field, including its affine normalization to PARI's Stark unit.
- [x] Determine the apparent conductor of the reconstructed principal degree-\(10\) branch.
- [x] Check whether the prime above \(5\) enters the conductor: it enters as \(\mathfrak q_5^2=(5)\).
- [ ] Compare its modular-data distinction with conductor arithmetic.

## Fifth priority: recover all \(A_{g,h}\) from Stark units

- [x] Obtain a uniform fourth-power expression for every generic entry (Section 28), bypassing separate unit-group searches.
- [x] Lift it to complete exact matrices for \(n=7,11,13,17,29\), including all three \(\mathbb Z_{17}\) ratio types (Section 29).
- [x] Determine coherent signs by linear equations over \(\mathbb F_2\), leaving only a global generic sign (Section 30).

## Sixth priority: general symbolic formula

- [x] Give a single phase-sequence formula including exceptional entries (Section 31).
- [x] Fourier transform the entire quadratic system for arbitrary odd \(n\) (Section 31).
- [ ] Prove the Fourier identities and the cubic system for a uniform analytic construction.
- [ ] Search for a class-field / character-sum ansatz.

---

# 19. Main conjectural picture

The current working conjecture is:

\[
\boxed{
\text{Cyclic Haagerup–Izumi Q-system \(F\)-symbols are class-field-theoretic objects over }
K_p=\mathbb Q(\sqrt{p^2+4}).
}
\]

More specifically:

1. the relevant algebraic fields are narrow ray class fields, or closely related sub/extensions, with modulus involving
   \[
   (\delta-1)\infty_+;
   \]

2. the normalized unit-circle generic \(F\)-symbols are roots of short products or quotients of Stark conjugates; for the exact \(p=7\) solution and the reconstructed \(p=13,17\) candidates, the same exact quotient form holds, and reduction at the inert prime \((2)\) identifies the relevant field automorphism as arithmetic Frobenius at \((2)\), up to the global Artin-reciprocity inversion convention;

3. the relabeling symmetry
   \[
   g\mapsto ug
   \]
   is the Artin action of
   \[
   \mathbb F_p^\times;
   \]

4. class-group effects explain multiple HI branches: at \(p=19\), the two reconstructed branches are exactly the Hilbert-class conjugate factors of the full ray-field polynomial once the initial phase recognition is accepted;

5. exceptional unit structure explains anomalies such as \(p=11\);

6. a direct Stark/Shintani construction may provide a route to proving existence for infinitely many cyclic Haagerup–Izumi categories without numerical algebraic reconstruction.

---

# 20. References to keep open

Primary HI / Izumi references used in this exploration:

- [Huang–Lin, arXiv:2007.00670](https://arxiv.org/abs/2007.00670)
  Transparent gauge and explicit \(F\)-symbol calculations.

- [Evans–Gannon, arXiv:1506.03546](https://arxiv.org/abs/1506.03546)
  Non-unitary fusion categories and their doubles via endomorphisms; a later generalization of the HI/Q-system framework.

- [Evans–Gannon, arXiv:1006.1326](https://arxiv.org/abs/1006.1326)
  Twisted Haagerup–Izumi modular data; Section 4.1 contains equations (4.1)–(4.3), the exact \(p=7\) construction, and the numerical phase seeds for \(p=11,13,17,19\).

Stark / real quadratic references to inspect:

- [PARI/GP documentation for `bnrstarkunit`](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html#bnrstarkunit).
- [Kopp, *The Shintani–Faddeev modular cocycle: Stark units from q-Pochhammer ratios*, arXiv:2411.06763](https://arxiv.org/abs/2411.06763).
- [Kopp, *SIC-POVMs and the Stark conjectures*](https://doi.org/10.1093/imrn/rnz153). Its quadratic base field is different from the HI field here, so this is a structural analogy rather than a direct identification.

---

# 21. Completed exact \(p=17\) Stark comparison

All computations in this section were run with PARI/GP 2.17.4 and are reproduced by `z17_stark_test.gp`.

## 21.1 Correct ray modulus

PARI orders the roots of
\[
y^2-17y-1
\]
as
\[
\delta_-=-0.058621\ldots,
\qquad
\delta_+=17.058621\ldots.
\]

Consequently the physical place \(\delta>0\) is the second real place, and the intended input is

```gp
pp  = idealhnf(bnf, delta - 1);
bnr = bnrinit(bnf, [pp, [0,1]], 1);
```

The relevant ray groups are

| infinite part | ray group |
|---|---:|
| none | \(C_8\) |
| \(\infty_-\) | \(C_8\), with redundant infinite part |
| \(\infty_+\) | \(C_{16}\) |
| \(\infty_-\infty_+\) | \(C_{16}\), with redundant \(\infty_-\) |

Thus
\[
\operatorname{Cl}_{(\delta-1)\infty_+}(K_{17})\simeq C_{16}.
\]

## 21.2 Exact HI unit polynomial

Write
\[
P_2(z)=P_e(z^2)+zP_o(z^2)
\]
and let \(e=-B^2/\delta\). Its monic polynomial is obtained exactly as
\[
E(X)
=
\delta^{-16}\operatorname{Res}_z(P_2(z),z^2+\delta X)
=
\delta^{-16}
\left(P_e(-\delta X)^2+\delta X P_o(-\delta X)^2\right).
\]

It has the reciprocal form
\[
E(X)=X^{16}+\sum_{j=1}^7 c_j(X^{16-j}+X^j)+c_8X^8+1,
\]
with
\[
\begin{aligned}
c_1={}&5161\delta-88037,\\
c_2={}&-162681688\delta+2775125324,\\
c_3={}&2224285803398\delta-37943249370668,\\
c_4={}&-13169066631628602\delta+224646121653727220,\\
c_5={}&27687887695366003925\delta-472317193126595318329,\\
c_6={}&-17815979606089964004310\delta+303916050690909978642141,\\
c_7={}&3918293373380552919833799\delta-66840683129156896141024224,\\
c_8={}&-175532701751128886825808423\delta
       +2994345899737840449537231154.
\end{aligned}
\]

Exact checks give:

- \(E\) is irreducible over \(K_{17}\);
- \(E\) is reciprocal with constant term \(1\), so \(e\) is a relative norm-one algebraic unit;
- \(K_{17}(e)=K_{17}(B)\);
- the relative field discriminant is
  \[
  \mathfrak D_{K_{17}(e)/K_{17}}=(\delta-1)^{15};
  \]
- the absolute discriminant is
  \[
  293^{16}17^{15}
  =8445312928482424626719575461796488049229751237996868073393;
  \]
- the absolute signature is \((16,8)\): the physical-place roots lie on the unit circle, while all sixteen roots at the conjugate real place are positive.

## 21.3 Comparison with PARI's Stark orbit

`bnrstarkunit` returns a different irreducible reciprocal polynomial \(S\) of degree \(16\). Nevertheless:

1. \(S\) has the same relative discriminant \((\delta-1)^{15}\).
2. `rnfpolredabs` reduces \(E\) and \(S\) to the same relative field polynomial.
3. Independently, `nfisisom` finds sixteen isomorphisms between their absolute fields, and every one fixes \(K_{17}\).

Therefore the HI unit and PARI's Stark unit generate exactly the same relative ray field.

They are not related by a pure power. An absolute unit-group computation shows that the HI unit vector and every individual Stark-conjugate unit vector have rank \(2\); hence there are no nonzero integers \(a,b\) with
\[
e^a=\pm\sigma(s)^b.
\]

There is, however, a particularly short exact orbit relation. Compatible roots can be chosen so that, for a generator \(\sigma\) of \(G\simeq C_{16}\),
\[
\boxed{
e^2=\frac{s^2}{\sigma^2(s)}.
}
\]

Equivalently, if \(\rho=\sigma^2\) generates the order-eight subgroup \(G^2\), then
\[
e^2=s^2/\rho(s).
\]

This automorphism has an intrinsic ray-class label. The rational prime \(2\) is inert in \(K_{17}\), so
\[
\mathfrak q_2=(2),
\qquad
N\mathfrak q_2=4.
\]
In the common absolute field, exact reduction gives
\[
\rho(s)\equiv s^4\pmod{\mathfrak q_2}.
\]
Consequently \(\rho=\operatorname{Frob}_{\mathfrak q_2}\), not merely an automorphism of the same order. Since the positive generator \(2\) has residue \(2\bmod(\delta-1)\), this is multiplication by \(2\) in the natural ray labeling, with the usual possible inversion depending on the Artin-map convention.

This exact quotient is the strongest evidence so far for a multiplicative-difference or cocycle construction of the HI phases. The algebraic comparison is exact. PARI's interpretation of \(S\) as the characteristic polynomial of an analytic Stark unit remains conditional on the Stark algebraicity conjecture, as documented for `bnrstarkunit`.

---

# 22. Completed \(p=11\) conductor analysis

Let
\[
\delta^2-11\delta-1=0,
\qquad
\epsilon=\frac{\delta-3}{5}=\frac{1+\sqrt5}{2},
\qquad
\delta=\epsilon^5.
\]

## 22.1 Secondary branch: exact quadratic ray field

For \(\mathfrak p_+=(\delta-1)\), the physical modulus \(\mathfrak p_+\infty_+\) has ray group \(C_2\). The polynomial from Section 9 is
\[
Q(t)=t^2+\frac{3\delta-4}{5}t+\delta,
\qquad
\operatorname{disc}Q=1-\delta.
\]

PARI returns the Stark polynomial
\[
S(u)=u^2+\frac{3\delta-24}{5}u+1.
\]

These generators are related exactly by
\[
\boxed{
Q(1+\epsilon^3u)=\epsilon^6S(u).
}
\]

Moreover, \(Q\) and PARI's relative class-field polynomial define the same quadratic extension, and
\[
\mathfrak D_{K_{11}(t)/K_{11}}=\mathfrak p_+,
\qquad
\mathfrak f=\mathfrak p_+\infty_+.
\]

Thus the secondary branch is exactly the simple quadratic ray field, and its displayed HI generator is an affine transform of PARI's norm-one Stark unit.

## 22.2 Principal branch: the missing prime over \(5\)

Refining the published Evans–Gannon phase seed and recognizing the orbit of
\[
\eta=-B_{g,2g}^2/\delta
\]
gives the reciprocal polynomial
\[
P_\eta(X)=X^{10}+c_1X^9+c_2X^8+c_3X^7+c_4X^6+c_5X^5
           +c_4X^4+c_3X^3+c_2X^2+c_1X+1,
\]
where
\[
\begin{aligned}
c_1&=144\delta-1597,\\
c_2&=854377-77039\delta,\\
c_3&=15771418\delta-174907704,\\
c_4&=13808071707-1245073049\delta,\\
c_5&=27511525729\delta-305107495744.
\end{aligned}
\]

The reproducible 100-digit refinement in `z11_stark_test.gp` gives residuals below \(4.2\times10^{-100}\) over every instance of (4.2) and all \(11^4\) instances of (4.3), and a maximum coefficient error below \(6.4\times10^{-99}\). A separate 180-digit run gives corresponding bounds \(3.7\times10^{-181}\) and \(3.6\times10^{-170}\). Polynomial recognition is the sole numerical-to-exact step; once this reconstructed polynomial is accepted as input, all following statements are exact PARI calculations:

- \(P_\eta\) is irreducible over \(K_{11}\);
- if \(\mathfrak q_5\) is the ramified prime above \(5\), then
  \[
  \boxed{
  \mathfrak f
  =\mathfrak p_+\mathfrak q_5^2\infty_+
  =5\mathfrak p_+\infty_+;
  }
  \]
- the full ray group for this conductor is \(C_{10}\), and \(P_\eta\) defines the full ray field rather than a proper quotient;
- the relative discriminant is
  \[
  \mathfrak D=\mathfrak q_5^{16}\mathfrak p_+^9;
  \]
- the absolute discriminant is
  \[
  -5^{26}11^9
  =-3513615863025188446044921875.
  \]

This confirms the earlier guess that the ramified prime over \(5\) distinguishes the principal branch. The identification is still conditional on the numerical-to-exact reconstruction of \(P_\eta\), so an independent reconstruction or direct verification of the Izumi equations remains desirable.

---

# 23. Explicit Shintani–Faddeev parameters for the HI ray classes

Kopp's ray-class/RM-point correspondence can be specialized explicitly to the HI fields. This is a derivation from Theorem 3.14 and Theorem 8.2 of [arXiv:2411.06763](https://arxiv.org/abs/2411.06763), not a formula stated there specifically for Haagerup–Izumi data.

View \(K_p\) through the real embedding \(\rho_1(\delta)=\delta_-<0\), leaving the physical place as Kopp's distinguished second embedding, and put
\[
\beta=-\delta=\delta_+^{-1}>0,
\qquad
M=\begin{pmatrix}1&p\\p&p^2+1\end{pmatrix},
\qquad
\mathbf r_u=-\frac{u}{p}\binom11.
\]

Then
\[
M\beta=\beta,
\qquad
j_M(\beta)=\beta^{-2}>1,
\qquad
M\equiv I\pmod p.
\]

Kopp's denominator parameter becomes
\[
[[\mathbf r_u,\beta]]
=\frac{u(1-\beta)}p
=\frac{u(1+\delta)}p
=\frac{u\delta}{\delta-1},
\]
so its denominator ideal is exactly \(\mathfrak p_+=(\delta-1)\). Taking the totally positive generator
\[
\alpha=\delta(\delta-1)
\]
of \(\mathfrak p_+\), the correspondence produces
\[
\gamma_u
=\alpha[[\mathbf r_u,\beta]]
=u\delta^2
\equiv u\pmod{\mathfrak p_+}.
\]

Thus the characteristics \(\mathbf r_u\), for \(u\in\mathbb F_p^\times\), carry exactly the desired residue-class labeling. For \(p=17\), they exhaust the sixteen ray classes.

For this specialization the theta and eta multiplier factors simplify to \(1\). Since the two-infinite-place to one-infinite-place ray-class map has trivial fiber at \(p=17\), Kopp's formula becomes
\[
\exp\!\left(2Z'(0,\mathfrak A_u)\right)
=
\operatorname{shin}^{\mathbf r_u}_M(\beta)^2.
\]

This also explains why the sign in
\[
\varepsilon_{\mathrm{HI}}=-U^2
\]
is natural: at \(\rho_1\), \(\delta<0\), so \(U=B/\sqrt\delta\) is imaginary and \((iU)^2=-U^2\).

The exact algebraic comparisons at \(p=7,13,17\) now identify the quotient automorphism by reduction at \((2)\): after a compatible Galois shift of the Stark root,
\[
\boxed{
e_u^2=\frac{s_u^2}{\operatorname{Frob}_{(2)}(s_u)}.
}
\]
After a compatible identification of the HI multiplier orbit with the displayed residue-class labeling, this reads \(e_u^2=s_u^2/s_{2u}\), up to the global arithmetic-versus-geometric Artin convention. That individual-root alignment is not encoded by the present minimal-polynomial tests. The next analytic computation is therefore sharper: evaluate Kopp's Shintani–Faddeev values for the displayed \((M,\beta,\mathbf r_u)\), fix their root normalization and Artin convention, and determine whether this exact Frobenius quotient is a standard cocycle or distribution relation.

---

# 24. Exact \(p=7\) comparison

The \(p=7\) case can be derived without numerical reconstruction. Evans–Gannon's proof of Theorem 5(d) in [arXiv:1006.1326](https://arxiv.org/abs/1006.1326) gives an exact construction of the entry
\[
a=B_{1,2}.
\]

Eliminating their auxiliary quadratic element \(b\) from the displayed cubic for \(a\) gives
\[
\begin{aligned}
P_a(W)={}&W^6-W^5+(\delta-7)W^4+(9-3\delta)W^3+W^2\\
&-(7\delta+1)W+(50\delta+7).
\end{aligned}
\]

For \(e=-a^2/\delta\), exact elimination yields
\[
\boxed{
\begin{aligned}
E_7(X)={}&X^6+(15\delta-107)(X^5+X)\\
&+(-503\delta+3591)(X^4+X^2)\\
&+(5153\delta-36794)X^3+1.
\end{aligned}
}
\]

For
\[
K_7=\mathbb Q(\delta),
\qquad
\delta^2-7\delta-1=0,
\qquad
\mathfrak p_+=(\delta-1),
\]
PARI gives
\[
\operatorname{Cl}_{\mathfrak p_+\infty_+}(K_7)\simeq C_6.
\]

Its `bnrstarkunit` polynomial is
\[
\begin{aligned}
S_7(X)={}&X^6+(19\delta-137)(X^5+X)\\
&+(-503\delta+3591)(X^4+X^2)\\
&+(1635\delta-11672)X^3+1.
\end{aligned}
\]

As at \(p=17\):

- \(E_7\neq S_7\), and no HI root is pure-power-related to an individual Stark conjugate;
- both polynomials are irreducible and define exactly the same relative field;
- both fields have relative discriminant \(\mathfrak p_+^5\);
- for compatible roots \(e,s\) and a generator \(\sigma\in C_6\),
  \[
  \boxed{
  e^2=\frac{s^2}{\sigma^2(s)}.
  }
  \]

Equivalently, \(e^2=s^2/\rho(s)\) for a generator \(\rho\) of the order-three subgroup \(G^2\). Because the HI input here is exact, this proves that the quotient pattern is not an artifact of the \(p=17\) numerical reconstruction.

Here too the quotient automorphism is determined intrinsically. The prime \((2)\) is inert with norm \(4\), and exact reduction in the common field gives
\[
\rho(s)\equiv s^4\pmod 2.
\]
Thus
\[
\rho=\operatorname{Frob}_{(2)},
\qquad
\operatorname{ord}(\rho)=3=\operatorname{ord}_7(2).
\]

All statements are reproduced by `z7_stark_test.gp`, including a certified base-field class/unit computation.

---

# 25. Completed \(p=13\) comparison and the Frobenius-\(2\) law

The \(p=13\) input begins with the Evans–Gannon numerical seed from Section 4.1 of [arXiv:1006.1326](https://arxiv.org/abs/1006.1326),
\[
j^{(13)}=(-3.1050384,\,0.5993399,\,-0.111708,\,-0.969766,\,1.336848,\,1.00483129).
\]
Six independent instances of their equation (4.2) refine these phases to 180 digits. All instances of (4.2), and all \(13^4\) instances of (4.3), then have numerical residual below \(3.7\times10^{-181}\). The script records 100 digits of the refined solution and recomputes the complete systems with residual below \(3.1\times10^{-100}\); its maximum coefficient error is \(1.1\times10^{-96}\). Thus polynomial recognition is the only numerical-to-exact step below.

For
\[
K_{13}=\mathbb Q(\delta),
\qquad
\delta^2-13\delta-1=0,
\qquad
e=-B_{g,2g}^2/\delta,
\]
the recognized orbit polynomial is
\[
E_{13}(X)=X^{12}+\sum_{j=1}^{5}c_j(X^{12-j}+X^j)+c_6X^6+1,
\]
where
\[
\begin{aligned}
c_1&=467\delta-6097,\\
c_2&=12814191-979939\delta,\\
c_3&=825835784\delta-10799019382,\\
c_4&=3392673833885-259448689016\delta,\\
c_5&=30448109649290\delta-398153890397194,\\
c_6&=11724621314790962-896619533298169\delta.
\end{aligned}
\]

The following statements are then exact:

- the physical ray group is
  \[
  \operatorname{Cl}_{(\delta-1)\infty_+}(K_{13})\simeq C_{12};
  \]
- \(E_{13}\) is irreducible and reciprocal, and its field has conductor exactly \((\delta-1)\infty_+\), so it is the full ray field;
- the relative discriminant is \((\delta-1)^{11}\);
- the absolute discriminant and signature are
  \[
  173^{12}13^{11}
  =1288042262034535290413536071230037719077,
  \qquad
  (r_1,r_2)=(12,6);
  \]
- PARI's degree-twelve Stark polynomial is different from \(E_{13}\), but the two absolute fields admit twelve \(K_{13}\)-preserving isomorphisms.

For a compatible HI root \(e\), Stark root \(s\), and one order-twelve generator \(\tau\), the exhaustive exact two-conjugate search finds one relation per HI conjugate, always with the same displacement. One representative is
\[
e^2=\frac{\tau^8(s)^2}{\tau(s)}.
\]
Putting \(s_0=\tau^8(s)\) and \(\rho=\tau^5\) gives
\[
\boxed{
e^2=\frac{s_0^2}{\rho(s_0)}.
}
\]

Finally, \(2\) is inert in \(K_{13}\), the prime \(\mathfrak q_2=(2)\) has norm \(4\), and its ray class generates \(C_{12}\). Exact reduction gives
\[
\rho(s)\equiv s^4\pmod{\mathfrak q_2},
\]
so
\[
\rho=\operatorname{Frob}_{\mathfrak q_2},
\qquad
\operatorname{ord}(\rho)=12=\operatorname{ord}_{13}(2).
\]

Together, the three completed cases give
\[
\begin{array}{c|c|c}
p & \operatorname{ord}_p(2) & \operatorname{ord}(\operatorname{Frob}_{(2)})\\ \hline
7&3&3\\
13&12&12\\
17&8&8
\end{array}
\]
and, more strongly than this order coincidence, the reduction calculations identify the field automorphism itself. After choosing a compatible identification between the HI multiplier orbit and the ray-class labels, the resulting sharpened conjecture is
\[
\boxed{
e_u^2=\frac{s_u^2}{s_{2u}}.
}
\]
The field-theoretic statement using \(\operatorname{Frob}_{(2)}\) is exact. Two labeling points remain to be fixed analytically: whether a chosen reciprocity map labels arithmetic Frobenius by \(2\) or \(2^{-1}\), and which individual HI root carries the ray label \(u=1\).

All exact checks, together with the recorded 100-digit reconstruction test, are reproduced by `z13_stark_test.gp`.

---

# 26. The two \(p=19\) branches and the Hilbert class field

The class-number-two case now admits a precise explanation. Put
\[
K=K_{19}=\mathbb Q(\delta),
\qquad
\delta^2-19\delta-1=0,
\qquad
\mathfrak p=(\delta-1).
\]
PARI certifies
\[
\operatorname{Cl}(K)\simeq C_2,
\]
and the physical ray group is
\[
\boxed{
\operatorname{Cl}_{\mathfrak p\infty_+}(K)
\simeq C_{18}\times C_2.
}
\]
Thus the order is \(36\), as predicted earlier, but the group is not cyclic.

## 26.1 The residue-(2) subgroup and the class-group quotient

The prime \(\mathfrak q_2=(2)\) is inert in \(K\), with norm \(4\). In PARI's displayed \(C_{18}\times C_2\) coordinates its ray class is \([10,1]\), of order
\[
18=\operatorname{ord}_{19}(2).
\]
Because \((2)\) is principal, its class lies in the kernel of the natural map
\[
\operatorname{Cl}_{\mathfrak p\infty_+}(K)
\longrightarrow
\operatorname{Cl}(K).
\]
Both that kernel and \(\langle\operatorname{Frob}_{(2)}\rangle\) have order \(18\), so they are equal. Moreover,
\[
\operatorname{Frob}_{(2)}^9=c,
\]
where \(c\) is complex conjugation; this is the class-field version of \(2^9\equiv-1\pmod {19}\).

The fixed field of this order-eighteen subgroup is the Hilbert class field
\[
H=K\!\left(\sqrt{58-3\delta}\right)
  =\mathbb Q(\sqrt5,\sqrt{73}).
\]
PARI gives the relative and absolute equations
\[
X^2+3\delta-58,
\qquad
X^4-59X^2+49,
\]
and \(\operatorname{disc}(H)=365^2\), confirming that \(H/K\) is everywhere unramified.

This makes the two-branch mechanism nearly forced: the two cosets of the subgroup generated by Frobenius at \(2\) are exactly the two ordinary ideal classes. The nontrivial class involution exchanges the cosets, while Frobenius at \(2\) moves transitively inside each one.

The full ray field \(L/K\) has
\[
\mathfrak D_{L/K}=\mathfrak p^{34},
\qquad
|\operatorname{disc}L|=365^{36}19^{34},
\qquad
(r_1,r_2)=(36,18).
\]
PARI's full `bnrstarkunit` polynomial is irreducible, reciprocal, and of degree \(36\). If \(s\) is one of its roots, the trace \(s+s^{-1}\) has an irreducible degree-eighteen polynomial whose field is exactly the finite-ray, maximal totally real subfield; its relative discriminant is \(\mathfrak p^{16}\).

## 26.2 Reconstruction of the two HI branches

Both Evans–Gannon \(p=19\) phase seeds were Newton-refined to 450 digits. The regression script retains about 115 digits and checks every instance of equations (4.2) and (4.3) for both branches. From the two \(t=2\) orbits, set
\[
e=-B_{u,2u}^2/\delta.
\]
Their combined orbit has the reciprocal polynomial
\[
E_{19}(X)
=X^{36}+\sum_{j=1}^{17}c_j(X^{36-j}+X^j)+c_{18}X^{18}+1.
\]
The full coefficient list is recorded in `z19_stark_test.gp`; useful fingerprints are
\[
\begin{aligned}
c_1={}&-333455+17502\delta,\\
c_{18}={}&313454105109270988272887994762348265080330293\\
&-16452136243396368439735966221635671877278307\delta.
\end{aligned}
\]

Polynomial recognition is the only numerical-to-exact step. Once \(E_{19}\) is accepted, exact PARI calculations show that it is irreducible over \(K\), has conductor exactly \(\mathfrak p\infty_+\), has trivial norm subgroup in \(C_{18}\times C_2\), and has relative discriminant \(\mathfrak p^{34}\). It therefore defines the full ray field. It differs from PARI's Stark polynomial, but both generators define the unique full ray extension attached to the same conductor and norm subgroup.

Each branch separately becomes algebraic over \(H\), not over \(K\). If \(w,w'\) are the first nontrivial coefficients of the two conjugate degree-eighteen branch polynomials, then
\[
w+w'=-333455+17502\delta,
\]
\[
ww'=61207710-3212584\delta.
\]
The resulting quadratic coefficient field is unramified over \(K\) and reduces to
\[
X^2+\delta-29;
\]
it is the same Hilbert class field \(H\). All remaining branch coefficients were recognized in \(K(w)\), and their exact Hilbert conjugate norm is \(E_{19}\).

This is a direct arithmetic realization of the old branch hypothesis:
\[
\boxed{
\text{the two HI branches are the two Hilbert-class conjugate halves of one ray-class orbit.}
}
\]
It also explains why Evans–Gannon's second modular-data label involves the pair \(\{5,73\}\): these are precisely the two prime-discriminant factors whose genus field is \(\mathbb Q(\sqrt5,\sqrt{73})\).

## 26.3 Status of the Stark quotient at \(p=19\)

A high-precision all-pairs root search finds exactly \(36\) matches of the form
\[
e_k^2=\frac{s_i^2}{s_j}.
\]
The selected edges form a permutation of the Stark roots with cycle lengths \([18,18]\), and its ninth power sends every root to its inverse. This is exactly the cycle signature of a generator of
\[
\langle\operatorname{Frob}_{(2)}\rangle
=\ker\!\left(\operatorname{Cl}_{\mathfrak p\infty_+}(K)\to\operatorname{Cl}(K)\right).
\]
This comparison is numerical, unlike the exact reductions modulo \(2\) at \(p=7,13,17\). It does not yet distinguish \(\operatorname{Frob}_{(2)}\) from another generator of the same cyclic subgroup. The branchwise conjecture is therefore
\[
\boxed{
e_{b,u}^2
=\frac{s_{b,u}^2}{s_{b,2u}},
\qquad
b\in\operatorname{Cl}(K)\simeq C_2,
}
\]
subject to exact Artin/root alignment.

The exact ray arithmetic is reproduced by `z19_ray_test.gp`; the numerical reconstruction and exact downstream HI-field checks are in `z19_stark_test.gp`.

---

# 27. Group-ring and Shintani–Faddeev reformulation

The quotient law now has a useful intrinsic form. Let
\[
G=\operatorname{Gal}(L/K),
\qquad
\phi=\operatorname{Frob}_{(2)},
\qquad
H=\langle\phi\rangle,
\qquad
t=e^2.
\]
With multiplicative group-ring notation, the exact \(p=7,13,17\) relation is
\[
\boxed{
t=s^{\Theta_2},
\qquad
\Theta_2=2-\phi.
}
\]
The opposite Artin convention replaces \(\phi\) by \(\phi^{-1}\).

## 27.1 Why the operator loses no field information

If \(d=\operatorname{ord}(\phi)\), define
\[
\Psi_d=2^{d-1}+2^{d-2}\phi+\cdots+\phi^{d-1}.
\]
Then
\[
(2-\phi)\Psi_d=2^d-\phi^d=2^d-1,
\]
and hence
\[
t^{\Psi_d}=s^{2^d-1}.
\]
On each \(H\)-coset,
\[
\operatorname{coker}\!\left(
\mathbb Z[H]\xrightarrow{\,2-\phi\,}\mathbb Z[H]
\right)
\simeq \mathbb Z/(2^d-1),
\]
while characterwise the eigenvalues are \(2-\chi(\phi)\), none of which vanish. Because the ray fields here have a real embedding, their only roots of unity are \(\{\pm1\}\); since \(2^d-1\) is odd, the relation implies
\[
K(s)=K(e^2).
\]
This gives a conceptual reason, independent of polynomial reduction, that the Frobenius quotient still generates the full Stark field.

It is important not to call \(t\) uniformly a Hilbert–90 coboundary. What is always a coboundary is
\[
\frac ts=\frac{s}{\phi(s)}=s^{1-\phi},
\]
so \(N_H(t)=N_H(s)\). At \(p=13\) and \(17\) this subgroup norm is \(1\). At \(p=7\) it is not: the exact absolute polynomial of \(N_H(s)\) is
\[
X^4-932X^3+70X^2-932X+1.
\]
These norm assertions are now included in the corresponding GP scripts.

## 27.2 A sharper analytic candidate

Kopp defines the Shintani–Faddeev modular cocycle on the upper half-plane by
\[
\operatorname{shin}^{\mathbf r}_{A}(\tau)
=\frac{\varpi_{\mathbf r}(A\tau)}{\varpi_{\mathbf r}(\tau)}.
\]
For the odd-denominator characteristics \(\mathbf r_u\) of Section 23,
\[
\Gamma_{\mathbf r_u}=\Gamma_{2\mathbf r_u}.
\]
Therefore
\[
D^{\mathbf r}_{2,A}(\tau)
:=
\frac{\operatorname{shin}^{\mathbf r}_{A}(\tau)^2}
     {\operatorname{shin}^{2\mathbf r}_{A}(\tau)}
\]
is itself a modular \(1\)-cocycle. On the upper half-plane it is the literal coboundary of
\[
F^{\mathbf r}_2(\tau)
=\frac{\varpi_{\mathbf r}(\tau)^2}{\varpi_{2\mathbf r}(\tau)}.
\]
As with Kopp's original cocycle, extension to the larger domain containing an RM boundary point can leave a nontrivial cohomology class.

Under the Stark normalization in Section 23,
\[
s_u=\operatorname{shin}^{\mathbf r_u}_{M}[\beta]^2
\]
up to the already noted inversion and multiplier conventions. Consequently
\[
\left(D^{\mathbf r_u}_{2,M}[\beta]\right)^2
=\frac{s_u^2}{s_{2u}}.
\]
The algebraic result therefore suggests the unsquared formula
\[
\boxed{
e_u
=\pm
\frac{\operatorname{shin}^{\mathbf r_u}_{M}[\beta]^2}
     {\operatorname{shin}^{2\mathbf r_u}_{M}[\beta]}.
}
\]
This characteristic-difference cocycle is a substantially sharper analytic target than a literal Stark-unit equality.

It is not Kopp's conductor-lowering relation in disguise. Theorem 4.46 applied to doubling uses a determinant-four matrix and a product over four half-characteristics; standard arithmetic smoothing at the inert ideal \((2)\) likewise has weight \(N(2)=4\). The observed operator \(2-\phi\) is instead a square-root, or weight-one, analogue. Establishing the algebraicity, sign, and Shimura-reciprocity law of this unsquared RM value appears to be the genuinely new theorem required.

More generally, for \(c\) coprime to \(p\), put
\[
D_{c,u}=\frac{q_u^c}{q_{cu}},
\qquad
\Theta_c=c-\sigma_c.
\]
Then the formal identities
\[
\Theta_{ab}=b\Theta_a+\sigma_a\Theta_b,
\qquad
D_{ab,u}=D_{a,u}^{\,b}D_{b,au}
\]
give a weighted semigroup distribution law. Whether the other HI ratio types \(B_{u,cu}\) realize these \(D_c\) is now a concrete test rather than a vague search for unit relations.

The best first analytic experiment is the exact \(p=7\) case: evaluate \(D_{2,M}^{\mathbf r_1}[\beta]\), fix its sign and Artin orientation against the known algebraic HI root, and only then attempt a proof from quantum-dilogarithm or theta identities.

---


---

# 28. A diagonal-determination theorem for the full fourth-power core

The short Frobenius law contains more information than Section 14 suggested.
The following argument is algebraic and works for every finite abelian group
of odd order. It requires a **labeled** doubling law in a common field;
equality of orbit polynomials alone does not supply that hypothesis.

## 28.1 Correct cyclic phase normalization

The Evans–Gannon phases in Section 4 are initially given for integer
representatives \(0<g<h<n\). Put \(r=(n-1)/2\) and
\(C=j_r+j_{r+1}\). Their extension rule says \(j_{n-g}=C-j_g\).
The periodic phases to use in identities on \(\mathbb Z_n\) are
\[
 z_0=1,\qquad z_g=\exp\!\left(i(j_g-Cg/n)\right),\quad 1\le g<n.
\]
Then \(z_{-g}=z_g^{-1}\), and the generic formula
\(U_{g,h}=z_h/(z_gz_{h-g})\) holds with indices reduced modulo \(n\).
Using the raw published \(e^{ij_g}\) as a periodic sequence would miss
the correction at wraparound.

Define an auxiliary normalized cocycle
\[
 C(a,b)=\frac{z_{a+b}}{z_az_b},\qquad V(a,b)=C(a,b)^4.
\]
Thus \(C(a,b)=U_{a,a+b}\) when \(a,b,a+b\ne0\), while
\(C(a,0)=C(0,a)=C(a,-a)=1\). These auxiliary boundary values are
**not** the actual exceptional scaled matrix entries.

Both cocycles are symmetric and satisfy
\[
 V(a,b)V(a+b,c)=V(b,c)V(a,b+c).
\]

## 28.2 Diagonal determination

**Proposition.** Let \(V\) be a normalized symmetric multiplicative
\(2\)-cocycle on a finite abelian group \(G\) of odd order, taking values
in a number field \(L\) with a real embedding. Suppose \(s_a\in L^\times\),
\(s_0=1\), and
\[
 V(a,a)=s_a^2/s_{2a}\quad(a\in G).
\]
Then
\[
 \boxed{V(a,b)=s_as_b/s_{a+b}\quad(a,b\in G).}
\]

**Proof.** Divide \(V\) by the symmetric cocycle
\(R(a,b)=s_as_b/s_{a+b}\), obtaining \(W\) with \(W(a,a)=1\).
For any symmetric cocycle, comparing the two groupings of
\((a,a,b,b)\) gives
\[
 W(2a,2b)=W(a,b)^2
 \frac{W(a+b,a+b)}{W(a,a)W(b,b)}=W(a,b)^2.
\]
Choose \(d\) such that multiplication by \(2^d\) is the identity on
\(G\). Iteration yields \(W(a,b)^{2^d-1}=1\). A field with a real
embedding has only the roots of unity \(\{\pm1\}\), and \(2^d-1\)
is odd. Hence \(W(a,b)=1\). ∎

In particular, assuming the common-field and labeling hypotheses, the
doubling law in Section 27 implies the **entire** generic formula
\[
 \boxed{
 U_{g,h}^4=\frac{s_gs_{h-g}}{s_h},\qquad
 B_{g,h}^4=\delta^2\frac{s_gs_{h-g}}{s_h}.
 }
 \tag{28.1}
\]
For \(h=2g\), this is precisely \(e_g^2=s_g^2/s_{2g}\).
The formula is compatible with rotation and with reflection/conjugation
when \(s_{-g}=s_g^{-1}\). Section 29 verifies it with exact labels,
for all entries, in the five completed cases.

This argument neither assumes a primitive root \(2\) nor assumes that
\(\delta\) is fundamental or that the base class number is one.
It also explains why a field hypothesis matters: in \(\mathbb C^\times\)
alone there can be odd-order torsion ambiguities.

## 28.3 Correction to the proposed higher-multiplier formula

For an integer \(2\le c<n\) and a unit \(g\bmod n\), (28.1) gives
\[
 U_{g,cg}^4=\frac{s_gs_{(c-1)g}}{s_{cg}}.
\]
In contrast, telescoping gives
\[
 \boxed{
 \prod_{j=1}^{c-1}U_{g,(j+1)g}^4=\frac{s_g^c}{s_{cg}}.
 }
 \tag{28.2}
\]
Thus the weighted operator \(c-\sigma_c\) at the end of Section 27
describes a product of adjacent generic entries. Its identification with
a single ratio type is appropriate only at \(c=2\), unless an additional
special identity holds. Formula (28.1), with three Stark factors, is the
uniform expression for individual entries.

---

# 29. Exact construction from Stark polynomials without HI seeds

The new file [`hi_stark_seedless.gp`](hi_stark_seedless.gp) starts with
\[
 S=\operatorname{bnrstarkunit}
 \left(K_n,\,(\delta-1)\infty_+\right)
\]
and constructs a full matrix over its field. There is no numerical HI
seed, Newton iteration, coefficient recognition, or numerical root
selection in this construction.

PARI's general analytic Stark interpretation remains conjectural. That
does not make these **finite existence certificates** conditional:
the returned polynomial supplies exact algebraic input, and the
constructed matrix is checked against the complete defining equations.
An incorrect analytic guess would simply fail those checks.

The precise construction is as follows.

1. Certify the quadratic class/unit computation and check the returned
   polynomial's irreducibility, conductor, and full ray degree. Express
   its root \(s\) and \(\delta\) in an absolute number field \(L\).
2. Choose a small prime \(\ell\) inert in \(K_n\) that generates
   \(\mathbb F_n^\times\). Identify arithmetic Frobenius at \((\ell)\)
   by reduction of **every integral-basis element** at a prime above
   \(\ell\). This avoids relying on a particular polynomial having
   index coprime to \(\ell\).
3. Set \(s_{\ell^j}=\phi^j(s)\) and \(s_0=1\). Repeated ray labels are
   permitted: at \(n=11,29\), \(\phi\) has smaller order than \(n-1\).
4. For \(2\le h\le(n+1)/2\), find the roots **inside \(L\)** of
   \[
    X^4-\delta^2s_1s_{h-1}/s_h.
   \]
   There are exactly two, differing by sign, in each completed case.
   Initially select either one. Set \(B_{1,n+1-h}=B_{1,h}\).
5. Define \(P_1=1\), \(P_h=\prod_{j=2}^hB_{1,j}\). Reconstruct
   \[
    \boxed{B_{g,h}=P_h/(P_gP_{h-g})\quad(0<g<h<n).}
    \tag{29.1}
   \]
   Extend by conjugation, and insert the exceptional entries from
   Section 4. No square root of \(\delta\) is needed in (29.1).
6. Use the sign-transport theorem in Section 30 to impose
   \(\phi(B_{g,h})=B_{\ell g,\ell h}\), and check the resulting
   linear system over \(\mathbb F_2\). Exactly one global generic
   sign remains. Test its two choices against the quadratic equations.
7. Verify rotation, conjugation, generic norms, every formula (28.1),
   and the full quadratic and cubic Izumi systems, with exact field
   arithmetic.

To justify physical unitarity rather than just a formal involution,
the script proves that \(s+s^{-1}\) generates a totally real subfield
of index two, that \(\phi^{(n-1)/2}(s)=s^{-1}\), and that every real
embedding of \(L\) has \(\delta<0\). Therefore this involution is actual
complex conjugation at the physical embeddings \(\delta>0\).
The checked identities \(B_{g,h}\overline{B_{g,h}}=\delta\) give the
required positive physical norms.

## 29.1 Completed exact certificates

The full results are recorded in
[`hi_stark_seedless_results.txt`](hi_stark_seedless_results.txt).

| \(n\) | ray group | \([L:\mathbb Q]\) | rank of sign system | cubic representatives checked |
|---:|---|---:|---:|---:|
| 7 | \(C_6\) | 12 | 2 | 401 |
| 11 | \(C_2\) | 4 | 4 | 1465 |
| 13 | \(C_{12}\) | 24 | 5 | 2381 |
| 17 | \(C_{16}\) | 32 | 7 | 5221 |
| 29 | \(C_4\) | 8 | 13 | 25261 |

The cubic counts cover **every** quadruple: after verifying multiplier
covariance, each nonzero \((g,h,k,l)\) has a unique scalar multiple
whose first nonzero coordinate is \(1\). Include the zero quadruple.
The count is
\[
 1+\frac{n^4-1}{n-1}=n^3+n^2+n+2.
\]
The script uses the scaled equations
\[
 \sum_j B_{g+j,h}\overline{B_{j,h}}
 = (\delta-1)^2\left(\mathbf1_{g=0}-\frac{\mathbf1_{h=0}}\delta\right),
 \tag{29.2}
\]
\[
 \begin{split}
 \sum_j B_{j,g+h}\overline{B_{j+k,g}B_{j+l,h}}
 ={}&(\delta-1)B_{g+l,k}B_{h+k,l}\\
 &-\frac{(\delta-1)^3}{\delta}\mathbf1_{g=0}\mathbf1_{h=0}.
 \end{split}
 \tag{29.3}
\]
Together with the checked symmetries, these are exactly the
Evans–Gannon/Izumi conditions. Their sufficiency for the corresponding
subfactor and HI fusion rules is the result used from
[Evans–Gannon, Section 4.1 and Theorem 6](https://arxiv.org/html/1006.1326#S4).

These are certificates of the construction in this repository, not a
claim that existence at these five orders is new to the literature.

## 29.2 Removal of numerical-recognition assumptions

As **downstream** checks, the script proves:

- at \(n=11\), its \(B_{1,2}\) satisfies
  \(X^2+(3\delta-4)X/5+\delta\), identifying the simple-ray secondary
  branch of Section 22.1;
- at \(n=13\), the exact product
  \(\prod_{g\ne0}(X+B_{g,2g}^2/\delta)\) is exactly \(E_{13}\) of
  Section 25;
- at \(n=17\), all three exact products
  \(\prod_{g\ne0}(X-B_{g,tg})\), \(t=2,3,4\), agree with
  `z17_haagerup_izumi_minpolys.sage`.

Thus the old recognized polynomials really occur in complete exact
HI solutions. Their downstream field identifications no longer require
an assumption that the numerical phases were correctly recognized.
The principal \(n=11\) branch retains its previously stated
qualification. The later exact order-19 certificate and polynomial
assertions in Section 35.2 discharge the order-19 recognition issue.

## 29.3 Small explicit inputs for the fixed-field family

The two certificates over \(K=\mathbb Q(\sqrt5)\) start from particularly
small polynomials. With \(\epsilon=(1+\sqrt5)/2\), PARI returns
\[
 S_{11}(X)=X^2+(3\epsilon-3)X+1,
\]
\[
 S_{29}(X)=X^4+(14\epsilon-21)(X^3+X)
                    +(45-27\epsilon)X^2+1.
\]
Here \(\delta_{11}=\epsilon^5\) and
\(\delta_{29}=\epsilon^7\). Applying the construction above yields
complete exact matrices over fields of absolute degrees 4 and 8.
These two cases show concretely that a nonfundamental \(\delta\) and
the resulting collapse of residue labels are compatible with the
full fourth-power formula and exact sum identities.

## 29.4 The earlier class-number-two checkpoint, now completed

A bounded \(n=19\) run completed the exact field, Frobenius-label,
and physical-conjugation checks, and found both roots inside the
degree-72 absolute ray field for each of the nine independent row
quartics, \(2\le h\le10\). The transcript is
[`hi_stark19_partial_results.txt`](hi_stark19_partial_results.txt).
The run reached its ten-minute limit before completing matrix
verification. That bounded run alone was not a full certificate.
Section 35.2 records its completed continuation, including every cubic
equation and the exact identification of the earlier branch polynomial.

---

# 30. Why the sign problem has only one binary degree of freedom

The observed ranks in Section 29 have a structural explanation.

**Proposition.** Let \(p\) be odd prime. Suppose two normalized phase
cocycles \(C,C'\) on \(\mathbb Z_p\) have \(C(a,-a)=C'(a,-a)=1\).
Suppose their corresponding generic \(B\)-entries lie in a common
number field with a real embedding, have the same fourth powers, and
are equivariant for one automorphism implementing a primitive scalar
\(\ell\bmod p\). Then their generic entries agree everywhere, or all
differ by the same sign.

**Proof.** Their ratio \(W=C'/C\) is a normalized symmetric cocycle
with values in \(\{\pm1\}\). Write \(D(a)=W(a,a)\). The duplication
identity from Section 28 gives
\[
 W(2a,2b)=D(a+b)D(a)D(b).
\]
Since doubling is invertible, the function \(f(a)=D(a/2)\) satisfies
\[
 W(a,b)=f(a)f(b)/f(a+b).
\]
Equivariance fixes the signs, so \(W(\ell a,\ell b)=W(a,b)\).
Consequently \(f(\ell a)/f(a)\) is a homomorphism
\(\mathbb Z_p\to\{\pm1\}\), which is trivial. The scalar \(\ell\)
is transitive on nonzero indices; hence \(f\) is constant there.
Its value is either \(1\) or \(-1\). The associated coboundary equals
that value on every generic pair. ∎

This first proposition is an **at-most-two** statement. Under the
quartic-lift hypotheses of the construction, consistency also has a
uniform proof.

**Sign-transport proposition.** Suppose the arbitrary initial row
roots in Section 29 exist in \(L\), the labeled \(s_a\) have physical
modulus one, \(L\) has a real embedding with \(\delta<0\), and
\(\phi^{(p-1)/2}\) is physical complex conjugation.
Then signs making the reconstructed matrix scalar-equivariant exist.
They are determined up to the global generic sign above.

**Proof.** The row roots have physical modulus \(\sqrt\delta\).
Their reflection symmetry \(B_{1,h}=B_{1,p+1-h}\) permits a unit
phase sequence with \(z_{-a}=z_a^{-1}\): apply the prefix recursion
and choose \(z_1\) to close the cyclic sequence. Thus the initial
matrix defines a normalized phase cocycle \(C\).

Extend \(\phi\) to fix \(\sqrt\delta\). This is legitimate because
\(\sqrt\delta\notin L\): at a real embedding of \(L\) the element
\(\delta\) is negative. In particular the extension still satisfies
\(\phi^{(p-1)/2}=\) physical conjugation. Put
\[
 E(a,b)=\frac{\phi(C(a,b))}{C(\ell a,\ell b)}.
\]
The fourth-power formula shows \(E(a,b)^4=1\); the square roots of
\(\delta\) cancel in this quotient, so \(E(a,b)\in L\) and hence
\(E(a,b)\in\{\pm1\}\). It is a symmetric normalized cocycle.
As above,
\[
 E(a,b)=f(a)f(b)/f(a+b),\qquad f(a)=E(a/2,a/2).
\]
Write \(r=(p-1)/2\). Iterating the error equation \(r\) times gives
\[
 \prod_{j=0}^{r-1}E(\ell^j a,\ell^j b)
 =\frac{\overline{C(a,b)}}{C(-a,-b)}=1.
\]
Therefore \(F(a)=\prod_{j=0}^{r-1}f(\ell^j a)\) is a homomorphism
\(\mathbb Z_p\to\{\pm1\}\), so \(F(a)=1\).
Define \(t_0=1\), choose \(t_1=1\), and transport signs by
\[
 \boxed{t_{\ell a}=f(a)t_a.}
\]
The half-orbit product just proved ensures \(t_{-a}=t_a\) and
closure of the full orbit. Replacing \(C(a,b)\) by
\(C(a,b)t_at_b/t_{a+b}\) kills its covariance error and preserves
the normalization and conjugation conditions. ∎

Thus root-sign compatibility is not a further conjecture in prime
order once these field and fourth-root hypotheses are available.
Neither proposition asserts that the quadratic or cubic sum
identities hold; those remain separate requirements.

The row algorithm also makes the constraints explicit. There are
\((p-1)/2\) initial row signs. Formula (29.1) expresses the sign of
every entry as a linear expression in their bits. Comparing scalar
translates gives a linear system over \(\mathbb F_2\), of rank
\((p-3)/2\) in every completed case. The script constructs its
solution by the transport formula, checks every linear equation,
and verifies the rank. This replaces a search over
\(2^{(p-1)/2}\) phase choices with sign transport and two final tests.

For composite \(n\), multiplication by units is not transitive on
all nonzero residues. The prime-order conclusion must not be used
unchanged: additional sign freedoms can occur on the different gcd
strata.

---

# 31. One sequence and a Fourier formulation of the quadratic equations

There is a useful uniform formula that includes the exceptional entries.
For any odd \(n\), choose \(b_g\) with
\[
 b_0=-\delta^{-1/2},\qquad |b_g|=1\ (g\ne0),\qquad
 b_{-g}=\overline{b_g}.
\]
For a phase solution, take \(b_g=z_g^{-1}\) for \(g\ne0\).
Put
\[
 \lambda=\frac{\sqrt\delta}{\delta-1},\qquad
 \mu=1-\delta^{-1}.
\]
Then the whole matrix is
\[
 \boxed{
 A_{g,h}=\lambda b_gb_{h-g}b_{-h}
            +\mu\,\mathbf1_{g=0}\mathbf1_{h=0}.
 }
 \tag{31.1}
\]
Exactly one zero index gives \(-1/(\delta-1)\). At \((0,0)\), the
right-hand side is
\(-1/(\delta(\delta-1))+1-1/\delta=(\delta-2)/(\delta-1)\).
Rotation and Hermitian symmetry follow directly from the three factors.
Also
\[
 \sum_g|b_g|^2=n-1+1/\delta=\delta-1.
\]

For \(h\ne0\), let
\[
 f_h(m)=b_mb_{h-m}=b_m\overline{b_{m-h}},\qquad
 \widehat f_h(k)=\sum_{m=0}^{n-1}f_h(m)e^{-2\pi i km/n}.
\]
The quadratic Izumi equation becomes
\[
 \lambda^2\sum_m f_h(m+g)\overline{f_h(m)}=\mathbf1_{g=0}.
\]
Taking the discrete Fourier transform in \(g\) proves the equivalence
\[
 \boxed{
 |\widehat f_h(k)|^2=\frac{(\delta-1)^2}{\delta}
 \quad(h\ne0,\ k\in\mathbb Z_n).
 }
 \tag{Q}
\]
The entire \(h=0\) quadratic system holds automatically for the
exceptional column, using \(\delta^2=n\delta+1\).

Equivalently, the unit vector \(v=b/\sqrt{\delta-1}\) has a prescribed
discrete ambiguity function:
\[
 \left|\sum_m v_m\overline{v_{m-h}}e^{-2\pi i km/n}\right|^2
 =\begin{cases}
 1,&(h,k)=(0,0),\\
 \delta^{-2},&h=0,\ k\ne0,\\
 \delta^{-1},&h\ne0.
 \end{cases}
 \tag{31.2}
\]
The \(h=0,k\ne0\) overlap itself is \(-1/\delta\). This formulation
provides a concrete target for a character-sum or special-function
identity. The two nontrivial magnitudes differ, so this is not the
usual equal-overlap SIC condition.

Under the Stark construction, the natural phase target is
\[
 b_g^4=s_g\quad(g\ne0),
\]
with coherent root choices and the prescribed \(b_0\). Formula (31.1)
then gives (28.1) immediately. If a phase reconstruction initially
gives \(b_g^4=s_g\chi(g)\) for an additive character \(\chi\), its
unique fourth-root character removes \(\chi\) without changing the
generic entries, since \(n\) is odd.

**Remaining equation.** Let \(\mathcal A_{g,h}(b)\) denote the explicit
right-hand side of (31.1). Besides (Q), one must prove
\[
 \sum_m\mathcal A_{m,g+h}(b)
   \overline{\mathcal A_{m+k,g}(b)\mathcal A_{m+l,h}(b)}
 =\mathcal A_{g+l,k}(b)\mathcal A_{h+k,l}(b)
  -\delta^{-1}\mathbf1_{g=0}\mathbf1_{h=0}
 \tag{C}
\]
for all indices. Away from the explicit exceptional terms this is a
six-factor finite-sum identity in \(b\).
No implication from (Q) to (C) is proved here. They are verified
independently in Section 29. Neither the multiplicative cocycle law
nor Stark algebraicity by itself proves these additive identities.

[`hi_phase_reductions.py`](hi_phase_reductions.py) checks the rational
cocycle identities and binary sign ranks exactly, checks the Fourier
equivalence on arbitrary phases as well as a solution, and verifies
(Q) for the recorded \(n=13\) phases at 80-digit precision. Its
numerical checks supplement the derivation; the independent GP
certificates supply the finite existence proofs.

---

# 32. An unconditional infinite family of arithmetic inputs over one field

Restricting an infinitude strategy to primes \(p\) with
\(h(\mathbb Q(\sqrt{p^2+4}))=1\) would introduce a separate unproved
infinitude requirement. There is an explicit alternative if the target
is infinitely many **odd orders**, as in the present question.

Let
\[
 K=\mathbb Q(\sqrt5),\qquad \epsilon=(1+\sqrt5)/2,
 \qquad m>1,\quad m\equiv1,5\pmod6,
\]
and set
\[
 \delta_m=\epsilon^m,\qquad n_m=L_m=\epsilon^m-\epsilon^{-m}.
\]
Here \(L_m\) is the usual Lucas number for odd \(m\), and \(F_m\)
below is the Fibonacci number. Then
\[
 \delta_m^2-n_m\delta_m-1=0,\qquad
 n_m^2+4=5F_m^2.
\]
These give infinitely many distinct odd \(n_m\), all with \(K_{n_m}=K\).
No assertion that infinitely many of them are prime is needed.

## 32.1 Exact ray group and exact unit index

**Proposition.** Put \(\mathfrak a_m=(\epsilon^m-1)\). Then
\[
 \mathcal O_K/\mathfrak a_m\simeq\mathbb Z/n_m\mathbb Z,
\]
and the residue of \(\epsilon\) has exact order \(m\). Consequently
\[
 \boxed{
 \operatorname{Cl}_{\mathfrak a_m\infty_+}(K)
 \simeq(\mathbb Z/n_m\mathbb Z)^\times/\langle\bar\epsilon\rangle,
 \qquad
 [K^{\mathfrak a_m\infty_+}:K]=\frac{\varphi(n_m)}m.
 }
 \tag{32.1}
\]

**Proof.** The expansion
\(\epsilon^m=F_m\epsilon+F_{m-1}\) and the identity
\(n_m^2-5F_m^2=-4\) show \(\gcd(F_m,n_m)=1\), because \(n_m\)
is odd. Hence in the quotient
\[
 \bar\epsilon=(1-F_{m-1})F_m^{-1}\pmod{n_m}.
\]
The quotient has size \(|N(\epsilon^m-1)|=n_m\), proving the ring
isomorphism. Its unit order divides \(m\). If
\(0<r<m\) and \(\epsilon^r\equiv1\pmod{\mathfrak a_m}\), then
\(n_m\) divides \(N(\epsilon^r-1)\). For odd \(r\) this norm is
\(-L_r\); for even \(r\) it is \(2-L_r\). Its absolute value is
nonzero and strictly less than \(n_m\), a contradiction.

The field \(K\) has class number one: its Minkowski bound is
\(\sqrt5/2<2\). Its units are generated by \(-1\) and \(\epsilon\).
In the one-infinite-place ray exact sequence, \(-1\) removes the
sign factor and the remaining positive-unit image is generated by
\(\bar\epsilon\). This proves (32.1). ∎

The examples are reproduced by [`hi_pell_ray.gp`](hi_pell_ray.gp), with
results in [`hi_pell_ray_results.txt`](hi_pell_ray_results.txt).

| \(m\) | \(n_m\) | ray group | ray degree |
|---:|---:|---|---:|
| 5 | 11 | \(C_2\) | 2 |
| 7 | 29 | \(C_4\) | 4 |
| 11 | 199 | \(C_{18}\) | 18 |
| 13 | 521 | \(C_{40}\) | 40 |
| 17 | 3571 | \(C_{210}\) | 210 |
| 19 | 9349 | \(C_{492}\) | 492 |
| 23 | \(64079=139\cdot461\) | \(C_{1380}\times C_2\) | 2760 |
| 25 | \(167761=11\cdot101\cdot151\) | \(C_{300}\times C_{10}\times C_2\) | 6000 |

Only \(n=11,29\) in this table have the new HI certificates of
Section 29. The later rows are arithmetic computations, not claimed
categorifications.

## 32.2 A fixed maximal-order RM point and explicit characteristics

There is a necessary correction when specializing the analytic route
to this family:
\[
 [\mathcal O_K:\mathbb Z[\delta_m]]=F_m.
\]
Thus the lattice \(\mathbb Z+\mathbb Z(-\delta_m)\) used naively in
Section 23 is a nonmaximal order. It cannot silently be identified
with the maximal-order ray problem in (32.1).

Instead, use the fixed element \(\beta=-\epsilon\), viewed under the
nonphysical real embedding, so numerically
\(\beta=(\sqrt5-1)/2>0\). Its lattice
\(\mathbb Z+\mathbb Z\beta\) is \(\mathcal O_K\). Put
\[
 M_0=\begin{pmatrix}1&1\\1&2\end{pmatrix},\qquad M_m=M_0^m,
 \qquad
 \mathbf r_{m,u}=-\frac{u}{n_m}
 \binom{F_{m-1}+1}{F_m}.
 \tag{32.2}
\]
Then, exactly,
\[
 M_m\beta=\beta,\qquad j_{M_m}(\beta)=\delta_m^{-2}>1
 \quad\text{at the chosen embedding}.
\]
For odd \(m\), the Fibonacci identities give
\[
 M_m-I=n_m
 \begin{pmatrix}F_{m-1}&F_m\\F_m&F_{m+1}\end{pmatrix},
\]
so \(M_m\equiv I\pmod{n_m}\) and it stabilizes every displayed
characteristic. In the convention
\([[\mathbf r,\beta]]=r_2\beta-r_1\),
\[
 [[\mathbf r_{m,u},\beta]]
 =\frac{u(1+\delta_m)}{n_m}
 =\frac{u\delta_m}{\delta_m-1}.
\]
For \(u\) coprime to \(n_m\), its denominator ideal is precisely
\(\mathfrak a_m\). With the totally positive generator
\(\alpha=\delta_m(\delta_m-1)\), the numerator becomes
\[
 \alpha[[\mathbf r_{m,u},\beta]]=u\delta_m^2
 \equiv u\pmod{\mathfrak a_m}.
\]
This realizes the desired residue labels at **one fixed RM point**,
with stabilizer matrices that are powers of a single matrix.
It uses the RM/ray correspondence of
[Kopp, Sections 3 and 8](https://arxiv.org/html/2411.06763v2), but
the displayed specialization is derived here. This section does not
assert that the multiplier normalization from the \(p=17\) case
carries over unchanged.

When \(n_m\) is composite, the full HI matrix also needs nonunit
residue labels. These require the ray class monoid and values for
smaller conductors, as in Kopp's Proposition 6.11; the invertible ray
orbit alone supplies too few labels. The prime-only sign algorithm
also needs an extension to the gcd strata.

The subsequence \(m=5^k\), \(k\ge1\), even gives nested moduli,
since \(\epsilon^a-1\) divides \(\epsilon^{ab}-1\). It is therefore
a possible setting for a distribution argument. A distribution law
for units would still need a proof that it preserves (Q) and (C)
as the additive group changes size.

---

# 33. What an infinitude proof now needs

This records the target after the first continuation. Sections 34–37
sharpen it to one balanced identity and extend the sign theorem.

The work above proves finite existence and removes two general
obstacles: recovering higher ratio types and managing the numerous
root signs in prime order. It does not prove existence for infinitely
many \(n\).

A precise sufficient target is now available. For infinitely many
\(m\equiv1,5\pmod6\), construct physical phases \(b_g\),
\(g\in\mathbb Z_{L_m}\), with
\[
 b_0=-\delta_m^{-1/2},\qquad b_{-g}=\overline{b_g},\qquad
 |b_g|=1\ (g\ne0),
\]
and prove **(Q) and (C)** of Section 31. Formula (31.1) and the
Izumi construction then give the desired infinite family.

The candidate is to take coherent fourth roots of ray/monoid Stark
values at the explicit parameters (32.2). A proof through this
candidate must establish the following substantive points:

1. Define and normalize values for all required residues, including
   nonunits at composite \(L_m\), and produce the physical phases.
   If using the algebraic route, prove the necessary fourth-root lifts
   and sign compatibility; algebraicity of the Stark units alone is
   weaker than these requirements.
2. Prove the finite Fourier identity (Q) for those phases, uniformly
   in the chosen exponents \(m\).
3. Prove the cubic finite-sum identity (C), or prove a theorem that
   makes it follow from the particular construction and (Q).

These requirements are not supplied by the multiplicative
\(2-\operatorname{Frob}_{(2)}\) law, the usual Stark conjecture, or
class-field existence. They are the remaining analytic/algebraic
existence problem. In an analytic construction that directly produces
the physical phases and proves the two identities, prior Stark
algebraicity would not be necessary for existence.

The suggested next experiment, \(n=199\), is now complete in
Section 35.3. It stays over \(\mathbb Q(\sqrt5)\) with ray degree
18. The beta reduction and exact integer batches made its full cubic
verification feasible. This tests the fixed-field formula at a larger
order; an infinitude theorem still requires a uniform construction.


---

# 34. One balanced finite beta identity encodes the entire system

There is a uniform reduction beyond Section 31: **within its phase
ansatz, (Q) and (C) together are equivalent to a single balanced finite
beta identity**. This is an algebraic change of formulation, proved
below; it does not assert that arbitrary Stark values satisfy the identity.
It applies to every odd order, including composite orders.

Write \(d=\delta\), \(d^2=nd+1\), and retain
\[
 b_0=-d^{-1/2},\quad b_{-u}=\overline{b_u},\quad
 |b_u|=1\quad(u\ne0),\qquad
 \lambda=\frac{\sqrt d}{d-1},\quad \mu=\frac{d-1}{d}.
\]
All indices below lie in \(\mathbb Z_n\). For two triples
\(\mathbf a=(a_1,a_2,a_3)\), \(\mathbf c=(c_1,c_2,c_3)\)
satisfying \(\sum_i a_i+\sum_j c_j=0\), define
\[
 S(\mathbf a,\mathbf c)
 =\sum_m\prod_{i=1}^3 b_{m+a_i}\prod_{j=1}^3 b_{-m+c_j},
 \qquad
 P(\mathbf a,\mathbf c)=\prod_{i,j=1}^3 b_{a_i+c_j}.
\]
Put \(q=d^{-1}\), \([r]_q!=\prod_{s=1}^r(1+q+\cdots+q^{s-1})\),
and let \(m_x\) be the multiplicity of \(x\) in \(\mathbf a\).
The identity is
\[
 \boxed{\quad
 S(\mathbf a,\mathbf c)=\lambda^{-1}P(\mathbf a,\mathbf c)
 +\frac{(d-1)^3}{d^2}\,
  \mathbf1_{\{c_1,c_2,c_3\}=\{-a_1,-a_2,-a_3\}}
  \prod_x[m_x]_{1/d}! .\quad} \tag{34.1}
\]
The braces in the indicator denote **multisets**. Repeated entries
matter: the three possible correction factors are
\[
 1,\qquad 1+d^{-1},\qquad
 (1+d^{-1})(1+d^{-1}+d^{-2}),
\]
for multiplicities \(1+1+1\), \(2+1\), and \(3\), respectively.

A matrix in the exact certificates really has the required physical
phase form. To see this without numerical phase recognition, let
\(r_h=B_{1,h}/\sqrt d\), \(2\le h<n\), put \(z_0=z_1=1\),
and set \(z_h=\prod_{t=2}^h r_t\). The exact row norms give
\(|z_h|=1\), and the mirror row identity gives
\(z_gz_{n-g}=z_{n-1}\) for \(g\ne0\). Choose any unit-modulus
\(u\) with \(u^n=z_{n-1}\), and put \(b_g=u^g/z_g\) for
\(g\ne0\), with the prescribed exceptional \(b_0\).
Then \(b_{-g}=\overline{b_g}\). The checked prefix-product formula
for the upper triangle gives
\(B_{g,h}=\sqrt d\,b_gb_{h-g}b_{-h}\); Hermitian symmetry gives
the lower triangle. The exceptional entries supply (31.1) everywhere.
The choice of \(u\) changes the sequence only by a cyclic character.

## 34.1 Change of variables for the interior cubic equations

For \((g,h,k,l)\), set
\[
 \mathbf a=(0,k-g,l-h),\qquad
 \mathbf c=(g+h,-k,-l). \tag{34.2}
\]
Their cross-sum matrix is
\[
 (a_i+c_j)=
 \begin{pmatrix}
 g+h&-k&-l\\
 h+k&-g&k-g-l\\
 g+l&l-h-k&-h
 \end{pmatrix}. \tag{34.3}
\]
Conversely, shift \(a_i\mapsto a_i-a_1\),
\(c_j\mapsto c_j+a_1\), then set
\(k=-c_2\), \(l=-c_3\), \(g=-c_2-a_2\),
\(h=-c_3-a_3\). Thus (34.2) parametrizes every balanced pair,
up to a harmless reindexing of the sum.

If \(g,h,g+h\ne0\), substitute
\(A_{u,v}=\lambda b_u b_{v-u}b_{-v}+\mu\mathbf1_{u=v=0}\)
into (C). The three factors on its left have no origin correction.
After dividing its residual by
\(\lambda^3b_{-(g+h)}b_gb_h\), the result is precisely the
residual of (34.1).

Indeed, the two generic factors on its right give
\(\lambda^{-1}P\). An origin correction on the right occurs
only at \((k,l)=(0,-g)\) or \((-h,0)\). Each contributes
\(\mu/\lambda^2=(d-1)^3/d^2\) after division. These are
exactly the possible multiset matches when \(g,h,g+h\ne0\);
then all three entries of \(\mathbf a\) are distinct. To see the
last assertion directly, a matching permutation must avoid the three
nonzero cross entries corresponding to \(g,h,g+h\). Its only
possibilities are the two derangements. A repeated entry would give
a forbidden matching permutation as well.

In particular, when **all nine cross sums are nonzero**, the remaining
cubic equation has the simple form
\[
 \sum_m\prod_i b_{m+a_i}\prod_j b_{-m+c_j}
 =\frac{d-1}{\sqrt d}\prod_{i,j}b_{a_i+c_j}. \tag{34.4}
\]

## 34.2 Every collision case follows from (Q)

For a full multiset match, the three sums and product terms in (34.1)
are determined by norms alone. They are as follows.

| Multiplicity in \(\mathbf a\) | \(S\) | \(\lambda^{-1}P\) |
|---|---|---|
| \(1+1+1\) | \(n-3+3/d\) | \(-(d-1)/d^2\) |
| \(2+1\) | \(n-2+d^{-1}+d^{-2}\) | \(-(d-1)/d^3\) |
| \(3\) | \(n-1+d^{-3}\) | \(-(d-1)/d^5\) |

Subtracting the last column and using \(n=d-d^{-1}\) gives exactly
the three correction coefficients in (34.1).

For a collision without a full multiset match, permute the triples
so that \(a_1+c_1=0\). The corresponding pair of factors in the
summand is
\[
 b_{m+a_1}b_{-m-a_1}
 =1+(d^{-1}-1)\mathbf1_{m=-a_1}.
\]
The unrestricted sum of the other four factors is a quadratic
correlation. In fact, set \(H=a_2+c_2\), \(V=a_3+c_2\).
The balancing condition identifies that sum with
\[
 \sum_t b_t b_{H-t}b_{-t-V}b_{t+V-H}. \tag{34.5}
\]
This is exactly a correlation from (Q). Both relevant shifts are nonzero: if either
\(H\) or \(V\) vanishes, the remaining two pairs match, contrary
to the assumption. Hence (34.5) vanishes by (Q).

For clarity, one can instead normalize \(a_2=0\) and write the
remaining two triples as \((0,V-H)\) and \((H,-V)\).
Their four-factor sum is
\(\sum_t b_t b_{t+V-H}b_{-t+H}b_{-t-V}\),
which is exactly (34.5).
The surviving term of \(S\) is therefore
\[
 (d^{-1}-1)
 \prod_{i=2}^3b_{a_i-a_1}\prod_{j=2}^3b_{c_j+a_1}.
\]
The product \(P\) is \(b_0\) times these four boundary factors,
since its other four factors pair to
\(|b_H|^2|b_V|^2=1\). Finally
\(\lambda^{-1}b_0=d^{-1}-1\), proving (34.1) in this case.

Conversely, (34.1) implies every nontrivial quadratic correlation.
Given nonzero \(g,h\), take
\[
 \mathbf a=(t,0,g-h),\qquad \mathbf c=(-t,h,-g).
\]
There is a cross-zero pair but no full multiset match. The calculation
just made subtracts the exceptional term from (34.1) and leaves
\(\sum_m b_m b_{h-m}b_{-m-g}b_{m+g-h}=0\).
The zero-shift correlations follow from the norms and
\(d^2=nd+1\), and the \(h=0\) column of (Q) is automatic.
Thus the collision part of (34.1) recovers all of (Q).

## 34.3 The boundary cubic equations also follow from (Q)

Here are explicit reductions, including the exceptional origin.
Write \(c_0=(d-1)^{-1}\), so \(A_{u,0}=\mathbf1_{u=0}-c_0\).
For \(g=0\), \(h\ne0\), the left side of (C), using (Q), becomes
\[
 A_{-k,h}\overline{A_{l-k,h}}-c_0\mathbf1_{l=0}.
\]
For \(l\ne0\) this equals \(A_{l,k}A_{h+k,l}\) directly from
the phase formula and the unit norms at nonzero indices. For \(l=0\),
use \(|A_{u,h}|^2=\lambda^2\) when \(u\ne0,h\), and
\(|A_{u,h}|^2=c_0^2\) otherwise. The case \(h=0,g\ne0\)
follows by exchanging \((g,k)\) with \((h,l)\).

For \(h=-g\ne0\), the left side similarly reduces to
\[
 \overline{A_{k,g}}A_{-l,g}-c_0\mathbf1_{k=g+l}.
\]
If \(k\ne g+l\), the phase products equal the right side of (C).
If \(k=g+l\), the assertion reduces to the same two norm values;
use \(\lambda^2-c_0=c_0^2\).

For \(g=h=0\), the left side is
\[
 \mathbf1_{k=l=0}
 -c_0(\mathbf1_{k=0}+\mathbf1_{l=0}+\mathbf1_{k=l})
 +3c_0^2-nc_0^3.
\]
The right side is \(|A_{l,k}|^2-d^{-1}\). The cases
\(k=l=0\), exactly one of \(k=0,l=0,k=l\), and none of them
agree by \(d^2=nd+1\).

Combining these observations proves the equivalences
\[
 \boxed{\quad
 (Q)+(C)\quad\Longleftrightarrow\quad(34.1)
 \quad\Longleftrightarrow\quad(Q)+(34.4)
 \text{ for all cross-zero-free balanced pairs}.\quad}
\]
No implication from (Q) alone to (C) in arbitrary order is proved here.

## 34.4 Symmetry and exact verification

The two sides of (34.1) are invariant under independent permutations
of the triples, interchange of the triples, and opposite translation
of the triples. The first two operations form
\((S_3\times S_3)\rtimes C_2\), of order 72. For prime order,
checked multiplier covariance supplies the scalar action as well.
It is enough to check (C) at one representative of each resulting
orbit of cross-zero-free quadruples; all other equations follow by
the preceding proof. Scalar covariance also reduces (Q) to the
columns \(h=0,1\).

| Prime | Earlier cubic scalar representatives | New beta representatives |
|---|---:|---:|
| 7 | 401 | 6 |
| 11 | 1,465 | 17 |
| 13 | 2,381 | 30 |
| 17 | 5,221 | 63 |
| 19 | 7,241 | 91 |
| 29 | 25,261 | 320 |
| 199 | 7,920,401 | 108,406 |

At \(n=199\), this changes the cubic summand count from
1,576,159,799 to 21,572,794. These are exact enumeration counts,
not estimates of runtime. It remains a substantial computation.

`hi_beta_reductions.py` independently checks the orbit coverage,
the rational collision coefficients, the change of variables on
arbitrary nonsolutions at orders 3, 5, 7, 9, and every balanced
identity for the recorded order-13 solution. `hi_stark_seedless.gp`
uses the same proven reduction for exact number-field certificates.
The optional `HI_STARK_FULL_CUBIC=1` runs the older exhaustive scalar
check and the full quadratic check too; both methods agree exactly
at orders 7, 11, 13, 17, 29.


---

# 35. Exact ideal evidence and the next finite orders

## 35.1 Quadratic equations imply cubic equations at orders 3, 5, 7, 9

There is now an exact algebraic result supporting the possible
redundancy of (C), beyond the earlier numerical experiments. Put
\(c_g=\sqrt d\,b_g\), so that \(c_0=-1\) and
\(c_gc_{-g}=d\) for \(g\ne0\). Over
\(K=\mathbb Q(d)\), \(d^2=nd+1\), consider the ideal
\[
 I_n=\left(
 c_gc_{-g}-d,\quad
 \sum_m c_m c_{h-m}c_{-m-g}c_{m+g-h}
 \ \bigm|\ g,h\ne0\right)
 \subset K[c_1,\ldots,c_{n-1}]. \tag{35.1}
\]
The second set of generators is precisely the nontrivial part of (Q)
in these coordinates. For each balanced cross-zero-free pair, set
\[
 F_{\mathbf a,\mathbf c}
 =d^2\sum_m\prod_i c_{m+a_i}\prod_j c_{-m+c_j}
 -(d-1)\prod_{i,j}c_{a_i+c_j}. \tag{35.2}
\]
Here the bold \(\mathbf c\) denotes the second triple of indices,
whereas \(c_g\) denotes a variable. The different degrees, six and
nine, are intentional: clearing the phase normalization multiplies
(34.4) by \(d^5\).

`hi_quadratic_ideal.py` computes a reduced Gröbner basis in Singular
and verifies the actual ideal memberships
\[
 \boxed{F_{\mathbf a,\mathbf c}\in I_n\quad
 \text{for all such pairs when }n=3,5,7,9.}
\]
The ideal is invariant under scalar permutations of its variables.
Together with the exact beta symmetries, this makes the finite
representative checks exhaustive even without assuming Galois
covariance of an individual solution. Section 34 then proves
\((Q)\Rightarrow(C)\) for every phase solution at these four orders.
This is ideal membership, stronger than numerical vanishing or
membership merely in the radical.

| \(n\) | Reduced Gröbner basis size | \(\dim_K K[c_1,\ldots,c_{n-1}]/I_n\) | Beta representatives tested |
|---|---:|---:|---:|
| 3 | 3 | 6 | 1 |
| 5 | 14 | 20 | 2 |
| 7 | 41 | 42 | 6 |
| 9 | 132 | 108 | 14 |

The dimensions in this table count scheme length; reducedness or a
classification of physical solutions is not inferred from these
numbers. The same direct Gröbner computations at orders 11 and 13
reached a 300-second limit without completing. The later row-coordinate
certificate in Section 45 resolves order 11. The earlier timed-out runs establish no
implication at those orders. A **uniform proof of (35.2) lying in
(35.1)** would remove (C) as a separate requirement in the phase
ansatz. Existence of physical solutions of (Q) would still need proof.

## 35.2 The order-19 certificate is now complete

The earlier partial checkpoint in Section 29.4 has been completed.
The construction from the full ray Stark polynomial gives exact
fourth-root lifts, sign transport, every instance of (Q), all norm,
rotation and multiplier identities, and all of (C), the last by
91 balanced-beta representatives. The field has absolute degree 72
and ray group \(C_{18}\times C_2\).

Two further exact assertions identify the formerly recognized data.
If \(E_{19}\) is the degree-36 polynomial of Section 26, the matrix
satisfies
\[
 E_{19}(-B_{1,2}^2/d)=0.
\]
Its principal-orbit coefficient
\[
 \tau=\sum_{g=1}^{18} B_{g,2g}^2/d
\]
satisfies
\[
 \tau^2-(-333455+17502d)\tau+61207710-3212584d=0.
\]
These checks occur **after** the construction and use no numerical
HI seeds. The earlier exact irreducibility and Hilbert-class-field
computations therefore identify the full relative minimal polynomial
and its two branch factors without a phase-recognition assumption.
The other Hilbert-class conjugate of the matrix also satisfies every
equation: the ray Galois group is abelian, so its action commutes with
the verified physical conjugation and fixes \(d\).

The logs `hi_stark19_results.txt` record the exact initial field and
root stages, the completed matrix verification, and these downstream
polynomial assertions. The old partial log is retained as history.

## 35.3 The fixed-field experiment at order 199

For \(n=L_{11}=199\), the base field is \(\mathbb Q(\sqrt5)\),
the ray group is \(C_{18}\), and the absolute field degree is 36.
The exact construction has passed all field and physical-involution
checks, every fourth-root lift, sign transport of rank 98, every
quadratic equation, rotation, scalar covariance, and all generic
norms and fourth-power Stark identities. In particular, the
fixed-field candidate satisfies the complete Fourier identity (Q)
at this much larger order.

**All 108,406 cubic representatives have now passed exactly**, in
16 disjoint batches. Together with the preceding checks, this is a
complete existence certificate at order 199. The construction and
coverage logs are `hi_stark199_construction_results.txt` and
`hi_stark199_cubic_results.txt`.

The saved `hi_stark199_certificate.gp` contains 458 distinct entries
and their index matrix, plus the defining field and involutions.
`hi_stark19_certificate.gp` has the analogous data with 62 distinct
entries. These are exact rational expressions, with no phase seeds.
`hi_stark_verify_certificate.py` verifies the fields, physical
involutions, coherent phase form, symmetries and quadratic equations
directly from the saved data, then runs the cubic batches. For example:

```sh
python hi_stark_verify_certificate.py hi_stark199_certificate.gp --jobs 16
```

The `--structure-only` option stops before the separately required
cubic stage. It does not report a complete existence certificate.

The separate final-stage verifier `hi_stark_cubic_batches.py` clears
a common denominator \(D\) of \(B\) and \(d\). With
\(X=DB\) and \(Y=D(d-1)\), it checks the integer-polynomial
congruences
\[
 \sum_jX_{j,g+h}X_{g,j+k}X_{h,j+l}
 =Y X_{g+l,k}X_{h+k,l}\pmod{P}, \tag{35.3}
\]
where \(P\) is the monic absolute defining polynomial. Hermitian
symmetry converts conjugation to transposition. The representatives
are cross-zero-free, so the exceptional \(g=h=0\) term is absent.
All operations take place in \(\mathbb Z[y]/(P)\); there is no
floating-point tolerance or probabilistic modular test. Disjoint
batches together cover every representative, and the log records
the SHA-256 of the matrix checkpoint to identify their common input.
The previously completed field, phase-form, covariance and quadratic
checks remain essential parts of this certificate.

---

# 36. Sign descent at composite orders and a prime-power theorem

The prime-order sign argument extends to a useful general criterion.
Let \(G\) be a finite abelian group of odd order and let a finite
group \(H\) act on \(G\) and on the coefficient field. Write
\(\sigma_h\) for the field action. Assume a normalized symmetric
phase cocycle \(C\) has been constructed and that its covariance
errors
\[
 E_h(a,b)=\frac{\sigma_h(C(a,b))}{C(ha,hb)}
\]
lie in \(\{\pm1\}\). The fourth-power identities and the real
embedding argument of Section 30 give this hypothesis in the prime
construction; it must be checked for a proposed composite
construction. Also assume \(-1\in H\) acts as physical conjugation,
so \(E_{-1}=1\).

Define
\[
 f_h(a)=E_h(a/2,a/2).
\]
The normalized sign-valued cocycle calculation gives, uniquely,
\[
 E_h(a,b)=\frac{f_h(a)f_h(b)}{f_h(a+b)},\qquad
 f_{hk}(a)=f_h(ka)f_k(a). \tag{36.1}
\]
Uniqueness uses the absence of nontrivial homomorphisms
\(G\to\{\pm1\}\). For \(a\in G\), let
\(H_a=\{h:ha=a\}\). Then
\[
 \chi_a:H_a\longrightarrow\{\pm1\},\qquad
 \chi_a(h)=f_h(a),
\]
is a character.

**Sign descent criterion.** A correction
\(C'(a,b)=C(a,b)t_at_b/t_{a+b}\), \(t_0=1\),
\(t_a\in\{\pm1\}\), with exact \(H\)-covariance exists if
and only if every \(\chi_a\) is trivial. When it exists, the
remaining freedom is one sign per nonzero \(H\)-orbit in \(G\).
The correction respects \(t_{-a}=t_a\).

To prove the criterion, exact covariance is equivalent, by uniqueness
in (36.1), to
\[
 t_{ha}=f_h(a)t_a. \tag{36.2}
\]
For \(h\in H_a\) this requires \(\chi_a(h)=1\). Conversely,
choose one sign at a representative of each orbit and extend by
(36.2). The cocycle identity makes this well-defined precisely when
the stabilizer characters vanish. Finally \(f_{-1}=1\) gives the
negation condition. Two choices differ by an orbit-constant sign
function. Distinct such functions give distinct corrected cocycles,
because their quotient cannot be a nontrivial sign character of the
odd group \(G\).

**Prime-power corollary.** For
\(G=\mathbb Z_{p^k}\), \(p\) odd, and
\(H=(\mathbb Z/p^k)^\times\), all stabilizers of nonzero
elements have odd order. An element of additive order \(p^j\)
has stabilizer of order \(p^{k-j}\), the kernel of reduction to
\((\mathbb Z/p^j)^\times\). Thus every stabilizer character is
trivial, and the sign correction always exists under the stated
phase and covariance-error hypotheses. There are exactly \(k\)
remaining orbit signs, one for each additive order
\(p,p^2,\ldots,p^k\), giving \(2^k\) choices before imposing (Q).
This removes a sign obstruction uniformly on an infinite family of
candidate orders. It does not supply their fourth-root lifts or (Q).

For general odd cyclic \(n\), the number of nonzero scalar orbits
is \(\tau(n)-1\), but their stabilizers can have even order. Their
characters cannot simply be ignored. The script
`hi_composite_signs.py` checks the prime-power orbit counts and
constructs an abstract example at \(n=15\) with
\(f_{-1}=1\), yet \(\chi_3(11)=-1\). This is an example of
sign-error data, not a claimed HI or Stark counterexample.

There is a concrete class-field sufficient condition for general
\(n\). If \(a\) has additive order \(q\), require its diagonal
fourth-root lift \(B_{a/2,a}\) to lie in the field fixed by
\(\sigma_h\) for every \(h\equiv1\pmod q\). Then
\[
 f_h(a)=\sigma_h(B_{a/2,a})/B_{a/2,a}=1
 \quad(h\in H_a),
\]
and the obstruction vanishes. In a ray-monoid construction this is
the expected lower-conductor field condition on the **root lift**;
having only its fourth power in that field is insufficient. Once
these lower-conductor lifts and the global phase cocycle are
constructed, there is no further composite sign compatibility
problem beyond the orbit signs.

---

# 37. The sharpened infinitude target

The strongest uniform target from this continuation is now explicit:
construct, for infinitely many odd orders, the physical sequence of
Section 34 and prove **the single balanced identity (34.1)**. That
identity includes unitarity through its collision cases and gives the
remaining Izumi equations through its cross-zero-free cases. This
would be an existence proof without needing prior Stark algebraicity.

There are two concrete arithmetic settings. The fixed-field Lucas
family of Section 32 supplies explicit RM characteristics and ray
moduli; its composite labels require lower-conductor root control as
in Sections 36 and 38. Alternatively, the orders \(p^k\) are already an
unconditional infinite sequence, and Section 36 makes sign descent
automatic once the phase/root hypotheses hold. For that route the
quadratic fields vary with \(k\), and the phase construction and
finite identities remain unproved. Neither setting requires an
unproved infinitude of special primes.

The beta reformulation suggests a more specific analytic comparison
than the general appeal to quantum dilogarithms. The integral
identity (1.11) in
[Bazhanov–Sergeev, *A distant descendant of the six-vertex model*](https://arxiv.org/html/2310.08427v2#S1.E11)
has three numerator and three denominator factors, a balancing
condition, and nine pairwise factors on the other side. The authors
relate it to the constant beta pentagon identity of Garoufalidis and
Kashaev. Our finite identity has a comparable pattern after using
\(b_{-x}=b_x^{-1}\) at nonzero indices. This comparison is a
research direction, not a specialization theorem.

A successful specialization would have to establish the finite
\(\mathbb Z_n\) sum, the normalization \((d-1)/\sqrt d\), and
all three collision coefficients in (34.1). The continuous integral
in that paper does not by itself provide them. The explicit fixed-RM
characteristics from Section 32 are candidates for such a descent;
no descent or limiting argument accomplishing it has been proved
here.

A second precise route is to prove the uniform ideal containment
(35.2) in (35.1), then construct physical solutions of (Q) uniformly.
The small-order containments and the larger exact Stark-derived
quadratic solutions support this approach, but they do not replace
those two required theorems. Existence for infinitely many \(n\)
remains open in these notes.


---

# 38. All fourth-root lifts collapse to one Kummer root

There is a stronger simplification of Sections 28, 30 and 36. The
many row-root computations can be replaced by **one fourth-root
condition**, followed by Galois transport and, at prime powers,
odd-degree norms. This does not assert the remaining sum identities.

## 38.1 An explicit inverse to the doubling-root map

Let \(L\) be the ray field, let \(\alpha=\sigma_2\) be its
residue-2 automorphism, and suppose \(\alpha(d)=d\). Then the two
root problems
\[
 D^4=d^2\frac{s^2}{\alpha(s)}
 \qquad\text{and}\qquad
 W^4=d^2s \tag{38.1}
\]
are equivalent **inside the same field \(L\)**. The mutually inverse
maps are
\[
 \boxed{\quad D=\frac{W^2}{\alpha(W)},\qquad
 W=\frac{d^2\alpha^{-2}(s)}
          {\alpha^{-2}(D)^2\alpha^{-1}(D)}.\quad} \tag{38.2}
\]
For example, raising the second expression to the fourth power and
using the first equation in (38.1) gives \(d^2s\); substituting it
into \(W^2/\alpha(W)\) returns \(D\) exactly. No extraction of
additional roots occurs in this inverse formula.

Thus even the single known doubling root \(B_{1,2}\) already gives
a fourth root of \(d^2s\). The apparently weaker doubling quotient
condition is not weaker at the level of fourth-root existence.
This is an algebraic equivalence, without any Stark conjecture.

For prime order, define \(W_a=\sigma_a(W)\) for \(a\ne0\).
At a physical embedding, \(\overline s=s^{-1}\) gives
\((W\overline W)^4=d^4\). Positivity of \(W\overline W\)
therefore forces \(W\overline W=d\). Consequently
\[
 b_0=-d^{-1/2},\qquad b_a=W_a/\sqrt d\quad(a\ne0)
\]
has the required physical norms and negation symmetry, and
\[
 \boxed{B_{g,h}=\frac{W_gW_{h-g}}{W_h}
 \quad(g,h,h-g\ne0).} \tag{38.3}
\]
The exceptional entries are prescribed as before. Every generic
fourth-power formula, rotation symmetry, Hermitian symmetry and
scalar covariance now follows directly. Since \(L\) has a real
embedding, a solvable fourth-root problem has exactly two roots in
\(L\); these give the two global generic sign choices. No separate
row-sign linear system is necessary for this construction.

The formula also recovers an already certified matrix, not just some
matrix with the same fourth powers. Write \(D_a=B_{a,2a}\). Then
\[
 W_a=\frac{d^2s_{a/4}}{D_{a/4}^{\,2}D_{a/2}},
 \qquad W_a^4=d^2s_a,\qquad W_a^2/W_{2a}=D_a.
\]
The quotient of the two normalized phase cocycles has values in
\(\{\pm1\}\) and trivial diagonal, hence is identically one by
the odd-order sign-cocycle lemma. Direct exact computation confirms
(38.3) for every generic entry of both saved matrices at orders
19 and 199. In this gauge the phase values themselves satisfy
\(b_a^4=s_a\); the cyclic-character ambiguity of the prefix-product
construction has been removed.

## 38.2 Odd-degree norm descent of the root

Let \(L/M\) have odd degree \(r\), with \(d\in M\), and suppose
\(N_{L/M}(s_L)=s_M\). If \(W_L^4=d^2s_L\), set
\[
 \boxed{\quad W_M=d^{(1-r)/2}N_{L/M}(W_L).\quad} \tag{38.4}
\]
Then
\[
 W_M^4=d^{2(1-r)}d^{2r}s_M=d^2s_M.
\]
If physical conjugation commutes with the norm and
\(W_L\overline W_L=d\), it also gives
\(W_M\overline W_M=d\). The exponent in (38.4) is an integer;
this is why odd degree removes the apparent extra root extraction.

For \(n=p^k\), \(p\) odd, write
\((d-1)=\mathfrak p^k\) in the maximal quadratic order. The prime
\(p\) splits since \(n^2+4\equiv4\pmod p\). The ray extensions
from conductor \(\mathfrak p^k\) to
\(\mathfrak p^j\), with the same infinite place, have degree a
power of \(p\). Thus (38.4) applies whenever the distinguished
units have the required norm compatibility. One top-level Kummer
root then supplies roots in every smaller nontrivial conductor.
There are initially up to \(2^k\) stratum signs in the phase ansatz.
Section 40 makes one necessary quadratic equation linear in transformed
signs; imposing the exact norm law leaves only a global sign.

## 38.3 Nonunit labels need their remaining numerator ideal

The lower-conductor values must be assigned to the correct ray-monoid
class. They cannot simply be copied from the identity class at the
smaller conductor. For \(g=p^j u\), \(p\nmid u\), cancelling
\(\mathfrak p^j\) from the numerator ideal gives
\[
 (g)\mathfrak p^{-j}=(u)\overline{\mathfrak p}^{\,j}.
\]
Therefore the label at additive order \(p^{k-j}\) includes the
Artin action of \(\overline{\mathfrak p}^{\,j}\). In compatible
normalizations, the intended formula is
\[
 s_{p^j u}
 =\sigma_u\sigma_{\overline{\mathfrak p}}^{\,j}
    (s_{k-j}),\qquad
 W_{p^j u}
 =\sigma_u\sigma_{\overline{\mathfrak p}}^{\,j}
    (W_{k-j}). \tag{38.5}
\]
Here \(s_{k-j}\) and \(W_{k-j}\) are the lower-conductor unit and
root obtained before applying that class label. The ideal calculation
is the specialization of the conductor-reduction formula in
[Kopp, Proposition 6.11, equation (6.35)](https://arxiv.org/html/2411.06763v2#S6.E35).
Its norm factor contributes no derivative correction because the
differenced zeta function vanishes at zero. The assertion identifying
canonical analytic values with algebraic Stark units remains subject
to the hypotheses stated in that proposition.

The need for this numerator ideal is visible at \(n=25\). Over
\(\mathbb Q(\sqrt{629})\), the ray groups at
\(\mathfrak p^2\) and \(\mathfrak p\) are \(C_{40}\) and
\(C_8\). The exact degree-five norm of the full Stark generator
is a root of the lower-conductor Stark polynomial. Its untwisted
cochain gives all quartic lifts and physical norms, but **none of its
four stratum-sign choices satisfies (Q)**. This rules out that
untwisted assignment; it does not rule out order-25 existence.

For the corrected assignment, the conjugate-prime Artin map can be
identified exactly without reducing a poorly conditioned power basis
at the ramified rational prime. An auxiliary prime above 23 has base
root \(d\equiv6\pmod{23}\), and its ray coordinate is 29 in
\(C_{40}\), while that of \(\overline{\mathfrak p}\) is 33.
The auxiliary Frobenius is identified modulo a squarefree factor of
\(P\bmod23\), and its \(33/29\bmod40\) power gives the desired
map. Its square is exactly the rational-2 Frobenius, as also follows
from the positive generator
\((d+1)/d\) of \(\overline{\mathfrak p}^{\,2}\), which is
congruent to 2 modulo \(\mathfrak p^2\).

## 38.4 A more economical sufficient target for prime powers

For a fixed odd prime \(p\), an infinitude proof along \(p^k\)
can now be organized around the following substantive assertions:

1. Construct compatible ray units with the physical involution and
   the same-support norm law across the nontrivial conductors.
2. Prove just **one** Kummer condition \(d_k^2s_k\in L_k^{\times4}\)
   at the top conductor. Equations (38.4)–(38.5) then produce all
   nonzero residue phases with their correct class labels.
3. Prove the balanced identity (34.1) for some choice of stratum
  signs, uniformly for infinitely many \(k\).

Section 40 replaces the sign search in the third item by a rational
linear system. If the roots are required to obey (38.4), only one
global sign remains, and one necessary quadratic equation uniquely
selects it whenever it can be selected at all.

The quadratic base field varies with \(k\). Class-field existence,
Stark algebraicity, and the norm formulas do not establish the last
two assertions. Nevertheless, this removes the separate collection
of mixed-index fourth-root problems and turns lower-conductor sign
compatibility into an explicit construction.


---

# 39. Complete exact existence at the composite order 25

The corrected construction of Section 38 passes **every** Izumi
equation at \(n=25\). It uses no numerical HI seed. The arithmetic
data are
\[
 K=\mathbb Q(\sqrt{629}),\quad h_K=2,\quad
 \operatorname{Gal}(L/K)=C_{40},\quad [L:\mathbb Q]=80,
\]
with lower ray group \(C_8\) and relative conductor-descent degree
five. One exact root \(W^4=d^2s\), its normalized norm
\(d^{-2}N(W)\), and the conjugate-prime Artin twist produce the
cochain on both nonzero residue strata. The untwisted assignment
fails (Q), while the corrected one passes it.

The independently verified coefficient artifact is
`hi_stark25_certificate.gp`, with SHA-256
```text
e19474b7d332a306ab2d13009d526a7bd484011bdbeeb7fa77eef7d10d73477b
```
It contains exact rational coefficients in a degree-80 number field.
The verifier checks the field and physical involution, every matrix
norm, the full coherent phase form, Hermitian and rotation symmetries,
scalar covariance, and all quadratic equations. For the last check,
the columns \(h=0,1,5\) cover all scalar strata.

The cubic enumeration for composite orders uses actual unit-group
orbits; it never normalizes an index by division by a nonunit.
There are 267,720 cross-zero-free quadruples and 246 representatives
under the balanced-beta symmetries. All 246 exact cubic checks pass
in eight disjoint batches. Section 34 covers every remaining cubic
equation. The complete log is `hi_stark25_verification_results.txt`.

To verify the saved artifact without rerunning Stark computations:
```sh
python hi_stark_verify_certificate.py hi_stark25_certificate.gp --jobs 8
```
To reproduce the construction in a fresh temporary directory:
```sh
hi_work=$(mktemp -d /tmp/hi25_reproduce.XXXXXX)
export HI_STARK_LIBRARY=1
export HI_STARK_CHECKPOINT="$hi_work/rows.bin"
export HI_SINGLE_ROW_CHECKPOINT="$HI_STARK_CHECKPOINT"
export HI_SINGLE_CONJUGATE_FROBENIUS="$hi_work/conjugate_prime.bin"
export HI_SINGLE_OUTPUT="$hi_work/certificate.gp"
gp -q -f hi_stark_seedless.gp hi_stark_prime_power.gp
gp -q -f hi_stark_seedless.gp hi_stark25_artin.gp
gp -q -f hi_stark_seedless.gp hi_stark_single_root.gp
python hi_stark_verify_certificate.py "$HI_SINGLE_OUTPUT" --jobs 8
```
The first three stages are construction stages; only the last command
certifies all equations. `hi_stark25_artin.gp` deliberately implements
the exact cyclic ray-group calculation for this order, without claiming
to handle every prime power. The single-root and sign formulas are
uniform. This is a finite existence theorem, not an induction step
from order 5 to order 25: the dimension and quadratic base field differ.


---

# 40. Prime-power sign selection becomes rational linear algebra

There is a further uniform reduction of the apparent \(2^k\) sign
search. Let \(n=p^k\), with \(p\) odd, and suppose a physical
cochain and its phase matrix \(B\) have already been constructed.
No quadratic or cubic equation is assumed. Changing the sign of
\(W_a\) on the valuation stratum \(v_p(a)=j\) multiplies it by
\(\epsilon_j\in\{\pm1\}\), for \(0\le j<k\).

## 40.1 One necessary quadratic equation is linear in new signs

Set
\[
 D=B_{1,2},\qquad T=D+\overline D,\qquad
 R_m=B_{m+1,1}B_{1,m}\quad(2\le m\le n-2).
\]
Partition the generic terms by
\(j=v_p(m^2-1)\), and define
\[
 C_0=1+\sum_{\substack{2\le m\le n-2\\p\nmid m^2-1}}R_m,
 \qquad
 C_j=\sum_{\substack{2\le m\le n-2\\v_p(m^2-1)=j}}R_m
 \quad(1\le j<k).
\]
The valuations in these sums are less than \(k\): the only square
roots of 1 modulo an odd prime power are \(\pm1\), and those
indices have been excluded. For the sign-changed matrix, the single
quadratic equation with \(g=h=1\) is exactly
\[
 \boxed{C_0-\epsilon_0T+
       \sum_{j=1}^{k-1}\epsilon_0\epsilon_jC_j=0.} \tag{40.1}
\]

Here is the sign calculation. The \(m=0\) term is 1. The two
terms at \(m=1,-1\) sum to \(-\epsilon_0T\). In every other
term, the cochain signs occur as
\(\epsilon_{v_p(m)}^2
  \epsilon_{v_p(m-1)}\epsilon_{v_p(m+1)}\).
If \(p\mid m\), both neighbors are units and this product is 1.
If \(m,m-1,m+1\) are all units it is again 1. Otherwise exactly
one neighbor has positive valuation \(j\), giving
\(\epsilon_0\epsilon_j\). Oddness of \(p\) is essential here.

The substitution
\[
 y_0=\epsilon_0,\qquad y_j=\epsilon_0\epsilon_j\ (j>0)
\]
is a bijection of the sign cube, with inverse
\(\epsilon_0=y_0\), \(\epsilon_j=y_0y_j\). Expanding (40.1)
in any rational basis of the coefficient field gives the exact
linear system
\[
 \boxed{\quad [-T\ C_1\ \cdots\ C_{k-1}]\,y=-C_0,
           \qquad y_j\in\{\pm1\}.\quad} \tag{40.2}
\]
If the \(k\) coefficient columns are rationally independent,
there is at most one sign choice even for this one necessary
equation. Solve the rational system and check that all coordinates
are signs. An inconsistent system, or a unique solution with a
coordinate other than \(\pm1\), rejects every stratum-sign choice
for the proposed roots. In deficient rank, intersect the rational
affine solution space with the sign cube before testing the other
quadratic equations.

For the saved order-25 matrix, the rational rank is exactly two and
the unique solution is \(y=(1,1)\). Directly testing the other
three stratum-sign choices independently confirms that **each fails
already at \(g=h=1\)**. The routine
`hi_prime_power_sign_candidates` implements (40.2); the one-root
constructor now uses it before the full quadratic check. Full rank
for all prime powers has not been proved, and this one equation
does not replace the remaining quadratic or cubic equations.

## 40.2 Exact norm compatibility leaves only a global sign

Under the norm hypotheses of Section 38, requiring the roots
themselves to satisfy (38.4) is stronger than independently choosing
a root on each stratum. If two compatible choices differ by signs
\(\eta_r\) at conductor level \(r\), an odd-degree norm gives
\(\eta_{r-1}=\eta_r^{[L_r:L_{r-1}]}=\eta_r\).
The Artin twists fix signs. Thus **all norm-compatible root choices
differ by one global sign**. This uses that the fields have a real
embedding, so their fourth roots of unity are only \(\pm1\).
It does not assert that every solution of (Q) must obey these norm laws.

Put \(U=C_0+\sum_{j>0}C_j\). For a global change
\(\epsilon_j=\eta\), equation (40.1) becomes
\[
 U=\eta T. \tag{40.3}
\]
For the Stark construction, \(T\ne0\) whenever \(s\ne1\).
Indeed, \(T=0\) and \(D\overline D=d\) would imply
\(D^2=-d\), hence \(D^4=d^2\). The doubling formula then gives
\(\alpha(s)=s^2\), where \(\alpha=\sigma_2\). If \(\alpha\)
has order \(r\), this forces \(s^{2^r-1}=1\). A field with a
real embedding has only the roots of unity \(\pm1\), so the odd
exponent forces \(s=1\), a contradiction.

Consequently the necessary and sufficient condition that one of
the two global choices satisfy this single quadratic equation is
\[
 U^2=T^2,
\]
and its sign is then determined algebraically by \(\eta=U/T\).
The selected cochain \((U/T)W\) is unchanged if the initially
extracted fourth root is replaced by its negative. There is no
remaining global choice after this equation is imposed.

The saved matrices at orders 19, 199 and 25 pass exact reconstruction
from the single root and the test \(U=T\ne0\). At order 25 the
reconstructed nonunit root is exactly
\(d^{-2}\sigma_{\overline{\mathfrak p}}N(W)\), with no additional
relative sign. `hi_single_root_checks.gp` reproduces these assertions;
`hi_prime_power_signs.py` separately checks (40.1) on arbitrary
phases and all sign choices at several prime powers.

The prime-power route to infinitude now has an explicit sign procedure.
What remains is a uniform source of the top Kummer root and a proof
of the balanced identity for the selected phases, or a construction
of physical quadratic solutions together with a uniform proof that
(Q) implies (C). Neither finite rank tests nor norm compatibility
establish those missing statements.


---

# 41. A weighted-design formulation and an obstruction to Alltop deformation

The quadratic system has a uniform formulation in finite-dimensional
frame theory. This gives another possible route to constructing its
physical solutions, independent of Stark algebraicity. It also permits
a rigorous test of a tempting deformation argument.

## 41.1 The Weyl orbit plus one basis is a weighted 2-design

First allow a variable exceptional amplitude:
\[
 b_0=-t,\qquad |b_j|=1\ (j\ne0),\qquad b_{-j}=\overline{b_j},
 \qquad t>0.
\]
Set \(u=t^2\), \(s=n-1+u\), and \(v=b/\sqrt s\).
Consider the zero-correlation equations
\[
 \sum_m b_m b_{h-m}b_{-m-g}b_{m+g-h}=0
 \quad(g,h\ne0). \tag{41.1}
\]
At \(t=d^{-1/2}\), these are exactly the nontrivial equations (Q).
Define
\[
 a=\frac{(u-1)^2}{s^2},\qquad
 \beta=\frac{n-2+2u}{s^2},\qquad w=n(\beta-a).
\]
The identity \(a+n\beta=1\) holds for every \(u\).

Let \(X,Z\) be the cyclic shift and modulation on \(\mathbb C^n\),
with \(Ze_j=e^{2\pi ij/n}e_j\), and put
\[
 P_{h,k}=|X^hZ^kv\rangle\langle X^hZ^kv|,
 \qquad E_j=|e_j\rangle\langle e_j|.
\]
Then (41.1) is equivalent to the tensor identity
\[
 \boxed{\quad
 \sum_{h,k}P_{h,k}\otimes P_{h,k}
   +w\sum_j E_j\otimes E_j
  =n\beta\,(I+\mathsf{Swap}).\quad} \tag{41.2}
\]
When \(w>0\), this says that the Weyl orbit, with weight 1 per
vector, together with the coordinate basis, with weight \(w\) per
vector, forms a weighted complex projective 2-design. The weights
in (41.2) are not normalized to sum to 1. Weighted 2-designs and their
relation to mutually unbiased bases are discussed in
[Roy–Scott, *Weighted complex projective 2-designs from bases*](https://arxiv.org/abs/quant-ph/0703025).

**Proof.** The norm pattern gives squared Weyl overlaps 1 at the
identity and \(a\) at every nonidentity diagonal Weyl operator.
Fourier transforming (41.1) gives squared overlap \(\beta\) for
each Weyl operator with nonzero shift, and conversely. The frame
operator
\[
 \mathcal F(Y)=\sum_{h,k}\operatorname{tr}(P_{h,k}Y)P_{h,k}
\]
is diagonal on the orthogonal Weyl basis of matrices, with eigenvalues
\(n\), \(na\), and \(n\beta\) on the identity, traceless
diagonal matrices, and off-diagonal Weyl operators, respectively.
The coordinate-basis frame operator is diagonal projection. Adding
\(w\) times this projection gives
\[
 \mathcal F(Y)+w\operatorname{diag}(Y)
   =n\beta\bigl(Y+\operatorname{tr}(Y)I\bigr),
\]
since \(n+w=n(n+1)\beta\). Writing this equality in matrix
entries gives (41.2). Each step is reversible. ∎

At the HI amplitude, \(s=d-1\), \(a=d^{-2}\),
\(\beta=d^{-1}\), and
\[
 \boxed{w=\frac{n(d-1)}{d^2},\qquad
 \sum_{h,k}P_{h,k}^{\otimes2}+w\sum_jE_j^{\otimes2}
       =\frac nd(I+\mathsf{Swap}).} \tag{41.3}
\]
Thus constructing these particular weighted designs would solve (Q).
A general weighted-design existence theorem is insufficient: the
single cyclic Weyl orbit and the exceptional coordinate amplitudes
are essential restrictions. Equation (41.3) does not establish (C).

## 41.2 Explicit Alltop solutions occur at the wrong amplitude

For a prime \(p\ge5\), write \(\zeta=e^{2\pi i/p}\) and choose
\(c\in\mathbb F_p^\times\). The sequence
\[
 b_m=-\zeta^{c m^3}
\]
satisfies (41.1) at \(t=1\), since its summand is
\[
 \zeta^{-3cgh(g-h+2m)}
\]
and its nonconstant character sums to zero. Here \(w=1\), and
the design is the familiar Alltop construction from mutually unbiased
bases; see [Blanchfield, *Orbits of mutually unbiased bases*](https://arxiv.org/abs/1310.4684).
The required HI amplitude is \(t=d^{-1/2}<1\).

**Rigidity theorem.** For every prime \(p\ge5\), each of these
Alltop solutions is an isolated solution of (41.1) in the enlarged
real phase space in which \(t\) may vary and
\(b_{-m}=\overline{b_m}\) is retained. In particular, a continuous
deformation within this space cannot start at an Alltop solution and
reach the HI amplitude.

**Proof.** Write a first-order variation as
\[
 \dot b_m=i\theta_m b_m\quad(m\ne0),\qquad
 \theta_{-m}=-\theta_m,\quad\theta_0=0,\qquad
 \dot b_0=-\dot t.
\]
Let \(F_\ell=\sum_m\theta_m\zeta^{\ell m}\). For a nonzero
pair \(g,h\), put
\[
 \ell=-6cgh,\quad A=\zeta^{-3cgh(g-h)},\quad
 R=\zeta^{\ell h},\quad S=\zeta^{-\ell g}.
\]
Differentiating the corresponding equation (41.1) gives exactly
\[
 \dot Q_{g,h}=A\left(i(1-R)(1-S)F_\ell
                         +(1+R)(1+S)\dot t\right). \tag{41.4}
\]
The four origin contributions are counted with multiplicity when
two origins coincide. All factors \(1-R\) and \(1-S\) are nonzero.

Suppose the full differential vanishes and \(\dot t\ne0\).
Fix \(gh=1\), hence \(\ell=-6c\). Equation (41.4) would require
\[
 \frac{1+\zeta^{\ell h}}{1-\zeta^{\ell h}}
 \frac{1+\zeta^{-\ell g}}{1-\zeta^{-\ell g}}
\]
to be independent of the choice of \((g,h)\). This is an equality
in \(\mathbb Q(\zeta)\). Applying the automorphism
\(\zeta\mapsto\zeta^{\ell^{-1}}\), and comparing
\((g,h)=(1,1)\) with \((2,2^{-1})\), would give
\[
 \cot^2(\pi/p)=\cot(2\pi/p)\cot(\pi\,[2^{-1}]_p/p).
\]
This is impossible in absolute value: for residues other than
\(\pm1\), the absolute cotangent is strictly smaller than
\(\cot(\pi/p)\), and both 2 and \(2^{-1}\) are such residues
when \(p\ge5\). Hence \(\dot t=0\).

Every nonzero \(\ell\) occurs as \(-6cgh\), so (41.4) now
forces \(F_\ell=0\) for every \(\ell\ne0\). Oddness gives
\(F_0=0\), and Fourier inversion yields \(\theta_m=0\).
The real Jacobian therefore has full column rank. Selecting an
invertible square minor and applying the inverse function theorem
proves local isolation, not merely absence of one chosen tangent. ∎

`hi_design_alltop.py` checks the weight identities symbolically,
the cotangent obstruction by exact reduction modulo cyclotomic
polynomials, and the differential formula on arbitrary variations.
It also checks (41.2) directly as a tensor equation for Alltop examples
and for the recorded HI solution at order 13. These computations
support the displayed proofs; they do not assert infinitude.

The design formulation remains available as a construction target.
The rigidity theorem rules out one specific way of reaching it:
locally varying the exceptional amplitude of a cubic Alltop sequence
while preserving all quadratic correlations.



# 42. Exact amplitude branches at orders 5 and 7

The varying-amplitude system in Section 41 also permits an exact algebraic
comparison of three different design problems. This comparison does not
assume the HI value of the amplitude at the outset.

Work in the polynomial ring
\[
 R_n=\mathbb Q[x_1,\ldots,x_{n-1},v,t],\qquad
 b_0=-t,\quad b_j=x_j\ (j\ne0),
\]
and impose
\[
 I_n=\left(x_jx_{-j}-1,\quad vt-1,\quad
 \sum_m b_m b_{h-m}b_{-m-g}b_{m+g-h}\ (g,h\ne0)\right).
 \tag{42.1}
\]
The variable \(v\) excludes zero amplitude. This is a complex algebraic
scheme: the equations \(x_jx_{-j}=1\) do not by themselves require
\(x_{-j}=\overline{x_j}\). Physical points are the points with that
additional conjugation condition and \(t>0\).

**Exact elimination certificates.** Singular's rational-arithmetic
`std` calculation, followed by elimination, gives
\[
 \boxed{I_5\cap\mathbb Q[t]
 =\big((t^2-1)(t^4+5t^2-1)\big),} \tag{42.2}
\]
\[
 \boxed{I_7\cap\mathbb Q[t]
 =\big((t^2-1)(t^4+7t^2-1)(t^4-4t^2-4)\big).} \tag{42.3}
\]
Both quotient rings are zero-dimensional. The complete scheme lengths
and the lengths after adjoining each indicated factor are:

| Order | Total | \(t^2-1\) | \(t^4+nt^2-1\) | \(t^4-4t^2-(n-3)\) |
| --- | ---: | ---: | ---: | ---: |
| 5 | 120 | 40 | 80 | 0 |
| 7 | 308 | 84 | 168 | 56 |

These are scheme lengths over \(\mathbb Q\), including every algebraic
amplitude conjugate. They are not counts of physical solutions. The
coprime factors give disjoint algebraic branches, and their lengths
sum to the full length. In particular, the HI factor represents an
actual nonempty component in both calculations, rather than merely
an annihilating polynomial which could have extraneous factors.

To interpret the three factors, set \(u=t^2\):

- \(u=1\) is the flat Alltop amplitude.
- \(u^2+nu-1=0\) has the unique positive root \(u=1/d\), the HI
  amplitude.
- \(u^2-4u-(n-3)=0\) is exactly the condition \(w=0\) in (41.2).
  At a physical point, the Weyl orbit alone is then a SIC: indeed
  \(a=\beta=1/(n+1)\). Its positive amplitude is
  \(u=2+\sqrt{n+1}\).

The third interpretation follows directly from the formulas of Section
41 and does not use a conjecture about SIC existence. The order-7
algebraic branch has positive length; the table alone does not certify
which of its points satisfy physical conjugation.

`hi_amplitude_ideal.py` generates the equations, computes the exact
Gröbner basis, checks both inclusions of the displayed elimination
ideal, and computes all branch lengths. Its saved output is
`hi_amplitude_ideal_results.txt`.

This gives a concrete algebraic question for a uniform construction:
prove that the fiber
\[
 \operatorname{Spec}\bigl(R_n/(I_n+(t^4+nt^2-1))\bigr)
 \tag{42.4}
\]
has a physical point for unbounded odd \(n\). The two small elimination
certificates do not prove a general amplitude-factorization formula,
nor does their nonemptiness imply nonemptiness at larger orders.
Even a uniform construction of physical points in (42.4) would still
require the cubic identity, or a uniform quadratic-to-cubic theorem.
The isolation result in Section 41 explains why simply deforming the
flat component is not enough to establish (42.4).



# 43. A uniform quotient by the cyclic character gauge

The prefix formula (29.1) can be strengthened to an equivalence of
algebraic schemes, without any Stark-unit hypotheses. This gives a
smaller coordinate ring for the remaining quadratic-to-cubic problem.

Let \(n=2m+1\), \(K=\mathbb Q(d)\), and
\[
 \mathcal C_n=K[c_1,\ldots,c_{n-1}]/(c_jc_{n-j}-d).
\]
All the \(c_j\) are units. For \(2\le h\le n-1\), put
\[
 r_h=\frac{c_1c_{h-1}}{c_h}=B_{1,h}.
\]
Then \(r_h=r_{n+1-h}\), so there are just \(m\) independent
row variables \(r_2,\ldots,r_{m+1}\). Extend any choice of these
nonzero variables by that reflection and set
\[
 P_1=1,\qquad P_h=\prod_{j=2}^{h}r_j,\qquad
 \mathcal R_n=K[r_2^{\pm1},\ldots,r_{m+1}^{\pm1}].
\]

**Proposition.** There is an explicit isomorphism
\[
 \boxed{\mathcal C_n\cong
 \mathcal R_n[a]/(a^n-dP_{n-1}),\qquad
 c_h=\frac{a^h}{P_h}.} \tag{43.1}
\]
In particular, \(\mathcal C_n\) is a finite free, faithfully flat,
étale algebra of rank \(n\) over \(\mathcal R_n\).

**Proof.** In the forward direction, the recurrence for \(r_h\)
gives \(c_h=c_1^h/P_h\). At \(h=n-1\), the norm relation
\(c_1c_{n-1}=d\) gives \(c_1^n=dP_{n-1}\). Conversely,
reflection of the row variables gives
\(P_hP_{n-h}=P_{n-1}\). Thus the displayed formulas yield
\(c_hc_{n-h}=a^n/P_{n-1}=d\), and the two constructions are
inverse. The monic relation gives the free basis
\(1,a,\ldots,a^{n-1}\). Both \(a\) and \(n\) are invertible,
so its derivative \(na^{n-1}\) is a unit, proving étaleness. ∎

Over an algebraic closure, the \(n\) points over one row are exactly
\(c_h\mapsto\zeta^{jh}c_h\), \(0\le j<n\), where
\(\zeta^n=1\). This is the cyclic character gauge. The invariant
ring is \(\mathcal R_n\), and the entire matrix is recovered by
\[
 B_{g,h}=\frac{P_h}{P_gP_{h-g}}\quad(0<g<h<n),\qquad
 B_{h,g}=\frac d{B_{g,h}}, \tag{43.2}
\]
together with the fixed axes, diagonal, and origin.

For the physical embedding \(d>0\), the physical row conditions
are exactly \(|r_h|=\sqrt d\). They imply
\(|P_h|=d^{(h-1)/2}\) and \(|a|=\sqrt d\), hence
\(|c_h|=\sqrt d\) and \(c_{n-h}=\overline{c_h}\).
Conversely, physical phase data give those row norms. Thus (43.1)
also describes the physical phase space as a finite covering, with
no omitted sign or continuous parameter.

Let \(J_n\subset\mathcal R_n\) be the ideal of the scaled quadratic
equations after (43.2). For \(g,h\ne0\), direct substitution gives
\[
 \sum_j B_{g+j,h}B_{h,j}
 =\frac1d\sum_m c_m c_{h-m}c_{-m+g}c_{m-g-h}.
\]
Thus the phase quadratic ideal of Section 35, after the already
imposed norm relations, is exactly the extension of \(J_n\) to
\(\mathcal C_n\). Faithful flatness therefore gives
\[
 f\in J_n\quad\Longleftrightarrow\quad
 f\in J_n\mathcal C_n\qquad(f\in\mathcal R_n). \tag{43.3}
\]
In particular, the cubic ideal-membership problem can be carried out
in the smaller row ring without weakening it. Whenever these
quotients are finite-dimensional,
\[
 \dim_K(\mathcal C_n/J_n\mathcal C_n)
   =n\,\dim_K(\mathcal R_n/J_n). \tag{43.4}
\]

`hi_row_ideal.py` implements this reduction. It clears Laurent
monomials and adds one equation in an auxiliary variable to invert
the product of the row variables. Its exact computations at orders
3, 5, 7, and 9 give row scheme lengths 2, 4, 6, and 12, respectively,
with all cubic remainders zero. Multiplication by \(n\) reproduces the
phase scheme lengths 6, 20, 42, and 108 from Section 35.

The proposition applies to every odd order. It reduces the size of
the uniform existence problem but does not prove that its physical
quadratic locus is nonempty or that its cubic ideal is contained in
its quadratic ideal for unbounded orders.



# 44. Diagonal quadratics and Galois covariance are not sufficient

There is an exact physical counterexample to a further tempting reduction.
At \(n=5\), even the phase cocycle, every generic norm, full multiplier
Galois covariance, and all the diagonal equations \(Q_{g,g}=0\) together
do **not** imply the remaining quadratics. This does not contradict
Section 40: that section uses one quadratic to select signs of an
already specified arithmetic candidate, and then still checks all of (Q).

Put \(d=(5+\sqrt{29})/2\) and let \(r\) be a root of
\[
 f(X)=X^4+(d-2)X^3+dX^2+(3d+1)X+d^2.
 \tag{44.1}
\]
This polynomial is irreducible over \(K=\mathbb Q(d)\). Define
\[
 R(X)=\frac{(d-6)X^3+(6-d)X^2+(13-3d)X+3-3d}{5},
 \qquad r_2=R(r).
\]
Exact reduction modulo \(f\) proves
\[
 f(R(r))=0,\qquad R(R(r))=d/r.
\]
Thus \(L=K(r)\) is cyclic quartic over \(K\), with generator
\(\phi(r)=R(r)\), and \(\phi^2(r)=d/r\).

Take the reflected row \((B_{1,2},B_{1,3},B_{1,4})=(r,r_2,r)\)
and reconstruct the matrix by (43.2). Exact reduction gives
\[
 \phi(B_{g,h})=B_{2g,2h},\qquad
 \phi^2(B_{g,h})=B_{h,g}.
\]
These are genuine physical conjugation identities. Indeed, dividing
(44.1) by \(r^2\) shows that the two possible traces \(v=r+d/r\)
satisfy
\[
 v^2+(d-2)v-d=0.
\]
Both roots lie strictly between \(-2\sqrt d\) and \(2\sqrt d\),
so every physical root of \(f\) has modulus \(\sqrt d\). The
real-coefficient formula for \(R\) and the formal norm identity give
\(|r_2|=\sqrt d\) as well. Section 43 then supplies physical phases.

Nevertheless, writing the scaled quadratic residual as
\[
 \mathcal Q_{g,h}=\sum_{j\in\mathbb Z_5}B_{g+j,h}B_{h,j},
 \qquad g,h\ne0,
\]
we get exactly
\[
 \boxed{\mathcal Q_{g,h}=
 \begin{cases}
 0,&h=\pm g,\\
 2(d-1),&h\ne\pm g.
 \end{cases}} \tag{44.2}
\]
Thus there are eight nonzero residuals despite every diagonal one
vanishing and full Galois covariance holding. All these identities,
irreducibility, and the exact inequalities on the traces are checked
by `hi_diagonal_counterexample.py`.

The one-root condition does distinguish this counterexample. By (43.1),
a root \(W=c_1\) inside its row field would have to satisfy
\[
 W^5=d\,r^2R(r).
\]
There is **no** such root in \(L\). The exact `nfroots` calculation
in `hi_diagonal_kummer.gp` proves this using the absolute polynomial
\[
 X^8+X^7-2X^6+5X^5-9X^4-60X^3+2X^2+12X+1
\]
and the embedding
\[
 d=-\frac{r^4-2r^3+r+1}{r^3+r^2+3r+5}.
\]
The absolute field has degree 8, signature \((4,2)\), and discriminant
\(5^5\,29^4\). It also fails the prescribed ray conductor condition:
the prime with \(d\equiv1\pmod5\) has ramification index 4, while
the conjugate prime with \(d\equiv-1\pmod5\) has ramification index 2.
Both primes ramify, whereas the intended modulus contains only the
first. These local assertions are checked in the same GP script.
Consequently the arithmetic requirement that the phase root already
lie in the prescribed abelian field is substantive. This example
suggests testing that condition together with the specified conductor as a way to exclude spurious
diagonal components. It does not prove that the condition excludes every such
component in arbitrary order, nor replace the missing uniform
quadratic identity.



# 45. Exact quadratic-to-cubic containment at order 11

The row reduction in Section 43 now extends the ideal theorem to
\(n=11\). This certifies a statement about **every** phase solution
of the quadratic equations at that order, not just the previously
constructed secondary Stark branch.

**Theorem (exact computation).** At \(n=11\), every cross-zero-free
cubic polynomial lies in the quadratic phase ideal (35.1). Hence
\((Q)\Rightarrow(C)\) for every phase solution. The row quotient
has \(K\)-dimension 12, and the phase quotient has dimension 132.

The proof uses a homogeneous certificate to avoid an issue with
unverified modular reconstruction. A candidate Gröbner basis of a
nonhomogeneous ideal can pass finite-field comparisons and exact
forward inclusion without certifying the reverse inclusion. Zero
cubic remainders against that candidate alone would not prove the
theorem. The following exact argument supplies the missing step.

**Hilbert comparison lemma.** Let \(I\) be a homogeneous ideal over a
number field \(K\), specified by homogeneous generators integral at a
prime \(\mathfrak q\), and let \(H\) be another homogeneous ideal over
\(K\). Suppose that

1. \(I\subseteq H\) is verified exactly;
2. the Hilbert series of \(K[\mathbf x]/H\), computed from a certified
   Gröbner basis, equals that of
   \(k_{\mathfrak q}[\mathbf x]/\overline I\).

Then \(I=H\).

**Proof.** In each degree, form the matrix whose rows are the appropriate
monomial multiples of the specified generators of \(I\). Its rank
can only decrease on reduction modulo \(\mathfrak q\). Therefore
\[
 \dim_K(K[\mathbf x]/H)_a
 \le \dim_K(K[\mathbf x]/I)_a
 \le \dim_{k_{\mathfrak q}}
       (k_{\mathfrak q}[\mathbf x]/\overline I)_a.
\]
Equality of the outer Hilbert functions forces equality throughout
in every degree. The inclusion \(I\subseteq H\) is therefore an
equality. ∎

For the order-11 calculation, homogenize the 15 distinct nonzero row
quadratic generators and the product-inversion equation with a new
variable \(z\). A saved homogeneous candidate has 816 generators.
Its standard basis is certified by an **exact rational-arithmetic**
`std` computation, treating \(d\) as a final block variable and
adjoining \(d^2-11d-1\). Passing back to the coefficient field
\(K=\mathbb Q(d)=\mathbb Q(\sqrt5)\) preserves the standard-basis
property for the ordinary variables in this block order.

The independent reduction uses the prime 32003. The polynomial
\(d^2-11d-1\) is irreducible modulo this prime, so the residue field
has \(32003^2\) elements. Exact `std` of the reduced **original**
homogeneous generators gives the same Hilbert-series numerator:
\[
\begin{split}
 N(T)={}&1-6T^6-4T^7-3T^8-2T^9-T^{10}
 +93T^{11}+391T^{12}\\
 &-1728T^{13}+2404T^{14}-1587T^{15}
 +500T^{16}-58T^{17}.
\end{split}
\]
Both Hilbert series are \(N(T)/(1-T)^7\). The exact input inclusion
and the lemma prove equality of the homogeneous ideals.

After \(z=1\), exact inclusions identify the affine ideal with the
saved 21-element row basis. Its scheme length is 12. All 17 beta
representatives have zero exact remainder. The beta orbit symmetries
and invariance of the full quadratic ideal under index multipliers
cover the remaining cubic equations, as in Section 35. Faithful
flatness from (43.3) transfers membership back to the phase ideal,
and (43.4) gives its length \(11\cdot12=132\).

The independent verifier is `hi_row11_verify.py`. It reads
`hi_row11_homogeneous_basis.txt.gz` and `hi_row11_basis.txt`, regenerates
the original equations, and performs all the checks above. Its saved
output is `hi_row11_verification_results.txt`. The compressed large
basis is an input to the verifier; its origin in modular reconstruction
is not relied on for ideal equality.

The certified orders for the quadratic-to-cubic implication are now
\[
 \boxed{n=3,5,7,9,11.}
\]
There is still no proof of this implication for unbounded orders,
and proving it uniformly would still leave physical existence of
quadratic solutions to be established.



# 46. A degree obstruction to fixed-order cyclic hypergeometric formulas

A uniform analytic construction cannot use a bounded-degree nonsingular
rational formula for consecutive phase ratios. This follows already
from the exceptional amplitude, independently of (Q) or (C).

**Proposition.** Let \(b_j\ne0\), \(j\in\mathbb Z_n\), satisfy
\[
 |b_0|=t\ne1,\qquad |b_j|=1\quad(j\ne0).
\]
Let \(\zeta\) be a primitive \(n\)-th root of unity. Suppose
\[
 \frac{b_j}{b_{j-1}}=\frac{P(\zeta^j)}{Q(\zeta^j)}
 \quad\text{for every }j\in\mathbb Z_n,
 \qquad Q(\zeta^j)\ne0,
\]
where \(P,Q\in\mathbb C[z]\) have degrees at most \(r\). Then
\[
 \boxed{2r\ge n-2.}
\]
In particular, for odd \(n\), \(r\ge(n-1)/2\).

**Proof.** Define the reflected polynomials
\[
 P^*(z)=z^r\overline{P(1/\overline z)},\qquad
 Q^*(z)=z^r\overline{Q(1/\overline z)}.
\]
The polynomial \(F=PP^*-QQ^*\) has degree at most \(2r\).
For \(j=2,\ldots,n-1\), the consecutive ratio has modulus 1,
so \(F(\zeta^j)=0\). These are \(n-2\) distinct roots. But
\[
 F(1)=|P(1)|^2-|Q(1)|^2=(t^2-1)|Q(1)|^2\ne0,
\]
so \(F\) is not the zero polynomial. The degree bound follows. ∎

For comparison, a standard nonsingular cyclic hypergeometric weight
\[
 W(j)=\gamma^j\frac{(\alpha;\zeta)_j}{(\beta;\zeta)_j}
\]
has a consecutive ratio of degree at most 1. Products of \(k\)
such weights have ratio degree at most \(k\). The standard weight,
its periodicity condition, and the distinction between cyclic sums
and unrestricted root-of-unity limits are given in
[Au-Yang–Perk, *About 30 Years of Integrable Chiral Potts Model*, Section 4.2](https://arxiv.org/abs/1601.01014).
Thus a product with a fixed number of nonsingular factors cannot
produce HI phases for unbounded orders. A formula with a growing
number of factors, a different special function, or a limit requiring
separate regularization at the exceptional indices is outside the
proposition. Such a limit would still need its own proof of the finite
beta identity and the collision corrections.



# 47. Unconditional norm elements in every prescribed odd-order ray field

The multiplicative and physical part of the arithmetic ansatz can be
made nonempty uniformly, without assuming Stark algebraicity. This is
an existence theorem for **norm elements**, not for solutions of the
additive Izumi equations or for roots of a prescribed Stark unit.

Fix any odd \(n\ge3\), put
\[
 d=(n+\sqrt{n^2+4})/2,\quad K=\mathbb Q(d),\quad
 \mathfrak f=(d-1),
\]
and let \(v_+\) be the embedding with \(d>0\). For any nontrivial
ideal divisor \(\mathfrak a\mid\mathfrak f\), let \(L_{\mathfrak a}\)
be the full ray class field of modulus \(\mathfrak a v_+\).

## 47.1 A local–global norm theorem

**Theorem.** Physical complex conjugation defines a nontrivial
involution \(c\in\operatorname{Gal}(L_{\mathfrak a}/K)\). Its fixed
field \(M_{\mathfrak a}=L_{\mathfrak a}^{c}\) is totally real, and
\[
 \boxed{\exists W\in L_{\mathfrak a}^{\times}\quad
        Wc(W)=d.} \tag{47.1}
\]
In particular, every embedding above \(v_+\) has
\(|W|=\sqrt d\). The element \(W\) need not be an algebraic unit.

**Proof.** The unit \(d\) has norm \(-1\). Choose the fundamental
unit \(\epsilon>1\) at \(v_+\); it has norm \(-1\), and
\(d=\epsilon^m\) for an odd integer \(m\). Since \(d\equiv1\)
modulo \(\mathfrak a\), the residue of \(\epsilon\) has odd order.
No unit negative at \(v_+\) can be congruent to 1 modulo
\(\mathfrak a\): such a unit is \(-\epsilon^j\), which would
require an odd-order element to have a power equal to \(-1\).
Here \(-1\ne1\) because \(N\mathfrak a>1\) is odd.

Consequently the sign part of the ray-class exact sequence survives,
and \(v_+\) ramifies in the full ray field. The other real place,
which is omitted from the modulus, splits into real places. Abelianity
over \(K\) makes conjugation at every embedding above \(v_+\) the
same nontrivial involution \(c\). Its fixed field is totally real.

Consider the quadratic extension \(L_{\mathfrak a}/M_{\mathfrak a}\).
The element \(d\) is a norm at every completion:

- Above \(v_+\), the extension is \(\mathbb C/\mathbb R\), and
  \(d>0\).
- Above the other real place, the local algebra is
  \(\mathbb R\times\mathbb R\), whose norm takes every nonzero
  real value.
- Away from \(\mathfrak a\), every finite local extension is
  unramified or split. The element \(d\) is a unit, and units are
  norms in an unramified quadratic local extension.
- At a finite place above \(\mathfrak a\), the residue characteristic
  is odd and \(d\equiv1\). Hensel's lemma makes \(d\) a square in
  the base completion. A base-field square is a norm from any
  quadratic extension.

The cyclic Hasse norm theorem now gives (47.1); see
[Milne, *Class Field Theory*, the Hasse norm theorem in VIII.3](https://www.jmilne.org/math/CourseNotes/CFT.pdf).
At the physical embeddings, \(c\) is actual complex conjugation,
so the displayed norm equation proves the asserted modulus. ∎

The crucial distinction is that (47.1) does not prescribe
\(W^4/d^2\). It therefore does not prove that the distinguished
Stark unit satisfies the Kummer-root condition in Section 38.

## 47.2 Physical Galois-covariant phase data for every odd order

The theorem supplies an unconditional input space for all the
multiplicative matrix constraints, including at composite orders.
First observe that
\(\mathfrak f\overline{\mathfrak f}=(n)\) and that these two
ideals are coprime: a prime dividing both would force
\(d\equiv\overline d\equiv1\) and hence \(1\equiv-1\),
so would lie above 2. Thus every prime dividing \(n\) splits in
\(K\), and \(\mathcal O_K/\mathfrak f\cong\mathbb Z/n\mathbb Z\).
For each divisor \(q>1\) of \(n\), there is a unique ideal
\(\mathfrak f_q\mid\mathfrak f\) of norm \(q\). Write
\(L_q=L_{\mathfrak f_q}\subseteq L_n\).

Choose \(w_q\in L_q^\times\) with \(w_qc(w_q)=d\) by (47.1).
For \(a\ne0\) modulo \(n\), write
\[
 q=n/\gcd(a,n),\qquad a=(n/q)u,\qquad (u,q)=1,
\]
and define
\[
 W_a=\sigma_u(w_q),\qquad b_a=W_a/\sqrt d,
 \qquad b_0=-1/\sqrt d. \tag{47.2}
\]
Here \(\sigma_u\) is the ray automorphism labeled by a positive
integer lift of \(u\pmod q\). This convention includes
\(\sigma_{-1}=c\); it does not mean the Artin symbol of the unit
ideal \((-1)\). The definition is independent of the lift.

For every unit \(k\) modulo \(n\), restriction of ray automorphisms
and (47.1) give
\[
 \sigma_k(W_a)=W_{ka},\qquad W_{-a}=c(W_a)=d/W_a,
 \qquad |b_a|=1.
\]
Therefore the matrix
\[
 B_{g,h}=W_gW_{h-g}/W_h\quad(g,h,h-g\ne0),
\]
with the usual exceptional entries, has the physical norms,
Hermitian and rotation symmetries, phase cocycle, and every multiplier
covariance identity. All its entries belong to the prescribed full
ray field \(L_n\). If
\(s_a=W_a^4/d^2\), then it also satisfies
\[
 B_{g,h}^4=d^2s_gs_{h-g}/s_h.
\]
These \(s_a\) are norm-one elements; integrality and their
identification with analytic Stark units have not been asserted.
This constructs the multiplicative data at **every odd order**.
It makes no assertion that (Q) or (C) vanishes for the chosen data.

For prime powers, one can additionally impose compatible norms
throughout the conductor tower. If \(n=p^k\), let
\(L_j=L_{\mathfrak p^j}\) and choose \(W_k\) by (47.1).
The degrees \(r_j=[L_k:L_j]\) are odd powers of \(p\). Set
\[
 W_j=d^{(1-r_j)/2}N_{L_k/L_j}(W_k).
\]
Then \(W_jc(W_j)=d\), the normalized norm descents are transitive,
and the corresponding \(s_j=W_j^4/d^2\) satisfy
\(N_{L_j/L_i}(s_j)=s_i\). Applying the conjugate-prime twists from
Section 39 gives the monoid labeling there. This is an unconditional
multiplicative norm system, still with no specified Stark units and
no additive identity.

## 47.3 What remains after the norm construction

Given one \(W_0\) satisfying (47.1), Hilbert's theorem 90 gives all
such elements as
\[
 W=W_0\frac{U}{c(U)},\qquad U\in L_{\mathfrak a}^{\times}.
 \tag{47.3}
\]
Equivalently, choose a nonzero \(v\in L_{\mathfrak a}\) with
\(c(v)=-v\). Apart from one point, the norm conic has the rational
parameterization
\[
 W=W_0\frac{1+zv}{1-zv},\qquad z\in M_{\mathfrak a}.
\]
This follows directly by solving for \(z\), or from
[Milne, *Fields and Galois Theory*, Hilbert's theorem 90](https://jmilne.org/math/CourseNotes/FT500.pdf).

The permitted algebraic norm elements are dense in their possible
physical phase tuples. Indeed, the Minkowski embedding identifies
the rational vector space \(L_{\mathfrak a}\) with a dense rational
subspace of its real archimedean vector space. Approximating the
chosen complex values of \(U\) in (47.3) approximates any prescribed
phases, with opposite embeddings paired by conjugation. This density
does **not** imply an exact zero of the quadratic or cubic equations.
It emphasizes that those additive identities remain substantive.

For example, at the limiting phase tuple \(b_a=1\) for \(a\ne0\),
with \(t=d^{-1/2}\), the diagonal correlation is
\[
 \sum_m b_m^2b_{1-m}b_{-1-m}=n-3+t^2-2t\ne0.
\]
It is negative when \(n=3\) and positive when \(n\ge5\). Hence
nearby admissible algebraic norm elements also fail (Q). The norm
theorem cannot be promoted to HI existence by omitting this step.

`hi_ray_norm.gp` constructs the ray fields using `bnrclassfield`,
finds the totally real fixed subfield, solves its relative quadratic
norm equation, and checks \(Wc(W)=d\) exactly. It uses neither Stark
polynomials nor HI seeds. The completed checks at orders 3, 5, 7, 9,
and 11 are recorded in `hi_ray_norm_results.txt`; they illustrate the
uniform theorem rather than replace its local–global proof.


---


# 48. An explicit integral norm unit for every order congruent to 3 modulo 4

The preceding norm theorem can be strengthened to **unit** existence on
an unconditional infinite family. This supplies more of the arithmetic
input, while leaving the additive Izumi identities to be proved.

## 48.1 The conductor calculation

**Theorem.** Let \(n\ge3\) and \(n\equiv3\pmod4\), and retain
\(K=\mathbb Q(d)\), \(\mathfrak f=(d-1)\), and the full ray field
\(L=L_{\mathfrak f v_+}\). Then
\[
 L_0=K\bigl(\sqrt{1-d}\bigr)\subseteq L,
 \qquad
 W_0=1+\sqrt{1-d}\in\mathcal O_L^\times,
 \qquad W_0c(W_0)=d. \tag{48.1}
\]
In particular, integral norm elements exist at every prime
\(p\equiv3\pmod4\), an infinite set of orders.

**Proof.** The element
\[
 \theta=\frac{d+\sqrt{1-d}}2
\]
satisfies the monic integral polynomial
\[
 X^2-dX+\frac{n+1}{4}d.
\]
Its discriminant is
\(d^2-(n+1)d=1-d\). Thus the relative field discriminant of
\(L_0/K\) divides \(\mathfrak f\); in particular there is no
extra ramification at 2. The extension is quadratic, since
\(1-d<0\) at \(v_+\), and has precisely the permitted
archimedean ramification: at the other real place,
\(1-\overline d=1+1/d>0\).

For a quadratic extension the finite conductor is its relative
discriminant. Its full conductor therefore divides
\(\mathfrak f v_+\), proving the inclusion by class field theory.
See [Milne, *Class Field Theory*, V.3.27 and Example 3.29](https://www.jmilne.org/math/CourseNotes/CFT.pdf).
Finally \(W_0\) is integral and
\[
 N_{L_0/K}(W_0)=(1+\sqrt{1-d})(1-\sqrt{1-d})=d.
\]
Since \(d\) is a unit, \(W_0\) is a unit. Physical conjugation
restricts to the nontrivial automorphism of \(L_0/K\), giving
(48.1). ∎

This proof works for composite \(n\equiv3\pmod4\) as well. At a
composite order it supplies a unit in the top conductor field; it
does not assert unit-valued descent at every proper divisor stratum.
For prime orders there is only one nonzero stratum.

The absolute polynomial of this particular unit is
\[
 X^4-4X^3+(n+4)X^2-2nX-1.
\]
It follows by substituting \(d=2W_0-W_0^2\) in
\(d^2-nd-1=0\). Its constant term also confirms the absolute
unit norm \(-1\).

## 48.2 Primitive unit choices also exist in the full ray field

The low degree of the explicit seed is not a restriction on the
available norm units. Write \([L:K]=2h\), and put
\[
 E^-=\{u\in\mathcal O_L^\times:u c(u)=1\}.
\]
The signature of \(L\) is \((2h,h)\), and \(L^c\) is totally
real of degree \(2h\). Dirichlet's unit theorem therefore gives
\(\operatorname{rank}E^-=h\). More concretely, its logarithms at
the \(2h\) real embeddings span the subspace on which \(c\)
acts by \(-1\); its logarithms at the complex embeddings vanish.
The unit-lattice statement used here is the usual logarithmic form
of [Dirichlet's theorem, Milne, *Algebraic Number Theory*, Section 5](https://www.jmilne.org/math/CourseNotes/ANTc.pdf).

The real embeddings over the other embedding of \(K\) form a
regular \(\operatorname{Gal}(L/K)\)-set. Its anti-invariant
subspace is faithful: the vector supported with values \(1,-1\)
at the positions \(1,c\) is fixed by no nonidentity translation.
Consequently every nonidentity \(\sigma\) acts nontrivially on
\(E^-\otimes\mathbb R\).

For any fixed \(\sigma\ne1\), each condition
\[
 \sigma(W_0u)=W_0u \quad\hbox{or}\quad
 \sigma(W_0u)=-W_0u
\]
restricts \(u\in E^-\) to an empty set or a coset of a subgroup
of rank less than \(h\). A finite union of these cannot cover the
rank-\(h\) lattice. Choosing \(u\) outside it gives
\[
 K(W_0u)=L,
 \qquad K\bigl((W_0u)^4/d^2\bigr)=L. \tag{48.2}
\]
For the second assertion, an automorphism fixing the fourth power
would have \(\sigma(W)/W\in\mu_4(L)=\{1,-1\}\), since \(L\)
has real embeddings. These possibilities were both excluded.

Thus, at infinitely many prime orders, one can unconditionally
choose **primitive integral units** satisfying all the norm and
fourth-root multiplicative relations in the prescribed full ray
field. The corresponding fourth powers have not been identified
with distinguished analytic Stark units, and additive identities
are not part of this conclusion.

## 48.3 The explicit seed itself fails the quadratic equation uniformly

It is possible to locate the missing step exactly even for the
simple seed (48.1). Suppose \(p\equiv3\pmod4\) is prime and let
\(\chi\) be the quadratic character modulo \(p\). The quadratic
ray character restricts to \(\chi\) on the integer residue classes,
so its labeled phases in the scaled variables of Section 34 are
\[
 c_0=-1,\qquad c_a=1+\chi(a)r\ (a\ne0),
 \qquad r^2=1-d.
\]
Let \(e=\chi(2)\). Then the necessary diagonal quadratic residual is
\[
 \boxed{
 \sum_{m\bmod p}c_m^2c_{1-m}c_{-1-m}
 =\begin{cases}
 2p+2-(p+6)d,&e=1,\\
 2p-14+(10-p)d,&e=-1.
 \end{cases}} \tag{48.3}
\]
Both expressions are nonzero. In the first case the coefficient of
\(d\) is nonzero; in the second case \(10-p\ne0\). Irrationality
of \(d\) then excludes vanishing.

For completeness, pair \(m\) with \(-m\) to cancel all odd
powers of \(r\). On the complement of \(0,1,-1\), the two
character sums needed for the even part are
\[
 \sum\chi((m-1)(m+1))=0,
 \qquad
 \sum\chi(m)\bigl(\chi(m-1)+\chi(m+1)\bigr)=-2-2e.
\]
They follow from the complete quadratic-character sums \(-1\)
by removing those three indices. The remaining sum is
\((p-3)(2-d)+4(1+e)(1-d)\). The three excluded terms sum to
\(-d\) when \(e=1\), and to \(-8+7d\) when \(e=-1\), giving
(48.3).

Changing the overall sign of the nonzero phases changes only the
terms with exactly one zero index. The residual for \(-W_0\) is
\[
 2p+2-(p+2)d\ne0,
\]
independently of \(\chi(2)\). Thus neither sign of the explicit
seed solves even this one quadratic equation.

`hi_explicit_ray_unit.gp` independently verifies the integral-order
discriminant, the unit norm, and (48.3) exactly at every prime
\(p\equiv3\pmod4\) below 100. Its saved results accompany the
uniform proof. This calculation shows why the explicit unit theorem
alone is not an existence proof for HI categories.

# 49. An exact half-lattice reduction and a new unit-selection experiment

## 49.1 The norm-unit coset is an exact arithmetic object

Let \(L,M=L^c\) be as above, and suppose a unit \(W_0\) with
\(W_0c(W_0)=d\) is available. Section 48 proves this hypothesis
for every \(n\equiv3\pmod4\). All unit solutions are
\[
 \{W\in\mathcal O_L^\times:Wc(W)=d\}=W_0 E^-.
 \tag{49.1}
\]
There is also an exact test for the hypothesis at other orders.
Choose fundamental units \(u_1,\ldots,u_r\) of \(L\), let
\(C\in\operatorname{GL}_r(\mathbb Z)\) describe \(c\) on their
free exponent lattice, and let \(\delta\in\mathbb Z^r\) be the
free exponent vector of \(d\). Then
\[
 d\in N_{L/M}(\mathcal O_L^\times)
 \quad\Longleftrightarrow\quad
 (I+C)x=\delta\text{ has }x\in\mathbb Z^r. \tag{49.2}
\]
Indeed a solution makes the relative norm equal to \(d\) up to
a root of unity. The only roots of unity are \(\pm1\), and
positivity of both the norm and \(d\) at a physical embedding
forces the plus sign. The same argument shows that a basis of
\(\ker_{\mathbb Z}(I+C)\) gives norm-one units, with no missed
negative-norm correction.

Choose a basis \(v_1,\ldots,v_h\) of \(E^-/\{1,-1\}\). Let
\(\tau_1,\ldots,\tau_{2h}\) be all the real embeddings of \(L\),
and write
\[
 \mathcal L_{ij}=\log|\tau_i(v_j)|,
 \qquad
 a_i(W)=\log|\tau_i(W)|+\tfrac12\log d_+,
\]
where \(d_+>0\) denotes the physical value of \(d\).
Since \(W_0^2/d\in E^-\), there is an **integer** vector
\(\kappa\) with
\[
 W_0^2/d=\pm\prod_jv_j^{\kappa_j}.
\]
At a real embedding \(\tau_i(d)=-1/d_+\), and therefore
\[
 2a(W_0)=\mathcal L\kappa,
 \qquad
 \boxed{\{a(W):Wc(W)=d,\ W\text{ a unit}\}
 =\mathcal L(\mathbb Z^h+\tfrac12\kappa).} \tag{49.3}
\]
The parity class \(\kappa\bmod2\) is independent of the initial
norm unit. Both signs of \(W\) give the same logarithms. Thus
minimizing the centered squared logarithmic size is exactly the
shortest-vector problem
\[
 \min_{z\in\mathbb Z^h, z\equiv\kappa\ (2)}
 z^{\mathsf T}(\mathcal L^{\mathsf T}\mathcal L)z.
 \tag{49.4}
\]
The reported score in the computation below is this doubled-log
score, four times \(\|a(W)\|^2\).

## 49.2 Exact finite Izumi certificates from short norm units

`hi_ray_unit_search.gp` constructs the prescribed ray field, solves
its norm equation, computes the action of physical conjugation on
units, and searches (49.4). It uses no HI seeds and calls no Stark
unit constructor. Logarithms order the candidates; acceptance
requires **exact** full quadratic identities, every remaining
balanced-beta cubic representative, and multiplier covariance.
Candidates in the same exactly checked Galois orbit share that
certificate.

The completed results are:

| Order | Relative unit rank | Accepted vectors modulo conjugation in the observed lowest shell | Exact Q and C |
|---:|---:|---:|---|
| 3 | 1 | 1 | pass |
| 5 | 2 | 2 | pass |
| 7 | 3 | 3 | pass |
| 11 | 1 | 1 | pass |
| 13 | 6 | 6 | pass |
| 17 | 8 | 8 | pass |
| 29 | 2 | 2 | pass |
| 199 | 9 | 9 | exact transport of the saved complete certificate |

At each order the accepted vectors form one Galois orbit, after
choosing their signs. The initially returned norm element failed
both sign choices at 11, 13, and 17; the unit-lattice search found
complete solutions at all three. This demonstrates a selection
mechanism different from specifying a distinguished Stark unit.

At order 199, the new construction yields nine vectors in its observed
lowest shell. Each one, with the appropriate sign, exactly matches the
previous complete certificate through a field isomorphism that preserves
\(d\) and the Artin generator. The saved certificate is used only after
the unit-lattice construction, to identify and verify its output. This
avoids repeating the 108,406 cubic representatives. The absolute unit
group completeness and global logarithmic minimality are not certified
at this order either; the transported finite Izumi certificate is exact.
The result is saved in `hi_ray_unit199_results.txt`.

The optional explicit-unit mode now starts directly from (48.1),
without a general norm solver. Its completed exact Izumi checks at
3, 7, and 11 are in `hi_ray_unit_explicit_results.txt`.

There are two separate limits on the shortest-shell claim. The
logarithmic enumeration uses floating arithmetic and is not an
interval certificate of global minimality. Also, completeness of
the absolute fundamental-unit group was certified at 3, 5, 7, 11,
and 29, while the expensive completeness certificates at 13 and 17
were not completed. At those two orders all units, conjugation
relations, norm identities, and accepted Izumi identities were still
verified exactly. Consequently the **finite existence certificates
are unconditional**, while global shortest-shell classification is
not claimed by these logs.

At rank one the geometric minimization itself is elementary once
the full unit group and the parity class are certified: an odd
coset has just two shortest integer vectors, \(1\) and \(-1\).
At order 11 this explains the correction of the initial candidate.
For the unit basis used in the calculation, its exact twice-offset
is 5, so the two nearest exponents relative to it are \(-2\) and
\(-3\). These are precisely the two translates passing (Q), with
opposite overall signs.

## 49.3 A precise remaining uniform target

For every prime \(p\equiv3\pmod4\), Sections 48–49 now provide
an unconditional nonempty norm-unit coset and hence a nonempty
finite shortest shell. A sufficient next theorem would be:

> For every such prime, some shortest norm unit, with one of its
> two signs, gives a matrix satisfying (Q) and (C) under the Artin
> labeling of Section 47.

This statement is **unproved**. Even a proof for an unbounded
subset of these primes would establish the requested infinitude.
The arithmetic construction, integrality, nonempty unit coset,
and availability of primitive generators no longer need Stark
conjectures on this prime family. What is still missing is a theorem
connecting unit selection to the additive identities. The finite
checks above do not establish that connection for unbounded orders.

---


# 50. The cubic equations are a fifth-order condition on one unitary operator

There is a uniform spectral formulation of the remaining cubic
problem. It applies at every odd order and does not assume that
quadratic equations imply cubic equations.

## 50.1 A transfer operator with a universal three-dimensional part

Let \(A\) be a physical matrix in the present phase ansatz satisfying
all of (Q), and put \(t=1/d\). On
\(\mathcal H=\mathbb C^{\mathbb Z_n\times\mathbb Z_n}\), define
\[
 (Rf)(a,b)=\sum_{c\in\mathbb Z_n}A_{b,a+c}f(b,c).
 \tag{50.1}
\]
Let \(u,v\) be unit vectors with
\[
 u(a,b)=n^{-1/2}\mathbf1_{b=0},
 \qquad v(a,b)=n^{-1/2}\mathbf1_{a=0},
 \qquad w=Ru.
\]
The column correlations (Q), together with Hermitian symmetry, give
\[
 RR^*=I-(1-t^2)uu^*,
 \qquad R^*R=I-(1-t^2)vv^*. \tag{50.2}
\]
Here \(nt=1-t^2\). The fixed exceptional row also gives
\(\sum_a A_{0,a}=-t\), and direct multiplication yields
\[
 Rv=-tu,\qquad Rw=v-tu. \tag{50.3}
\]
For the second identity, one uses
\[
 (R^2u)(a,b)=n^{-1/2}\sum_c A_{b,a+c}A_{c,b}
 =n^{-1/2}(\delta_{a,0}-t\delta_{b,0}).
\]

The space \(\mathcal K=\operatorname{span}(u,v,w)\) has dimension
three. Its Gram matrix is
\[
 \begin{pmatrix}
 1&1/n&-t/n\\
 1/n&1&-t/n\\
 -t/n&-t/n&1-t/n
 \end{pmatrix},
\]
whose determinant is
\[
 \frac{(2t+1)(t^2+t-1)^2}{(1-t^2)^3}>0
 \qquad(n\ge3).
\]
In this basis the restriction of \(R\) to \(\mathcal K\) is
\[
 R_{\mathcal K}=
 \begin{pmatrix}0&-t&-t\\0&0&1\\1&0&0\end{pmatrix},
 \qquad
 \det(XI-R_{\mathcal K})=X^3+tX+t. \tag{50.4}
\]
This restriction is invertible. Equations (50.2) and invariance of
\(\mathcal K\) then show that \(R^*\mathcal K\subseteq\mathcal K\):
write \(y=Rx\) with \(x\in\mathcal K\), and use
\(R^*Rx=x-(1-t^2)v\langle v,x\rangle\).
Thus \(\mathcal K\) reduces \(R\), and
\[
 U=R\big|_{\mathcal K^\perp}
 \quad\text{is unitary of dimension }n^2-3. \tag{50.5}
\]
All of these statements use (Q) and the fixed matrix symmetries,
with no use of (C).

## 50.2 An exact identity for the complete cubic residual

Write the residual of (C) in the \(A\) normalization as
\[
 \Phi_{g,h,k,l}=
 \sum_m A_{m,g+h}\overline{A_{m+k,g}A_{m+l,h}}
 -A_{g+l,k}A_{h+k,l}+t\delta_{g,0}\delta_{h,0}.
\]
Then
\[
 \boxed{
 \sum_{g,h,k,l}|\Phi_{g,h,k,l}|^2
 =2\left(d^2-5+6d^{-2}-\operatorname{Re}\operatorname{Tr}R^5\right)
 =\|U^5-I\|_{\mathrm{HS}}^2.
 } \tag{50.6}
\]
In particular, under (Q), the following are equivalent:
\[
 \boxed{
 \text{all of (C)}
 \quad\Longleftrightarrow\quad U^5=I
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\operatorname{Tr}R^5=d^2-5+6d^{-2}.
 } \tag{50.7}
\]
Thus all the cubic equations can be replaced by one scalar fifth-trace
identity, or by a fixed fifth-order condition on the unitary part.

**Proof of the residual identity.** Write \(\Phi=X-Y+Z\), with
\(X\) the summed term, \(Y\) the product of two entries, and
\(Z=t\delta_{g,0}\delta_{h,0}\). Column orthogonality and the
exceptional column give
\[
\begin{aligned}
 \|X\|^2&=n^2-3nt+2t^2+t^4,\\
 \|Y\|^2&=(n-t)^2,\\
 \|Z\|^2&=n^2t^2,\\
 \sum X\overline Z&=-t^4,\\
 \sum Y\overline Z&=t(n-t).
\end{aligned}
\]
For example, when summing \(|X|^2\) over \(k,l\), (Q) gives
\((\delta_{m,m'}-t\delta_{g,0})
 (\delta_{m,m'}-t\delta_{h,0})\). Summing the remaining indices
produces the first displayed expression.

The remaining cross term is a cyclic contraction of five entries:
\[
 \sum X\overline Y
 =\sum_{x_1,\ldots,x_5}
   \prod_{i=1}^5 A_{x_i,x_{i-1}+x_{i+1}}
 =\operatorname{Tr}R^5, \tag{50.8}
\]
with indices \(i\) taken modulo 5. The equality follows by
Hermitian symmetry and the cyclic ordering \((m,g,k,l,h)\).
Combining the six terms and substituting \(n=d-d^{-1}\) gives
the first equality in (50.6).

The cubic in (50.4) gives
\(\operatorname{Tr}R_{\mathcal K}^5=5t^2\), either by Newton's
identities or direct multiplication. Therefore unitarity of \(U\)
gives
\[
 \|U^5-I\|_{\mathrm{HS}}^2
 =2\bigl(n^2-3-\operatorname{Re}(\operatorname{Tr}R^5-5t^2)\bigr),
\]
which is the same expression. Positivity of the two sums of squares
proves (50.7). ∎

For the phase ansatz, \(\overline{A_{g,h}}=A_{-g,-h}\).
Conjugating every index by negation gives
\(\overline R=JRJ^{-1}\), so \(\operatorname{Tr}R^5\) is real.
Hence the scalar equality itself, without a real-part operation,
is an exact number-field certificate in this setting.

## 50.3 An equivalent polynomial test and the remaining gap

The cubic \(f(X)=X^3+tX+t\) has no root on the unit circle:
\(|tX+t|\le2t<1=|X^3|\). Hence \(f(U)\) is invertible.
Together with (50.4), this proves one more equivalent condition:
\[
 \boxed{
 (R^5-I)(R^3+d^{-1}R+d^{-1}I)=0.
 } \tag{50.9}
\]
This is a degree-eight matrix polynomial, with a degree independent
of \(n\). It eliminates the need to construct the orthogonal
complement explicitly when checking an exact candidate.

Alternatively, the Hermitian operator \(H=U+U^*\) has spectrum in
\([-2,2]\), and (C) is equivalent to
\[
 (H-2I)(H^2+H-I)=0.
\]
Thus its permitted eigenvalues are exactly
\(2,(\sqrt5-1)/2,-(\sqrt5+1)/2\). The same defect has the
nonnegative spectral expression
\[
 \sum|\Phi|^2
 =\operatorname{Tr}\bigl((2I-H)(H^2+H-I)^2\bigr).
\]
These formulas follow from \(U^* = U^{-1}\) and the fifth
Chebyshev identity. They provide an equivalent formulation using a
Hermitian operator and three allowed eigenvalues.

The operator theorem does **not** assert that (50.7) follows from
(Q) alone. It isolates the missing implication as a finite-order
spectral constraint. A uniform proof that the arithmetic candidates
satisfy both (Q) and this fifth-order condition would establish HI
existence on the infinite prime family of Section 48.

`hi_pentagon_operator.gp` verifies (50.2), (50.3), the exact scalar
trace certificate, and the polynomial test at orders 3, 5, and 7.
It uses the unit construction and does not evaluate the original
cubic loops. The companion Python file checks the indexing of the
complete residual-norm calculation on a random phase input and the
known order-13 solution; these latter checks are explicitly numerical.
The proof above supplies the uniform statement.

---

# 51. An explicit analytic candidate at every odd order

The boundary-value experiment proposed in Sections 23 and 27 can now be
replaced by a finite, directly evaluable double-sine formula. Throughout
this section,
\[
 d=\frac{n+\sqrt{n^2+4}}2>0,\qquad \delta=-d^{-1}<0.
\]
The resulting real matrices use \(\delta\), not the physical dimension
\(d\). They will be called **ghost candidates**. Numerical agreement with
their equations is not an existence certificate.

## 51.1 The continued-fraction cycle and its phase cancellation

**Proposition.** For every odd \(n\ge3\), the reduced quadratic irrational
\(\alpha=d+1\) has Hirzebruch–Jung cycle
\[
 [\overline{n+2,\underbrace{2,\ldots,2}_{n-1}}],\qquad
 \beta_0=d+1,\qquad
 \beta_j=\frac{d-j+1}{d-j}\quad(1\le j\le n).
 \tag{51.1}
\]
Here \(\beta_n=\beta_0\), and \(\prod_{j=1}^n\beta_j=d^2\).
For the residue label \(1\le a<n\), set
\[
 v_j=\left\{\frac{(j-1)a}{n}\right\},\qquad
 r_{j,1}=v_{j-1}-1,\quad r_{j,2}=v_j,\quad
 z_j=1-v_{j-1}+\beta_jv_j.
 \tag{51.2}
\]
Indices on \(v\) are periodic modulo \(n\). These are exactly the
normalized characteristics in \([-1,0)\times[0,1)\).

**Proof.** The recurrence \(\beta_{j+1}=1/(b_j-\beta_j)\), with
\(b_0=n+2\) and \(b_j=2\) otherwise, gives (51.1) directly using
\(d-n=d^{-1}\). If \(T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)\)
and \(S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)\), its word is
\[
 P=(T^{n+2}S)(T^2S)^{n-1}
 =\begin{pmatrix}n^2+n+1&-n^2\\n&1-n\end{pmatrix}
 =T^{n+1}\begin{pmatrix}1&n\\n&n^2+1\end{pmatrix}T^{-(n+1)}.
\]
The characteristic of Section 23 becomes
\((-2a/n,-a/n)\) after this conjugation. Each inverse step acts by
\((r_1,r_2)\mapsto(r_2,-r_1+b_jr_2)\). Since \(b_j\equiv2\pmod n\),
the unnormalized characteristic at step \(j\) is
\(((j-2)a/n,(j-1)a/n)\) modulo integers, proving (51.2). ∎

Write
\(\operatorname{Sin}_2(z;\beta,1)=
\Gamma_2(\beta+1-z;\beta,1)/\Gamma_2(z;\beta,1)\).
The explicit positive candidate is
\[
 \boxed{\displaystyle
 q_a=\prod_{j=0}^{n-1}\operatorname{Sin}_2(z_j;\beta_j,1)^{-1}.
 }\tag{51.3}
\]
All factors lie in their positive-period strip \(0<z_j<\beta_j+1\).
Kopp's double-sine cocycle formula identifies this product with the
normalized RM value; the construction also applies to the order
\(\mathbb Z[d]\), which need not be maximal.
[Kopp, Sections 7.2–7.3](https://arxiv.org/html/2411.06763v2#S7.SS2).

In this specialization even the phase normalization is elementary.
The two sums occurring in the double-sine transformation formula vanish:
\[
 \sum_j(\beta_j-3+\beta_j^{-1})=0,\qquad
 \sum_j\frac{(\beta_j-z_j)(1-z_j)}{\beta_j}=0.
 \tag{51.4}
\]
For the first use \(\sum_jb_j=3n\). For the second, substitute (51.2)
and pair \(\beta_j\) with \(\beta_{j+1}^{-1}\). The sum becomes
\[
 \sum_j(v_j-v_{j-1})^2-nv_0(1-v_0).
\]
The differences are \(a/n\) on \(n-a\) steps and \(a/n-1\) on
\(a\) steps, including when \(a\) is not a unit modulo \(n\).
Their squared sum is \(a(n-a)/n=nv_0(1-v_0)\). Thus the cocycle
value in the convention of Section 23 is the positive number \(q_a\)
itself, with no unresolved sign in this evaluation.

The order qualification matters. At \(n=11\), for example,
\(\mathbb Z[d]\) has conductor 5 in \(\mathbb Q(\sqrt5)\).
Formula (51.3) must not silently be identified with the smaller
maximal-order ray field used for the secondary branch. The formula
defines its analytic numbers without requiring any such identification.

## 51.2 Exact inverse symmetry and the proposed signs

**Proposition.** The numbers in (51.3) satisfy
\[
 q_a>0,\qquad q_aq_{n-a}=1.\tag{51.5}
\]

**Proof.** For a step with \(v_{j-1},v_j\ne0\), negating \(a\)
replaces \(z_j\) by \(\beta_j+1-z_j\), so reflection cancels the
two double sines. A boundary step \(v_j=0\) is followed by the
first-coordinate boundary \(r_{j+1,1}=-1\). Put
\(x=1-v_{j-1}\in(0,1)\).
At the first step the product of the two double sines is
\(2\sin(\pi x)\); at the next it is
\((2\sin(\pi x))^{-1}\). These follow from reflection and the
two shifts
\(\operatorname{Sin}_2(z+\beta;\beta,1)=
\operatorname{Sin}_2(z;\beta,1)/(2\sin\pi z)\) and
\(\operatorname{Sin}_2(z+1;\beta,1)=
\operatorname{Sin}_2(z;\beta,1)/(2\sin(\pi z/\beta))\).
The boundary steps pair disjointly because two successive \(v_j\)
cannot both vanish for \(0<a<n\). This proves (51.5). ∎

The sign search at small orders suggests the fixed, elementary rule
\[
 \varepsilon_a=-(-1)^{a(a+n)/2}=-i^{a(a+n)},\qquad
 W_0=-1,\qquad W_a=\varepsilon_a\sqrt{q_a/d}\quad(1\le a<n).
 \tag{51.6}
\]
There is no fitted parameter in this proposal. The signs satisfy
\(\varepsilon_{n-a}=-\varepsilon_a\), hence
\(W_aW_{n-a}=\delta\) exactly. Define
\[
 B_{0,0}=\delta-2,\qquad B_{g,0}=B_{0,g}=B_{g,g}=-1\quad(g\ne0),
 \qquad B_{g,h}=\frac{W_gW_{h-g}}{W_h}
\]
at the remaining positions, and \(A=B/(\delta-1)\). This establishes
the multiplicative normalization and order-three symmetry
\(A_{g,h}=A_{-h,g-h}\) uniformly. The claim that (51.6) gives the
correct signs for the **additive** equations remains conjectural.

**Explicit analytic conjecture.** For every odd \(n\ge3\), the
matrix defined by (51.1)–(51.6) satisfies
\[
 \sum_m A_{m,g+h}A_{g,m+k}A_{h,m+l}
 =A_{g+l,k}A_{h+k,l}-\delta^{-1}\delta_{g,0}\delta_{h,0}.
 \tag{51.7}
\]
Every quantity here is given by a convergent real integral and a
finite product. No Stark algebraicity assumption is part of the
statement. Section 52 explains its precise categorical consequence.

## 51.3 Numerical checks and a failed route to the physical embedding

The implementation `hi_shintani_ghost.py` uses
\[
 \log\operatorname{Sin}_2(z;\beta,1)=
 \int_0^\infty\left[
 \frac{\beta+1-2z}{\beta t}
 -\frac{\sinh((\beta+1-2z)t/2)}{2\sinh(\beta t/2)\sinh(t/2)}
 \right]\frac{dt}{t}.
 \tag{51.8}
\]
The subtraction at zero is evaluated by a convergent series. The
program independently checks reflection, both shifts, and period
scaling. It evaluates both halves of (51.5), rather than imposing
that equality numerically.

Initial screening passed the quadratic equations and numerical cubic
checks for every odd order from 3 through 31. The saved higher-precision
run checks all quadratics and all cross-free cubic orbits at
\(3,7,11,13,19,25,31\), using 60 requested digits and 15 guard digits.
The orbit calculation uses only the proved balanced-beta symmetries;
it makes **no scalar/Galois quotient**, since reciprocity of the analytic
numbers is not assumed. Collision equations follow algebraically from
the quadratics as in Section 34. Independent full cubic loops are
available with `--full-cubic`.

For example, direct analytic evaluation gives
\[
 q_1\big|_{n=7}=10.3078696780804590050094397024\ldots,\qquad
 q_2\big|_{n=7}=5.4484617205726756972518020268\ldots.
\]
These agree numerically with the positive square roots of the earlier
real Stark roots. They were computed without reading those roots.
At order 31 the saved quadratic and representative cubic errors are
\(1.10\times10^{-68}\) and \(1.39\times10^{-64}\), respectively.
An independent full cubic loop at order 7, rerun with 80 requested
digits and 15 guard digits, has maximum error below \(8.3\times10^{-95}\).
The residuals and the precision checks remain numerical, not rigorous
error bounds for exact zeros.

Replacing \(d\) by \(-1/d\) inside the positive-period double-sine
product does **not** implement the desired algebraic conjugation to a
physical matrix. The corresponding normalized product is 1: the unit
\(\delta\equiv1\pmod{\delta-1}\) has the sign that kills the relevant
second-place class. This is the fiber-one case of Kopp's
Theorem 7.15. [Kopp, proof of Theorem 7.15](https://arxiv.org/html/2411.06763v2#S7.SS2).
Direct evaluation checks this behavior too. An analytic substitution
at the conjugate quadratic point therefore supplies no unitarity proof.

---

# 52. Cubic reconstruction without first assuming Stark algebraicity

The negative-dimension calculation need not wait for an algebraicity
theorem before it can have a categorical consequence. The following
reduction is entirely polynomial and does not use positivity.

## 52.1 A uniform residual identity

Let \(G\) be a finite abelian group, \(t=\delta^{-1}\), and assume only
the order-three symmetry \(A_{g,h}=A_{-h,g-h}\). Define
\[
 Q(g,h)=\sum_m A_{m+g,h}A_{h,m}-\delta_{g,0}+t\delta_{h,0},
\]
\[
 C(g,h,k,l)=\sum_m A_{m,g+h}A_{g,m+k}A_{h,m+l}
 -A_{g+l,k}A_{h+k,l}+t\delta_{g,0}\delta_{h,0},
\]
and the quartic residual
\[
\begin{aligned}
 K(g,h,i,k)={}&\sum_{l,m}A_{l,m}A_{l+g,h}A_{h+m,l+i}A_{i,k+m}\\
 &-A_{h-g,i-g}\delta_{k,g}
 +t\delta_{h,0}A_{i,k}+tA_{g,h}\delta_{i,0}.
\end{aligned}
\]
Then, identically even away from solutions,
\[
 \boxed{\displaystyle
 K(g,h,i,k)=
 \sum_m A_{i,k+m}C(-h,h+m,g-h,i)
 +A_{i-h,g-h}Q(g-k,i).
 }\tag{52.1}
\]

**Proof.** In the inner sum over \(l\), replace
\(A_{l+g,h}\) by \(A_{-h,l+g-h}\). The definition of \(C\) makes
that inner sum
\[
 C(-h,h+m,g-h,i)+A_{i-h,g-h}A_{m+g,i}
 -t\delta_{h,0}\delta_{m,0}.
\]
Multiply by \(A_{i,k+m}\) and sum over \(m\). The remaining quadratic
sum is \(Q(g-k,i)+\delta_{g,k}-t\delta_{i,0}\).
Finally use \(A_{i-h,g-h}=A_{h-g,i-g}\), and, when \(i=0\),
\(A_{-h,g-h}=A_{g,h}\). This gives (52.1). ∎

With the exceptional row and column
\(A_{g,0}=A_{0,g}=a+\delta_{g,0}\), where
\(a=-1/(\delta-1)\), there is also the identity
\[
 \boxed{C(g,0,k,0)=a\,Q(-k,g).}\tag{52.2}
\]
To see it, split \(A_{0,m}=a+\delta_{m,0}\) in the cubic sum;
the constants cancel using \(a(1-t)+t=0\).
Thus **all cubics imply all quadratics and quartics** in this
normalization, over either quadratic embedding. This is distinct
from the still unresolved converse \(Q\Rightarrow C\).

`hi_cubic_quartic.py` checks (52.1) exactly on rational order-three
symmetric matrices that deliberately fail Q and C, and checks (52.2)
after imposing the exceptional row and column. All positions at orders
3, 5, and 7 pass. The proof above, not the finite tests, supplies the
uniform ideal containment.

## 52.2 Conditional categorification and automatic algebraicity

**Theorem.** Fix an odd \(n\ge3\). If the explicit matrix of Section 51
satisfies (51.7), it gives a spherical fusion category with the cyclic
HI fusion rules and categorical dimension \(\delta<0\). All of its
entries, and all the numbers \(q_a\), are algebraic. No Stark
algebraicity hypothesis is required for these conclusions.

**Proof.** The order-three symmetry and exceptional values are already
proved. Their column sum is \(-\delta^{-1}\), since
\(\delta^2=n\delta+1\). Equations (52.1)–(52.2) supply the quadratic
and quartic identities. These are precisely the \(\omega=1\) hypotheses
of Evans–Gannon's algebraic reconstruction, which permits either sign
of \(\delta\). [Evans–Gannon, Theorem 2(a)](https://arxiv.org/pdf/1506.03546).

For fixed \(n,\delta,\omega=1\), their Theorem 2(b) identifies
equivalent matrices exactly by the finite group \(\operatorname{Aut}(G)\).
Ocneanu rigidity gives finitely many equivalence classes for fixed
fusion rules. [Etingof–Nikshych–Ostrik, Theorem 2.28](https://annals.math.princeton.edu/wp-content/uploads/annals-v162-n2-p01.pdf).
It follows that the polynomial reconstruction system has finitely
many complex points. Since it is defined over \(\mathbb Q(\delta)\),
every coordinate of each point is algebraic. This also establishes
algebraicity in the particular displayed gauge, not just after an
unspecified change of basis.

Finally let \(R_h=B_{1,h}\) for \(2\le h<n\); these entries are
nonzero. The multiplicative formula gives
\[
 W_h=\frac{W_1^h}{\prod_{j=2}^hR_j},\qquad
 W_1^n=\delta\prod_{j=2}^{n-1}R_j.
\]
Consequently every \(W_h\), and then \(q_h=dW_h^2\), is algebraic. ∎

After algebraicity, a field embedding taking \(\delta\) to \(d>0\)
also yields a spherical categorification with positive categorical
dimensions, hence a pseudo-unitary one. This does not establish that
the conjugated matrix is Hermitian. Evans–Gannon's Theorem 2(c)
requires that additional condition for unitarity.

Therefore (51.7) at infinitely many odd orders would establish
infinitely many categorifications, and would simultaneously prove
algebraicity for this family of RM values. The stronger unitary
existence goal still needs either a Hermitian positive-embedding
argument or an independent physical construction. At present the
analytic identity itself is supported by the recorded computations,
not proved. Integrality, the precise class field, and reciprocity do
not follow merely from the algebraicity argument.

---

# 53. A uniform convex construction of algebraic one-column solutions

The signs in Section 51 also define a bounded convex domain. Its
logarithmic center gives an unconditional algebraic candidate at every
odd order, without evaluating a Stark invariant. The theorem below
proves one complete quadratic column, not the full HI system.

## 53.1 The domain and its unique center

Fix \(n=2m+1\ge3\), let \(h=(n+1)/2\in\mathbb Z_n\), and retain
\(d>0\), \(\delta=-1/d\). Set
\[
 L=(\delta-1)^2,\qquad
 \gamma=\frac{d-1}{d+1}=-\frac{n\delta}{L}\in(0,1).
 \tag{53.1}
\]
Consider real sequences \(u\) with
\[
 u_0=u_1=-1,\qquad u_a=u_{1-a},\qquad
 (-1)^{a+1}u_a>0\quad(2\le a<n).
 \tag{53.2}
\]
There are \(m\) free coordinates, represented by \(u_2,\ldots,u_h\).
Center the reflection by putting \(x_j=u_{h+j}\); then \(x_j=x_{-j}\).
The real eigenvalues of its symmetric circulant matrix \(T\) are
\[
 \lambda_k=\sum_{j\in\mathbb Z_n}x_j e^{2\pi i jk/n},\qquad
 \lambda_{n-k}=\lambda_k.
\]
Impose the additional linear inequalities
\[
 -(-1)^k\lambda_k>0\qquad(0\le k\le m).
 \tag{53.3}
\]
Denote the resulting open polytope by \(\mathcal P_n\).

**Theorem.** The polytope \(\mathcal P_n\) is nonempty and bounded.
The function
\[
 \boxed{\displaystyle
 \mathcal F(u)=\log|\det T|
             +\gamma\sum_{a=2}^{n-1}\log|u_a|
 }\tag{53.4}
\]
has a unique critical point \(u^*\) in \(\mathcal P_n\), its global
maximum. This point is nondegenerate and all its coordinates are
algebraic over \(\mathbb Q(\delta)\).

**Proof.** Start at \(u_0=u_1=-1\), with all free coordinates zero.
Its Fourier eigenvalues are
\[
 \lambda_k^{(0)}=-2\cos(2\pi kh/n)
 =-2(-1)^k\cos(\pi k/n).
\]
They are nonzero and have the signs in (53.3). Small free coordinates
with the prescribed signs therefore give points in \(\mathcal P_n\).

Fourier inversion at \(x_h=u_1=-1\) gives the positive linear relation
\[
 |\lambda_0|+
 2\sum_{k=1}^{m}\cos(\pi k/n)|\lambda_k|=n.
 \tag{53.5}
\]
All coefficients are positive. Thus all eigenvalues, and by Fourier
inversion all coordinates, are bounded on the domain.

On this domain, (53.4) is a sum of logarithms of positive affine
functions, with positive weights. The coordinate-log terms alone
have negative-definite Hessian on the \(m\) free variables.
Consequently \(\mathcal F\) is strictly concave. At every boundary
point at least one coordinate or eigenvalue tends to zero, while all
others remain bounded; hence \(\mathcal F\to-\infty\).
Existence of an interior maximum and its uniqueness follow.

Finally, the critical equations are rational equations over
\(\mathbb Q(\delta)\): use the derivative of \(\log\det T\), where
\(T\) has entries linear in \(u\). Their Jacobian is the invertible
Hessian just described. Clearing the nonzero denominators gives an
isolated simple complex algebraic point, so its coordinates are
algebraic. ∎

The Fourier signs select a chamber; no trigonometric values enter the
coefficients of the critical equations. The same existence argument
works for each of the \(2^m\) choices of signs for the free coordinate
orbits, while retaining (53.3). Thus there are at least \(2^m\)
distinct real algebraic solutions of the one-column problem below.
Selecting the particular chamber (53.2) is substantive.

## 53.2 Why the center solves a complete quadratic column

Write \(T^{-1}\) as a symmetric circulant with coefficients \(c_j\).
Differentiating (53.4) in a free coordinate orbit gives
\[
 n c_{a-h}+\frac{\gamma}{u_a}=0\qquad(2\le a<n).
 \tag{53.6}
\]
The orbit multiplicity, either 1 or 2, cancels. Define
\(v_a=Lc_{a-h}\). Equations (53.1) and (53.6) yield
\[
 v_a=\frac{\delta}{u_a}\quad(2\le a<n).
\]
The two exceptional values coincide by symmetry. The coefficient of
zero in \(TT^{-1}=I\) gives
\[
 -2c_h-\frac{(n-2)\gamma}{n}=1.
\]
Using \(L=(n-2)\delta+2\), it follows that
\[
 v_0=v_1=-1.
\]
Consequently inversion of the circulant is exactly the required
weighted reciprocal relation:
\[
 \boxed{\displaystyle
 \sum_a u_{a+g}v_a=L\delta_{g,0},\qquad
 v_0=v_1=-1,\quad v_a=\delta/u_a\ (a\ne0,1).
 }\tag{53.7}
\]

This reconstructs the phase variables explicitly. Put
\[
 R_a=\delta/u_a\quad(2\le a<n),\qquad
 W_1=\sqrt[n]{\delta\prod_{a=2}^{n-1}R_a}\ \text{(the real root)},
 \qquad W_a=\frac{W_1^a}{\prod_{j=2}^aR_j},\quad W_0=-1.
 \tag{53.8}
\]
Reflection of the \(R_a\) implies \(W_aW_{n-a}=\delta\).
Construct \(B\) and \(A\) as in Section 51. Then
\(B_{a,1}=u_a\), \(B_{1,a}=v_a\), and (53.7) proves
\[
 \sum_a A_{a+g,1}A_{1,a}=\delta_{g,0}\quad\text{for every }g.
 \tag{53.9}
\]
The exceptional zero column and all multiplicative symmetries also
hold. Every \(W_a\) is real and algebraic.

Moreover \(\operatorname{sgn}R_a=(-1)^a\). Taking signs in (53.8)
gives exactly
\[
 \operatorname{sgn}W_a=-(-1)^{a(a+n)/2}.
 \tag{53.10}
\]
Thus the signs proposed in Section 51 arise from this proved
construction. This does not by itself identify its magnitudes with
the double-sine product.

## 53.3 Computations, a counterexample, and the remaining implication

`hi_column_barrier.py` computes the unique center by Newton's method
with a line search inside the polytope. It then reconstructs the
entire matrix by (53.8). At orders \(3,7,11,19,25,31\), all
quadratics and all cross-free cubic orbits pass numerically; comparison
with the independently evaluated double sines agrees to their saved
60-digit precision. No arithmetic or analytic candidate is supplied
to the optimization.

Larger runs at \(n=51,101\) check **every quadratic**, but only eight
sampled cubics. At order 101 the maximum all-column quadratic residual
is below \(2.0\times10^{-126}\), and the sampled cubic residuals are
below \(1.8\times10^{-119}\), at 150-digit working precision.
These larger runs do not constitute complete cubic checks or exact
existence certificates.

One column alone does not force the other equations, even with the
formal norms and order-three symmetry. There is a small exact
counterexample at \(n=5\). In the row coordinates of Section 45 take
\[
 R_2=x,\qquad R_3=\frac{(2-\delta)x-1}{2},\qquad R_4=R_2,
 \qquad x^2+2\delta x+\delta=0.
\]
Its complete quadratic column \(h=1\) vanishes, whereas the four
scaled residuals with \(g,h\in\{2,3\}\) equal
\(-31\delta-4\ne0\). `hi_column_counterexample.py` verifies these
identities exactly over the quadratic extension. At \(\delta<0\)
both roots give real candidates, but neither has the coordinate signs
in (53.2). This is an algebraic ghost counterexample; physical unit
moduli are not asserted.

The resulting construction conjecture is now entirely algebraic and
variational:

> For every odd \(n\), the matrix reconstructed from the unique
> maximizer of (53.4) in \(\mathcal P_n\) satisfies all of (C).

This conjecture would imply categorification for all odd orders by
Section 52. Unlike the analytic approach, algebraicity and existence
of the candidate itself are already proved. The missing assertion is
that the chamber-selected center satisfies the additional equations.
Identifying it uniformly with the double-sine product would connect
the two routes, but is not a prerequisite for proving the variational
conjecture. A Hermitian positive-embedding argument would still be
needed for the stronger unitary conclusion.

**Update:** Section 93 proves this identification and all quadratic
identities of the double-sine candidate uniformly. The cubic assertion
in the construction conjecture remains unresolved.


# 54. The entire one-column algebra is finite, reduced, and real

Section 53 extends from the selected chamber to a classification of
**all complex one-column solutions** in the phase ansatz. In particular,
the isolatedness observed by elimination in small orders now has a
uniform proof. This does not prove that the full cubic locus is nonempty.

## 54.1 Positive logarithmic weights exclude every nonreal solution

Fix odd \(n\ge3\), keep the negative embedding \(\delta=-1/d\), and
set \(m=(n-1)/2\).
Allow the \(m\) free coordinates of Section 53 to be complex, subject
only to nonvanishing of those coordinates and of \(\det T\).
Factoring the circulant determinant gives the master function
\[
 \mathcal F=\sum_{k=0}^{m}\mu_k\log\lambda_k
       +\gamma\sum_{a=2}^{h}\nu_a\log u_a,
 \quad \mu_0=1,\quad\mu_k=2\ (k>0),
 \quad\nu_h=1,\quad\nu_a=2\ (a<h).
 \tag{54.1}
\]
Only its logarithmic derivative is used over \(\mathbb C\); branches
of the logarithms do not affect it. All weights are strictly positive
real numbers, and all linear forms have real coefficients.

The following elementary argument is the positive-weight master-function
principle; compare [Varchenko, *Critical points of the product of powers
of linear functions*, Theorem 1.2.1](https://www.numdam.org/item/CM_1995__97_3_385_0.pdf).
For real affine forms \(f_j(z)=b_j+a_j\cdot z\) with positive weights
\(w_j\), a complex critical point \(z=x+iy\) satisfies
\[
 0=y\cdot\operatorname{Im}\sum_j\frac{w_j a_j}{f_j(z)}
   =-\sum_j\frac{w_j(a_j\cdot y)^2}{|f_j(z)|^2}.
 \tag{54.2}
\]
Thus \(a_j\cdot y=0\) for every \(j\). The coordinate forms alone
span the dual space, so \(y=0\). Every critical point is real.
At a real point the Hessian is
\[
 -\sum_j\frac{w_j a_j a_j^{\mathsf T}}{f_j(x)^2},
 \tag{54.3}
\]
which is negative definite. Hence every critical point is simple.

Each bounded chamber of the real hyperplane complement has exactly one
critical point, by the same strict-concavity and boundary argument as
in Section 53. An unbounded chamber has none: a nonzero recession
direction \(v\) makes all ratios \((a_j\cdot v)/f_j(x)\) nonnegative,
and at least one is positive. The directional derivative of
\(\mathcal F\) is therefore strictly positive throughout that chamber.

There are finitely many chambers. Consequently the critical scheme is
finite and reduced, and its points are in bijection with the bounded
chambers. The argument applies at **every odd order**, including
composites.

This is exactly the one-column scheme, not an unrelated critical
subsystem. The full column equations give
\(TV=LI\), where \(V\) is the centered circulant of the reciprocal
row. Thus \(T\) is invertible and its inverse yields (53.6).
Conversely, (53.6) gives \(TV=LI\), including both exceptional
entries, by the trace computation in Section 53. These implications
use identities in the localized coordinate ring, so they also identify
the schemes and exclude hidden multiplicities.

## 54.2 An exact formula at every odd prime

Let \(b_n\) denote the number of one-column solutions modulo cyclic
character gauge. The preceding theorem identifies it with the number
of bounded chambers of \(2m+1\) affine hyperplanes in \(\mathbb R^m\).
In particular,
\[
 2^m\le b_n\le\binom{2m}{m}.
 \tag{54.4}
\]
The lower bound comes from the \(2^m\) chambers constructed in
Section 53. The upper bound is the general-position bound for bounded
regions of an affine arrangement.

**Theorem.** For every odd prime \(p\),
\[
 \boxed{\displaystyle b_p=\binom{p-1}{(p-1)/2}.}\tag{54.5}
\]

To prove this, use centered homogeneous coordinates
\(x_0,\ldots,x_m\). The arrangement before setting \(x_m=-1\)
consists of the \(m+1\) coordinate hyperplanes and the \(m+1\)
Fourier hyperplanes. Up to nonzero column scalings, the latter have
coefficient matrix
\[
 C_{k,j}=\cos(2\pi kj/p),\qquad 0\le k,j\le m.
\]
Every square minor of this matrix is nonzero by the discrete-cosine
version of Chebotarev's theorem: [Garcia–Karaali–Katz, *An improved
uncertainty principle for functions with symmetry*, Theorem 1.2](https://arxiv.org/abs/1807.07648).
Thus every \((m+1)\)-column minor of \([I\mid C]\) is nonzero.
The central arrangement is in general position, and its decone has
\(2m+1\) affine hyperplanes in general position. Its characteristic
polynomial is
\[
 \chi_n(t)=\sum_{j=0}^{m}(-1)^j\binom{2m+1}{j}t^{m-j}.
\]
The bounded-region formula \(b_n=(-1)^m\chi_n(1)\) and the elementary
alternating-binomial identity give (54.5). The region-count formula
is Zaslavsky's; see [Stanley's lectures on hyperplane arrangements](https://ocw.mit.edu/courses/18-315-combinatorial-theory-hyperplane-arrangements-fall-2004/pages/lecture-notes/).

For composite \(n\), the cosine matrix has vanishing minors, and the
prime formula need not hold. Exact ranks over \(\mathbb Q(\zeta_n)\)
give the following counts:

| \(n\) | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
|---|---:|---:|---:|---:|---:|---:|---:|
| \(b_n\) | 2 | 6 | 20 | 58 | 252 | 924 | 2492 |

`hi_column_arrangement.gp` computes the central characteristic
polynomial directly by its subset-rank formula, then divides by
\(t-1\). For example,
\[
 \chi_9(t)=t^4-9t^3+36t^2-83t+113,
 \qquad b_9=58,
\]
so the general-position upper bound 70 is strict. The counts and all
rank decisions in this calculation are exact.

## 54.3 Consequences for the remaining existence problem

Let \(K=\mathbb Q(\delta)\), and let \(\mathcal A_n\) be the
localized coordinate algebra of one full quadratic column in the row
or column coordinates. Then
\[
 \boxed{\displaystyle
 \mathcal A_n\text{ is a finite product of number fields},\qquad
 \dim_K\mathcal A_n=b_n.}\tag{54.6}
\]
Each factor has only real embeddings above the negative embedding of
\(K\). Its embeddings above the positive place may be complex.
The algebra and its reducedness are defined over \(K\), so the same
scheme length and simplicity hold after changing the dimension
embedding.

All remaining quadratic and cubic residuals are elements of
\(\mathcal A_n\): the character gauge cancels from \(B\), and the
row formulas express its entries rationally in these coordinates.
Adjoining more equations therefore retains some field factors and
discards others. In particular, within the phase ansatz, both the full
quadratic scheme and the full cubic scheme are finite and reduced
for **every odd \(n\)**, even though they may a priori be empty.
For the cubic scheme use (52.2), which puts the one-column equations
in the full cubic ideal.

Before quotienting by the character gauge, the one-column phase
scheme has length \(n b_n\). Indeed, adjoining \(W_1\) by (53.8)
is a degree-\(n\) finite étale extension: its right side is a unit and
\(n\ne0\). Over the negative embedding each character orbit has
exactly one representative with all \(W_a\) real, because \(n\) is
odd.

This supplies a finite, nondegenerate algebraic setting for the
variational conjecture at every order. The canonical chamber selects
one of its real points. Infinitude would follow if its field factor
survives all cubic equations for infinitely many orders. Neither the
chamber count nor reducedness proves that survival: at order 5 only
four of the six one-column points survive the full quadratic system,
as Sections 43 and 53 demonstrate.



# 55. A scalar completion condition and its prime-order field consequence

A single scalar condition now separates the tested genuine candidates
from the additional one-column solutions. Its sufficiency is proved
exactly at orders 3, 5, and 7, and it has a uniform arithmetic
consequence at every odd prime. Its sufficiency in unbounded order and
its validity at the canonical center remain conjectural.

**Update:** Section 94.4 proves its validity at the canonical center
uniformly. Its sufficiency for the cubic equations at unbounded orders
remains unresolved, as does the more specific period-40 formula below.

## 55.1 The condition depends on the phase lift

For reconstructed phases \(W\), define
\[
 S(W)=\frac{\sum_{a\in\mathbb Z_n}W_a}{\delta-1},\qquad
 T(A)=\sum_{a\in\mathbb Z_n}A_{a,2a}=\operatorname{Tr}\mathcal R.
\]
The last equality follows directly from the definition of \(\mathcal R\)
in Section 50; it does not require the quadratic equations. Consider
\[
 \boxed{S(W)^2+T(A)=2.}\tag{55.1}
\]
After clearing its nonzero constant denominator, this is
\[
 H(W)=\left(\sum_a W_a\right)^2
       +(\delta-1)\sum_aB_{a,2a}-2(\delta-1)^2=0.
 \tag{55.2}
\]
This involves \(\operatorname{Tr}\mathcal R\), not the fifth-power
trace in Section 50. No implication from that section to (55.1) is
being asserted.

Although \(T(A)\) is invariant under cyclic character gauge,
\(S(W)\) generally is not. Thus (55.1) is imposed on the phase
cover of the one-column algebra. At the negative dimension embedding,
requiring every \(W_a\) to be real selects exactly one lift of each
row point, as proved in Section 54.

**Theorem (exact finite computation).** At \(n=3,5,7\), the phase
norms, reflection and reconstruction identities, one complete quadratic
column, and (55.1) imply every quadratic and cubic equation.
The scalar-constrained phase schemes have respective lengths
\(2,4,6\) over \(K=\mathbb Q(\delta)\).

The proof uses a finite-algebra dimension comparison, avoiding a large
direct elimination. Let \(E\) be the one-column phase algebra and
\(M_H:E\to E\) multiplication by (55.2), after multiplication by a
Laurent monomial unit to obtain a polynomial. Then
\[
 \dim_K E/(H)=\dim_K E-\operatorname{rank}_K M_H.
 \tag{55.3}
\]
At a prime where every entry of this exact matrix is integral, its
rank can only decrease after reduction. This gives an upper bound on
\(\dim_K E/(H)\). An independent exact Gröbner computation adjoins
all of Q as well and gives a lower bound, because that quotient is a
quotient of \(E/(H)\).

| \(n\) | \(\dim_K E\) | Exact modular rank of \(M_H\) | Exact length after adjoining all Q |
|---|---:|---:|---:|
| 3 | 6 | 4 | 2 |
| 5 | 30 | 26 | 4 |
| 7 | 140 | 134 | 6 |

In each case the upper and lower dimension bounds coincide. Therefore
adjoining the remaining quadratics changes no ideal. Exact cubic
reductions in that same quotient vanish. The checks use all cross-free
beta orbits without scalar quotienting, and the collision identities
of Section 34 cover the other cubics.

`hi_column_trace_exact.py` regenerates the equations and the exact
multiplication matrix, checks integrality of every reduced coefficient,
and runs both sides of this comparison. The recorded prime is 32003,
with the respective images of \(\delta\) equal to 20720, 19299, and
7268. No finite-field dimension is silently treated as a
characteristic-zero equality: (55.3) and the matching exact lower
bound supply that equality. These certificates use no HI seeds or
numerical root recognition.

## 55.2 The scalar equation forces the one-root property at primes

**Proposition.** Let \(n=p\) be an odd prime. Take a real phase lift
at the negative embedding, reconstructed as in (53.8), and let
\[
 E=K(R_2,\ldots,R_{p-1})\subset\mathbb R
\]
be its row field. If (55.1) holds, then
\[
 \boxed{W_1,\ldots,W_{p-1}\in E.}\tag{55.4}
\]
The proposition does not need Q or C beyond any assumptions used to
construct the row; the reconstruction and scalar equation suffice.

**Proof.** Put \(x=W_1\) and
\(P_a=\prod_{j=2}^aR_j\), with \(P_1=1\). Then
\[
 x^p=\delta P_{p-1}\in E^\times,
 \qquad W_a=x^a/P_a\quad(1\le a<p).
\]
For a real \(x\) with \(x^p\in E\), the degree \([E(x):E]\) is
1 or \(p\). Indeed, if its minimal polynomial has degree
\(1\le k<p\), its constant coefficient is
\((-1)^k x^k\zeta_p^j\in E\subset\mathbb R\). Since \(x\) is real
and \(p\) odd, \(\zeta_p^j=1\); hence \(x^k\in E\).
Bezout's identity for \(k,p\) then gives \(x\in E\).

Suppose instead that \([E(x):E]=p\). All entries of \(A\), and
therefore \(T(A)\), lie in \(E\). Equation (55.1) implies that
\(s=\sum_aW_a\) has \(s^2\in E\). The degree \([E(s):E]\)
divides both 2 and \(p\), so \(s\in E\). But
\[
 s=-1+\sum_{a=1}^{p-1}x^a/P_a
\]
is a nonconstant linear combination of the independent basis
\(1,x,\ldots,x^{p-1}\), with all displayed coefficients nonzero.
This is a contradiction. Thus \(x\in E\), and the reconstruction
gives all the other phases in \(E\). ∎

This links the scalar condition to the arithmetic one-root requirement
in Sections 38 and 44. It does not establish that the row field is
abelian or has the desired ray conductor, nor does the one-root
conclusion alone supply the remaining Izumi equations.

## 55.3 The canonical trace has a conjectural period-40 formula

For the unique canonical center of Section 53, the numerical data
suggest the particularly small trace
\[
 \boxed{\displaystyle
 S(W)=\eta_n:=
 \sqrt2\sin\frac{\pi n}{4}\,
 \frac{\sin(\pi n/5)}{\sin(2\pi/5)},\qquad
 T(A)=2-\eta_n^2.}\tag{55.5}
\]
The first expression is periodic modulo 40. For odd \(n\), its
values belong to
\[
 \{0,\,\pm1,\,\pm(\sqrt5-1)/2\}.
\]
Consequently the proposed operator trace is 2 when \(5\mid n\),
1 when \(n\equiv\pm2\pmod5\), and \((1+\sqrt5)/2\) when
\(n\equiv\pm1\pmod5\).

`hi_column_trace.py` computes the canonical center without imposing
either trace identity. Its saved tests include orders 51 and 79 as
well as the smaller orders. At order 79, with 120-digit working
precision, the scalar defect is below \(9\times10^{-111}\), and
the first equality of (55.5) agrees within
\(3\times10^{-115}\). These are numerical observations.

The script also scans all coordinate-sign choices inside the fixed
Fourier-sign chamber (53.3) for \(n=5,7,9,11,13,15,17\):
508 centers in total. Exactly 24 pass the full quadratic tests
numerically, and these are exactly the 24 passing (55.1); no
false positives or false negatives appear in this scan. It is not
an enumeration of every Fourier chamber. Equation (55.5) is specific
to the canonical center: other full-Q candidates can have different
trace values, including \(S(W)=2\) in the secondary order-11 branch.

The proposed route to infinitude now has two explicit unresolved
assertions: prove scalar completion from one column in unbounded
orders, and prove (55.1) at the canonical center in those orders.
The stronger trace formula (55.5) would give the latter. Only the
finite scalar-completion theorem and the uniform prime-order field
consequence above are proved here. Infinitude remains unproved.


---

# 56. The two-value quadratic-character ansatz stops at orders 3 and 11

The secondary order-11 branch in Section 55 has only two phase values.
That feature suggests a possible uniform construction, but the quadratic
equations themselves give an exact obstruction to extending it.

**Theorem.** Let \(p\equiv3\pmod4\) be prime, let
\(\delta^2=p\delta+1\), and write \(\chi\) for the quadratic character
of \(\mathbb F_p\), with \(\chi(0)=0\). Suppose
\[
 W_0=-1,\qquad W_j=a+b\chi(j)\quad(j\ne0),\qquad
 a^2-b^2=\delta.
 \tag{56.1}
\]
If every quadratic equation holds, then \(p=3\) or \(p=11\).
At the negative embedding, the real solutions in this ansatz are precisely
\[
 \begin{array}{c|c|c}
 p&a&b^2\\ \hline
 3&\delta/2&(1-\delta)/4\\
 11&(2\delta-1)/10&(1-12\delta)/20
 \end{array}
 \tag{56.2}
\]
with either sign of \(b\). They satisfy all cubics as well.

The obstruction uses only two necessary consequences of Q; the scalar
completion conjecture is not assumed. Put \(e=\chi(2)\) and
\[
 Q(g,h)=\sum_j W_jW_{h-j}W_{-j-g}W_{j+g-h}.
\]
The diagonal equation \(Q(1,1)=0\), after substituting
\(b^2=a^2-\delta\), is
\[
 D_e=(4e+2p-2)a^4+(4e-4)a^3
 -\delta(4e+p+1)a^2+\delta(2-4e)a+\delta=0.
 \tag{56.3}
\]
This follows by expanding
\(W_j=a+b\chi(j)-(1+a)\mathbf1_{j=0}\), treating the repeated
root at zero and the simple roots at \(\pm1\) separately. The terms
odd in \(b\) cancel; the usual two-character sum gives the displayed
coefficients.

A second necessary equation comes from summing Q over its first index.
For \(s\ne0\), direct convolution gives
\[
 (W*W)(s)=(p-1)a^2-2a-\delta-2b(1+a)\chi(s).
\]
Consequently
\[
 \sum_g Q(g,1)=(W*W)(1)(W*W)(-1),\qquad
 Q(0,1)=2\delta+(p-2)\delta^2.
\]
All nonzero-index quadratics therefore force
\[
 E=\big((p-1)a^2-2a-\delta\big)^2
   -4(a^2-\delta)(a+1)^2-2\delta-(p-2)\delta^2=0.
 \tag{56.4}
\]
Eliminating \(a\) and then \(\delta\) gives the polynomial identities
\[
 \begin{aligned}
 \operatorname{Res}_{\delta}\!left(
  \operatorname{Res}_a(E,D_{-1}),\delta^2-p\delta-1\right)
  &=p^6(p-11)^2(p-3)^{14},\\
 \operatorname{Res}_{\delta}\!left(
  \operatorname{Res}_a(E,D_{+1}),\delta^2-p\delta-1\right)
  &=p^6(p+1)^{12}
    (p^4-76p^3+406p^2+532p-4047).
 \end{aligned}\tag{56.5}
\]
The first expression permits only 3 and 11. A prime root of the quartic
in the second expression must divide \(4047=3\cdot19\cdot71\).
None of these three primes is a root, so that case is impossible.

At \(p=3\), the common equation factors as
\((a-\delta/2)(a^2+\delta a/2+1/4)=0\); the quadratic factor
has no real root when \(\delta<0\). At \(p=11\), the monic gcd
of (56.3) and (56.4) over \(\mathbb Q(\delta)\) is
\(a-(2\delta-1)/10\). The norm condition then gives (56.2).
For \(p\equiv1\pmod4\), a real ansatz (56.1) at \(\delta<0\)
is already impossible, since \(\chi(-1)=1\) would require a real
phase square to equal \(\delta\).

`hi_paley_obstruction.py` verifies the resultants as identities with
symbolic \(p\), checks the character expansions off solution, and
checks every Q and C position in the two remaining quartic number
fields. Thus the finite cases have exact certificates. The theorem
excludes only the two-value quadratic-character construction; it places
no upper bound on orders admitting general HI solutions.


---

# 57. Explicit commuting matrices and scalar completion at orders 11 and 13

The one-column algebra now has explicit multiplication matrices at every
odd prime, obtained directly from the hyperplane arrangement. This avoids
eliminating the one-column equations. Applying these matrices extends the
exact scalar-completion theorem of Section 55 to orders 11 and 13.

**Theorem.** At each \(n\in\{3,5,7,11,13\}\), the phase norms,
reflection and reconstruction identities, one complete quadratic column,
and \(H=0\) imply every quadratic and cubic equation. The respective
scalar-constrained phase lengths over \(\mathbb Q(\delta)\) are
\(2,4,6,12,12\).

The matrix construction below is uniform in the prime. Nonvanishing of
the scalar kernel in unbounded orders, and scalar completion in those
orders, remain unproved.

## 57.1 Multiplication from the hyperplane circuits

Let \(p=2m+1\) be prime. Use the centered coordinates of Section 54,
with \(x_m=-1\), and put \(\mu_0=1\), \(\mu_j=2\) for \(j>0\).
The \(p\) affine forms and their weights are
\[
 \begin{array}{c|c}
 f&\alpha\\ \hline
 x_j\quad(0\le j<m)&\gamma\mu_j\\
 \lambda_k=\displaystyle\sum_{j=0}^{m-1}
   \mu_j\cos(2\pi kj/p)x_j-2\cos(2\pi km/p)
   \quad(0\le k\le m)&\mu_k
 \end{array}
 \tag{57.1}
\]
Index these forms by \(1,\ldots,p\), and write
\(f_i=z_i+\beta_i\cdot x\). Work over
\(F=\mathbb Q(\delta,\zeta_p+\zeta_p^{-1})\).
The minor theorem used in Section 54 ensures general position of both
the normals and the affine arrangement.

Here is the circuit presentation specialized to this arrangement. Take
oriented symbols \(e_I\) for \(m\)-element subsets, with relations
\(\sum_j e_{j,J}=0\) for every \((m-1)\)-element subset \(J\).
The symbols with \(I\subset\{1,\ldots,p-1\}\) form a basis of size
\(b_p=\binom{p-1}{m}\). For each \((m+1)\)-subset
\(C=(c_0,\ldots,c_m)\), choose nonzero cofactors \(\ell^C_{c_r}\)
so that \(\sum_{i\in C}\ell^C_i\beta_i=0\), and set
\(f_C=\sum_{i\in C}\ell^C_i z_i\ne0\). Define
\[
 L_C e_{C\setminus c_r}
   =(-1)^r\sum_{s=0}^{m}(-1)^s\alpha_{c_s}e_{C\setminus c_s},
 \qquad L_C e_I=0\quad(I\not\subset C),
\]
and
\[
 \boxed{K_i=\sum_{C\ni i}\frac{\ell_i^C}{f_C}L_C.}
 \tag{57.2}
\]
These are multiplication by \(\alpha_i/f_i\) in the critical algebra.
The identification follows from [Varchenko, *Critical set of the master
function and characteristic variety of the associated Gauss–Manin
differential equations*, Corollaries 2.17 and 3.8](https://armj.math.stonybrook.edu/html-articles/Files-2015-2024/15-20/).
The marked element corresponding to \(e_I\) is
\(\det(\beta_i)_{i\in I}\prod_{i\in I}\alpha_i/f_i\).
The positive weights satisfy the required unbalanced-weight condition.

For a coordinate form \(f_i=x_j\), this immediately gives
\[
 M_{x_j}=\alpha_iK_i^{-1},\qquad
 M_{\delta/x_j}=\frac{\delta}{\alpha_i}K_i.
 \tag{57.3}
\]
Reflection converts these into every row coordinate \(R_a\).
Thus reconstruction and the scalar polynomial H can be evaluated in
explicit commuting matrices, without any critical-point roots or HI seeds.

## 57.2 An integral matrix model gives a rigorous upper bound

Choose a rational prime \(q\equiv1\pmod p\) at which
\(p^2+4\) is a nonzero square. Choose images of \(\zeta_p\) and
\(\delta\) in \(\mathbb F_q\). Check that all normal minors,
circuit constants, and weights appearing in (57.2) stay nonzero.
The resulting matrices are reductions of the characteristic-zero
matrices in a free local lattice. The coordinate multiplication matrices
and the Laurent inverses needed for H are also checked to be integral
by verifying invertibility of their reductions.

Adjoin the reconstruction root as in Section 55:
\[
 \mathcal E=E[X]/\left(X^p-\delta\prod_{a=2}^{p-1}R_a\right),
 \qquad \dim_F\mathcal E=p\binom{p-1}{m},
 \tag{57.4}
\]
where \(E\) is the row critical algebra. Multiplication by H on
this regular module has an integral matrix. Rank specialization therefore
gives
\[
 \dim_F\mathcal E/(H)
 \ \le\ \dim_{\mathbb F_q}\overline{\mathcal E}/(\overline H).
 \tag{57.5}
\]
Extending the characteristic-zero coefficient field from
\(\mathbb Q(\delta)\) to \(F\) does not change this dimension.

The program computes the right side efficiently. A linear combination
of the row matrices has a cyclic vector; its exact Krylov basis gives
\(\overline E=\mathbb F_q[t]/(f(t))\). The program checks that f
is squarefree and factors it exactly. In each resulting finite field,
the degree of
\[
 \gcd\left(X^p-\delta\prod R_a,\,\overline H(X)\right)
 \tag{57.6}
\]
counts the surviving phase roots, with the degree of that finite field
as multiplicity. This computes a quotient dimension, not a count of
only the \(\mathbb F_q\)-rational points.

| \(p\) | Row dimension | Phase dimension | \(q\) | Image of \(\delta\) | Modular H-quotient dimension |
|---|---:|---:|---:|---:|---:|
| 3 | 2 | 6 | 32029 | 16171 | 2 |
| 5 | 6 | 30 | 32051 | 648 | 4 |
| 7 | 20 | 140 | 32089 | 16285 | 6 |
| 11 | 252 | 2772 | 32099 | 4506 | 12 |
| 13 | 924 | 12012 | 32059 | 1153 | 12 |

At 11 the selected row-field factor degrees are 2 and 10; at 13 there
is one factor of degree 12. Each has one surviving phase root over its
row field. These finite-field statements alone would not prove the
characteristic-zero theorem; matching lower bounds are essential.

## 57.3 Matching exact lower bounds

At 11, the previously certified full-Q algebra of Section 45 has
dimension 12 and satisfies every C. Exact FGLM converts its saved basis
to a primitive-coordinate presentation. Over \(\mathbb Q(\delta)\),
the primitive polynomial factors into degrees 2 and 10. In each field,
the characteristic-zero version of (57.6) has degree one. Thus the
full-Q/H phase quotient has dimension 12, matching the upper bound.

At 13, the construction of Section 28 produces a full Q/C certificate
in a field of absolute degree 24. Exact reconstruction finds a unique
phase root in that field and verifies \(H=0\). A row coordinate has
absolute degree 24, so its 12 conjugates over \(\mathbb Q(\delta)\)
are distinct. They supply 12 distinct points of the full-C/H locus,
again matching the upper bound. The rank comparison therefore proves
scalar completion here without computing the full order-13 Q ideal.

`hi_column_circuits.py` regenerates the circuit matrices, verifies
their critical relations, commutativity and complete quadratic column,
computes the modular bounds, and supplies the exact lower bounds.
At 11 it uses the already verified `hi_row11_basis.txt`; at 13 it reruns
the full exact construction and cubic certificate. The resulting
theorems establish finite scalar completion, not the canonical trace
identity or infinitude.


---

# 58. Positive-characteristic certificates and a Frobenius construction

There is a second use for finite-field calculations, distinct from the
specialization upper bounds in Section 57. A **complete cubic solution**
in a suitable positive characteristic already implies existence over
\(\mathbb C\), by algebraic reconstruction followed by categorical lifting.
No characteristic-zero lower bound is needed for this existence statement.
This section proves that implication, specializes it to characteristic 2
at every odd order, and gives new complete certificates at order 27.
It does **not** establish nonemptiness for unbounded orders.

**Prior work.** The finite-field/lifting strategy is also explicitly
reported in joint work of T. Gannon, A. Schopieray and H. Yadav,
*Haagerup–Izumi categories using the lifting technique*, listed as
in progress in Yadav's research description. That account reports
models over a positive-density set of prime fields for odd orders
through 19; it does not report unbounded-order existence.
[Yadav, “Exotic fusion categories in characteristic p”](https://sites.ualberta.ca/~hyadav3/research-description.html).
The reconstruction argument and certificate calculations below are
self-contained here; no unpublished result from that project is used.

## 58.1 Reconstruction and lifting from a complete finite-field solution

**Theorem.** Let \(n\ge3\) be odd and let \(k\) be an algebraically
closed field of characteristic \(\ell>0\), with
\(\ell\nmid n(n^2+4)\). Suppose \(\delta^2=n\delta+1\) and an
\(n\times n\) matrix \(A\) over \(k\) has the exceptional row,
column and order-three symmetry of Section 52, and satisfies every
cubic equation \(C(g,h,k,l)=0\). Then there is a fusion category over
\(\mathbb C\) with the cyclic HI fusion rules at order \(n\).

**Proof.** First, \(\delta\ne0,1\): the first assertion follows from
its quadratic equation, and \(\delta=1\) would force \(n=0\) in
\(k\). The polynomial residual identities (52.1)–(52.2) therefore
supply all quadratic and quartic reconstruction equations. The
exceptional column also has sum \(-\delta^{-1}\).

Here is the characteristic check for the reconstruction step. Choose
\(b\in k^\times\) with \(b^2=\delta^{-1}\). In the Leavitt algebra
over \(k\), use generators \(s,s',t_g,t'_g\) and relations
\[
 s's=1,\quad t'_g t_h=\delta_{g,h},\quad s't_g=t'_g s=0,
 \qquad ss'+\sum_g t_g t'_g=1.
\]
Define
\[
\begin{aligned}
 \rho(s)&=\delta^{-1}s+b\sum_g t_g t_g, &
 \rho(s')&=\delta^{-1}s'+b\sum_g t'_g t'_g,\\
 \rho(t_g)&=b s t'_{-g}+t_{-g}ss'
       +\sum_{h,j}A_{h+g,j+g}t_h t_{g+h+j}t'_j,\\
 \rho(t'_g)&=b t_{-g}s'+ss't'_{-g}
       +\sum_{h,j}A_{j+g,h+g}t_j t'_{g+h+j}t'_h.
\end{aligned}
\tag{58.1}
\]
Let \(\alpha_g\) fix \(s,s'\) and translate each \(t_h,t'_h\)
by \(h\mapsto h+2g\). These are the \(\omega=1\) reconstruction
formulas. Their verification is by polynomial coefficient comparison:
they preserve the Leavitt relations, satisfy
\(\alpha_g\rho=\rho\alpha_{-g}\), and give
\[
 \rho^2(x)=sxs'+\sum_g t_g\alpha_g\rho(x)t'_g.
 \tag{58.2}
\]
In particular the occurrence of the integer 2 in the label translation
uses that the **group order is odd**; it does not require division by
2 in the coefficient field.

For completeness, the simplicity argument is also valid in this
characteristic. Reduced-word leading terms show that the simultaneous
centralizer of \(\rho(s),\rho(s')\) consists of scalars. Comparing
\(\rho(t_{-2g})\) distinguishes the \(\alpha_g\rho\). The analogous
centralizer of \(s,s'\) distinguishes the \(\alpha_g\). A nonzero
intertwiner between the two types would have an uncancelled leading
coefficient proportional to \(1-\delta^{-1}\), which is nonzero.
Thus the simple objects have exactly the required Hom spaces over
\(k\). Iterating (58.2) gives matrix-unit bases for all Hom spaces;
closing under finite sums and idempotents gives a semisimple category
with exactly the \(2n\) indicated simples. Evaluation and coevaluation
for \(\rho\) are \(s'/b\) and \(s/b\). The duality calculations on
these generators give the identity double dual, and dimensions
\(1\) and \(\delta\). They use linear maps and coefficient identities,
with no complex conjugation or positivity assumption.
This verifies the extension to \(k\) of the proof of
[Evans–Gannon, Theorem 2(a) and Proposition 1](https://arxiv.org/pdf/1506.03546);
the statement in that paper itself is over \(\mathbb C\).

The resulting spherical category has global dimension
\[
 D=n(1+\delta^2),\qquad
 (1+\delta^2)^2=(n^2+4)\delta^2.
 \tag{58.3}
\]
Our characteristic assumption makes \(D\ne0\). The nondegenerate
category therefore lifts to the Witt ring \(W(k)\), preserving its
fusion rules, by [Etingof–Nikshych–Ostrik, Theorem 9.3](https://annals.math.princeton.edu/wp-content/uploads/annals-v162-n2-p01.pdf).
Passing to the generic fiber gives the required fusion rules over a
characteristic-zero field. The finite associator, unit, rigidity and
invertibility equations, in fixed bases, consequently have a solution
in characteristic zero. The weak Nullstellensatz supplies a solution
over \(\overline{\mathbb Q}\), hence over \(\mathbb C\). ∎

This conclusion is categorification, without a unitarity assertion.
It also does not assert that the prescribed finite-field phase gauge
lifts entry by entry. For existence, lifting the fusion category is
sufficient. A nonzero modular H-quotient **without** a complete cubic
certificate still supplies only the upper bound of Section 57.

The standalone `hi_finite_field_certificate.py --verify` accepts a
small JSON file specifying a finite field, \(\delta\), and a reflected
row \(R\). It checks irreducibility of the field polynomial, the
characteristic and dimension hypotheses, the row normalization, and
then reconstructs \(B\) by prefix products as in Section 43. It checks
the symmetry, linear sum, **every** Q and **every** C independently.
Exporting the scalar-selected row factors of Section 57 gives complete
finite-field certificates at 3, 5, 7, 11 and 13. The program does not
read characteristic-zero HI seeds for that construction.

## 58.2 A fixed characteristic works at every odd order

Take \(\ell=2\), put
\(\mathbb F_4=\mathbb F_2[\omega]/(\omega^2+\omega+1)\), and set
\(\delta=\omega\). For every odd \(n\),
\[
 \delta^2=n\delta+1,\qquad n(1+\delta^2)=\omega\ne0.
 \tag{58.4}
\]
Thus characteristic 2 is admissible at **all** the target orders.
Given phases
\[
 W_0=1,\qquad W_aW_{-a}=\omega\quad(a\ne0),
 \tag{58.5}
\]
the normalized matrix becomes
\[
 A_{0,0}=\omega^2,\qquad
 A_{g,0}=A_{0,g}=A_{g,g}=\omega\quad(g\ne0),\qquad
 A_{g,h}=\omega\frac{W_gW_{h-g}}{W_h}
 \quad(gh(g-h)\ne0).
 \tag{58.6}
\]
Its full cubic target is simply
\[
 \boxed{\sum_m A_{m,g+h}A_{g,m+k}A_{h,m+l}
       =A_{g+l,k}A_{h+k,l}+\omega^2\delta_{g,0}\delta_{h,0}.}
 \tag{58.7}
\]
An infinite set of odd orders with solutions to this finite-field
identity would prove the requested complex infinitude.

One constraint is automatic in a natural Frobenius ansatz.

**Lemma.** In characteristic 2, (58.5) together with
\[
 W_{2a}=W_a^4
 \tag{58.8}
\]
implies the scalar equation H of Section 55, without assuming any Q.

**Proof.** As \(\delta-1=\omega^2\), the scalar is
\[
 H=\left(\sum_a W_a\right)^2+\omega^2\sum_a B_{a,2a}.
\]
The origin contributes \(1+\omega^2B_{0,0}=1+\omega^3=0\).
For \(a\ne0\), (58.8) gives
\[
 W_a^2+\omega^2B_{a,2a}
 =W_a^2+\frac{\omega^2}{W_a^2}
 =W_a^2+W_{-a}^2.
\]
Summing over the inverse pairs proves \(H=0\). ∎

This does not prove the quadratic or cubic equations. For example,
the constant choice \(W_a=\omega^2\) for all \(a\ne0\) satisfies
(58.5) and (58.8), and hence H, but fails the first diagonal phase Q.
Its residual is \(\omega\) at every odd \(n\): the terms at
\(m=0,1,-1\) are \(\omega,1,1\), and the remaining \(n-3\)
terms, all \(\omega^2\), cancel in characteristic 2.

## 58.3 An exact search along the infinite family \(n=3^k\)

The integer 2 generates \((\mathbb Z/3^j\mathbb Z)^\times\) for
every \(j\ge1\). Consequently the nonzero labels at \(n=3^k\)
split into \(k\) doubling orbits, represented by \(3^s\),
\(0\le s<k\). Their lengths are
\[
 r_s=2\cdot3^{k-s-1}.
\]
Put \(N_s=4^{r_s/2}+1\), and choose a primitive \(N_0\)-th root
\(\xi\) in \(\mathbb F_{4^{r_0}}\). Since \(N_s\mid N_0\),
every solution of (58.5)–(58.8) is specified uniquely by
\[
 \begin{aligned}
 0\le i_s<N_s,\qquad
 W_{3^s}&=\omega^2\xi^{(N_0/N_s)i_s},\\
 W_{2^j3^s}&=W_{3^s}^{4^j}\quad(0\le j<r_s).
 \end{aligned}
 \tag{58.9}
\]
Indeed closure gives \(W_{3^s}\in\mathbb F_{4^{r_s}}\), while
\(2^{r_s/2}\equiv-1\pmod{3^{k-s}}\) turns inverse symmetry into
\(W_{3^s}^{1+4^{r_s/2}}=\omega\). Its solutions are exactly the
coset \(\omega^2\mu_{N_s}\) in (58.9). There is no unknown field
or square-root selection in this parametrization.

Frobenius covariance reduces all the nonexceptional quadratic columns
to \(h=3^s\). We therefore filter (58.9) by
\[
 \sum_{m\in\mathbb Z_n}
 W_mW_{h-m}W_{-m-g}W_{m+g-h}=0,
 \qquad 0<g<n,\quad h\in\{1,3,\ldots,3^{k-1}\}.
 \tag{58.10}
\]
Every term is \(\omega^e\xi^{L(i_0,\ldots,i_{k-1})}\), with an
explicit linear exponent. Binary-field addition is XOR, so tables of
\(\omega^e\xi^a\) make exhaustive search inexpensive at the first
three orders. This is an exact finite algorithm, not an asymptotic
nonemptiness argument.

| \(n\) | Ambient field | Number of phase candidates | First diagonal Q survivors | Full-Q survivors | Frobenius orbit lengths |
|---:|---|---:|---:|---:|---|
| 3 | \(\mathbb F_{2^4}\) | 5 | 2 | 2 | 2 |
| 9 | \(\mathbb F_{2^{12}}\) | 325 | 24 | 12 | 6, 6 |
| 27 | \(\mathbb F_{2^{36}}\) | 85,197,125 | 1,350 | 54 | 18, 18, 18 |

**Every orbit in this table passes every cubic equation.** The search
program `hi_char2_frobenius.py` exports one row certificate per orbit,
then invokes the independent verifier. In particular, each of the
three order-27 files passes all 729 Q and all 531,441 C. The theorem
in Section 58.1 therefore establishes cyclic HI categorification at
order 27 without numerical HI seeds, Stark polynomials, or recognition
of characteristic-zero algebraic numbers.

For a compact explicit order-27 specification, take
\[
 \mathbb F_{2^{36}}=\mathbb F_2[z]/(1+z+\cdots+z^{36}).
\]
The modulus is irreducible, since 2 has order 36 modulo 37. Encode
\(\sum_j c_jz^j\) by \(\sum_j c_j2^j\). In this encoding use
\[
 \omega=41370444133,\qquad \xi=25668351056,
\]
where \(\xi\) has order \(262145=5\cdot13\cdot37\cdot109\).
The three representatives \((i_0,i_1,i_2)\) in (58.9) are
\[
 (1509,12,3),\qquad (3577,14,2),\qquad (6763,2,4).
 \tag{58.11}
\]
The JSON certificates retain the complete field and row data, so
checking them does not depend on reproducing the search or the
particular primitive-element choices made by PARI.

There is still no established induction from \(3^k\) to \(3^{k+1}\).
The independent lower-stratum phases cannot simply be omitted. For
example, at order 9 the tempting normalized norm prescription
\(W_3=W_1^{13}\) excludes all 12 full-Q solutions in (58.9): with
compatible generators it would require \(i_1\equiv i_0\pmod5\),
which none of the successful pairs satisfy. Their pairs are
\[
 (1,0),(4,0),(5,1),(15,1),(16,0),(20,4),
 (45,1),(49,0),(50,4),(60,4),(61,0),(64,0).
\]
This obstructs that particular finite-field recursion, without
asserting a failure of the differently twisted ray-field norm formulas
in Sections 38–40. Section 63 gives a correction at 9 and 27: the norm
must use a different Frobenius branch, with a twist when cycling back
to the first branch.

The remaining uniform target is now entirely algebraic over
\(\overline{\mathbb F}_2\): prove that (58.9) has a solution to
(58.7) for infinitely many \(k\), or construct another unbounded
family of complete characteristic-2 solutions. Frobenius covariance
settles H uniformly, and categorical lifting settles the passage to
complex existence; neither supplies the missing nonemptiness theorem.

---

# 59. The same hyperbolic monodromy in the arithmetic and S-fold routes

A literature check identifies a precise common lattice transformation
behind the arithmetic candidate and a physical construction of HI
modular data. This comparison does not prove categorification, but it
makes the possible connection more specific than a shared occurrence
of the quantum dilogarithm.

Let \(d^2=nd+1\), with \(n\) odd, and use the basis \((d,1)\) of
\(\mathbb Z[d]\). Multiplication by \(d\) and \(d^2\) has matrices
\[
 M_n=\begin{pmatrix}n&1\\1&0\end{pmatrix},\qquad
 P_n=M_n^2=\begin{pmatrix}n^2+1&n\\n&1\end{pmatrix}.
 \tag{59.1}
\]
The first reverses the standard alternating form, and the second
preserves it. Moreover,
\[
 \operatorname{Tr}P_n=n^2+2,\qquad
 (\operatorname{Tr}P_n)^2-4=n^2(n^2+4),\qquad
 P_n-I=nM_n.
 \tag{59.2}
\]
Thus its eigenvalues are \(d^2,d^{-2}\), with the real quadratic
field of the HI dimension. Smith normal form gives
\[
 \operatorname{coker}(M_n-I)\cong\mathbb Z/n\mathbb Z,
 \qquad
 \operatorname{coker}(P_n-I)\cong(\mathbb Z/n\mathbb Z)^2.
 \tag{59.3}
\]
Indeed the first matrix has an entry 1 and determinant \(-n\),
whereas the second is \(n\) times a unimodular matrix. Modulo \(n\),
\(M_n\) exchanges the two coordinates. Its two eigensubgroups are
\(\{(a,a)\}\) and \(\{(a,-a)\}\); as \(n\) is odd, these are
complementary cyclic Lagrangian subgroups of the finite symplectic
module in (59.3). These are proved lattice statements; they do not
identify a category or a matrix of associators.

There is also an exact comparison with S-fold monodromies. Put
\[
 S=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
 T=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad
 R=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\]
Then
\[
 P_n=T^nR^n,\qquad
 ST^{-n}ST^n=-R^nT^n=-R^nP_nR^{-n}.
 \tag{59.4}
\]
In particular the two give conjugate transformations in
\(\operatorname{PSL}_2(\mathbb Z)\). The central sign in
\(\operatorname{SL}_2(\mathbb Z)\) should be retained when discussing
physical or quantum lifts.

Gang–Kim's S-fold analysis uses levels \(n^2+2\) to obtain
nonunitary HI modular data after removing a semion factor.
[Gang–Kim, *Generalized non-unitary Haagerup-Izumi modular data from
3D S-fold SCFTs*](https://arxiv.org/abs/2211.13561).
The more recent two-segment construction includes the monodromies
\(ST^{-n}ST^n\), and compares their Galois-transformed modular
matrices with the untwisted HI data for every odd \(n\).
[Jeong–Sohn, Section 4.2 and Table 1](https://arxiv.org/html/2608.11946v1#S4.SS2).
Equation (59.4) is the direct arithmetic comparison with that family.

For the analytic side, Yalkinoglu announces approximations of
Shintani invariants by cyclic quantum dilogarithms along rational
approximants to a modular geodesic. The stated setting assumes a
positive fundamental unit with a one-term minus continued fraction;
the paper defers full proofs. Its cyclic dilogarithm orders are the
growing denominators of those approximants.
[Yalkinoglu, Theorems 3.1–3.2](https://arxiv.org/pdf/2508.18320).
This is not an exact finite-order HI pentagon identity. Applying such
an approximation to Section 51 would require handling its actual
continued-fraction cycle and proving that a suitable identity survives
in the limit with exactly the HI index sum and collision corrections.

The missing categorical step on the physical side is also explicit:
one needs a rigorous semisimple ribbon category realizing the proposed
modular data, together with a suitable Lagrangian algebra and an
identification of its module fusion rules. Equality of S and T
matrices alone supplies neither these algebra structure maps nor the
HI associators. Alternatively, a direct identification of the
finite operator of Section 50 with a quantum-dilogarithm construction
would need to prove the fifth-order relation on the complementary
subspace and account for the exceptional three-dimensional block. The lattice equalities (59.1)–(59.4) do not
establish either step. **Infinitude remains unresolved.**

---

# 60. An exact fifth-order criterion in characteristic 2

The positivity argument in Section 50 cannot simply be reduced modulo
2. Its three-dimensional Gram matrix becomes singular. Nevertheless,
the entire cubic system has an exact operator reformulation in this
characteristic. A universal rank-three correction turns the transfer
operator into an operator whose fifth power must be the identity.
This gives a precise target for a finite quantum-dilogarithm approach.

## 60.1 A characteristic-free residual identity

Work over any field where \(\delta(\delta-1)\ne0\), with
\(\delta^2=n\delta+1\), \(t=\delta^{-1}\), and the normalized
exceptional row and column. Define \(R\) by (50.1), and use
**unnormalized** vectors in the space indexed by \((a,b)\):
\[
 u(a,b)=\delta_{b,0},\quad v(a,b)=\delta_{a,0},\quad
 w(a,b)=A_{b,a},\quad z(a,b)=A_{a,b}.
\]
All transposes in this section are ordinary linear transposes. Define
\[
 J_{(a,b),(c,e)}=\delta_{a,e}A_{b+c,a}
                      -\delta_{a,0}\delta_{e,0}.
 \tag{60.1}
\]
For the quadratic residual Q of Section 52, direct multiplication gives
\[
 \begin{aligned}
 (RJ-I)_{(a,b),(c,e)}&=\delta_{b,e}Q(c-a,b),\\
 (JR-I)_{(a,b),(c,e)}&=\delta_{a,c}Q(b-e,a).
 \end{aligned}
 \tag{60.2}
\]
The exceptional column sum \(-t\) cancels the rank-one corrections.
Consequently all Q imply \(J=R^{-1}\), in any characteristic.

Reshape the cubic residual as
\(F_{(a,b),(c,e)}=C(b,c,a,e)\). There is the **off-solution** identity
\[
 \boxed{F=R^3-J^2-wu^{\mathsf T}-vz^{\mathsf T}
                         +vu^{\mathsf T}+tuv^{\mathsf T}.}
 \tag{60.3}
\]
Indeed the \(((a,b),(c,e))\) entry of \(R^3\) is the cubic sum
in \(C(b,c,a,e)\), while
\[
 (J^2)_{(a,b),(c,e)}
 =A_{b+e,a}A_{a+c,e}-\delta_{e,0}A_{b,a}
 -\delta_{a,0}A_{c,e}+\delta_{a,0}\delta_{e,0}.
\]
Substitution proves (60.3), without assuming Q or C.

Assume Q from now on. Its direct vector consequences are
\[
 \begin{array}{lll}
 Ru=w,&Rv=-tu,&Rw=v-tu,\\
 u^{\mathsf T}R=-tv^{\mathsf T},&
 v^{\mathsf T}R=z^{\mathsf T},&
 z^{\mathsf T}R=u^{\mathsf T}-tv^{\mathsf T}.
 \end{array}
 \tag{60.4}
\]
Multiplying (60.3) on the right by \(R^2\), and using these
relations, proves
\[
 \boxed{\text{all C}\quad\Longleftrightarrow\quad R^5-I=D,\qquad
 D=-t\bigl(wz^{\mathsf T}+vv^{\mathsf T}+uu^{\mathsf T}
                                      -tuv^{\mathsf T}\bigr).}
 \tag{60.5}
\]
Both directions follow since \(R\) is invertible. This is an equality
of specified matrices; a rank bound on \(R^5-I\) alone is insufficient.
The matrix \(D\) is defined from any full-Q candidate and commutes
with \(R\), by (60.4), before C is imposed.

In the phase ansatz, the columns \(u,v,w\) and the rows
\(u^{\mathsf T},v^{\mathsf T},z^{\mathsf T}\) are independent:
\(u,v\) have different axis supports, and \(w,z\) are nonzero
off those axes. The coefficient matrix in (60.5) is invertible, so
\(D\) has rank exactly 3.

## 60.2 The universal rank-one and nilpotent parts

Now take characteristic 2, \(n\) odd and \(\delta=\omega\) as in
Section 58. Thus \(t=\omega^2\), \(t^2+t+1=0\) and \(t^3=1\).
Put
\[
 K=[u\ v\ w],\qquad L=[u\ v\ z]^{\mathsf T}.
\]
The Q identities give
\[
 LK=\begin{pmatrix}1&1&t\\1&1&t\\t&t&1+t\end{pmatrix}
   =rr^{\mathsf T},\qquad r=(1,1,t)^{\mathsf T}.
 \tag{60.6}
\]
This matrix has rank 1, rather than rank 3. In particular the
orthogonal-complement decomposition of Section 50 is unavailable.

There is instead a completely explicit algebraic decomposition.
Set
\[
 e=u+tv+t^2w,\qquad f^{\mathsf T}=tu^{\mathsf T}
                         +v^{\mathsf T}+t^2z^{\mathsf T}.
\]
Using (60.5)–(60.6), without assuming C, gives
\[
 D^2=ef^{\mathsf T},\qquad f^{\mathsf T}e=t^2,
 \qquad D^3=tD^2,\qquad Re=te,\qquad f^{\mathsf T}R=tf^{\mathsf T}.
 \tag{60.7}
\]
Consequently
\[
 E=tD^2,\qquad N=D-tE
 \tag{60.8}
\]
satisfy
\[
 \boxed{E^2=E,\quad \operatorname{rank}E=1,\quad RE=ER=tE,
 \quad N^2=0,\quad EN=NE=0,\quad \operatorname{rank}N=2.}
 \tag{60.9}
\]
To see the last rank assertion, use \(D=tE+N\), the direct sum
\(\operatorname{im}E\oplus\ker E\), and \(\operatorname{rank}D=3\).
All of (60.7)–(60.9) hold for a full-Q phase candidate, regardless of C.

**Theorem.** In characteristic 2, for any normalized full-Q phase
candidate, define
\[
 \boxed{\mathcal P=R(I+D).}
 \tag{60.10}
\]
Then
\[
 \boxed{\text{all C}\quad\Longleftrightarrow\quad\mathcal P^5=I.}
 \tag{60.11}
\]
The correction \(\mathcal P-R\) has rank 3.

**Proof.** Write \(V=I+D\). On \(\operatorname{im}E\), V is
multiplication by \(1+t=t^2\), of order 3. On \(\ker E\), it is
\(I+N\), of order 2. Hence \(V^6=I\) and \(V^5=V^{-1}\).
As \(R\) commutes with V,
\[
 \mathcal P^5=R^5V^{-1}.
\]
This is the identity exactly when \(R^5=V=I+D\), which is (60.5).
The rank statement follows from invertibility of \(R\). ∎

At a full solution \(\mathcal P=R^6\). The original transfer
operator satisfies
\[
 R^{10}=I+t^2E,\qquad R^{30}=I.
 \tag{60.12}
\]
In fact its order is **exactly 30**. The eigenvalue t forces a factor
3 in its order, and the nonzero square-zero N forces a factor 2.
On \(\operatorname{span}(u,v,w)\), the characteristic polynomial is
\[
 X^3+tX+t=(X+t)(X^2+tX+1).
\]
The two roots of the quadratic are primitive fifth roots of unity,
forcing a factor 5. This also shows why \(R\) itself cannot be
identified with a diagonalizable fifth-order operator. The corrected
operator \(\mathcal P\), however, is diagonalizable at every full
solution, since \(X^5-1\) is separable in characteristic 2.

## 60.3 Exact checks and a restriction on an adjoint construction

`hi_finite_field_transfer.py` verifies (60.2)–(60.3) on order-5
phase matrices deliberately failing Q and C, both over
\(\mathbb F_{16}\) and over \(\mathbb Q(\sqrt{29})\). It then
checks the complete matrix identities (60.5)–(60.12) on the saved
order-3 and both order-9 characteristic-2 certificates. All checks
pass, including the stated ranks and the exact order 30.

One tempting construction would identify \(\mathcal P\), up to a
linear change of basis, with conjugation by an \(n\times n\)
cyclic quantum-dilogarithm matrix. This has a testable restriction.
If \(\mathcal P\sim\operatorname{Ad}(B)\) and
\(\mathcal P^5=I\), then \(B^5\) is scalar. Over an algebraically
closed field we may normalize \(B^5=I\). If the multiplicities of
its fifth-root eigenvalues are \(m_0,\ldots,m_4\), then those of
\(\operatorname{Ad}(B)\) are
\[
 M_j=\sum_{i\in\mathbb Z_5}m_i m_{i+j},\qquad
 \sum_i m_i=n.
 \tag{60.13}
\]
These are integer dimensions, even though the matrices have
characteristic 2.

At the order-9 representative \((i_0,i_1)=(1,0)\), the computed
multiplicities of \(\mathcal P\) are
\[
 (M_0,M_1,M_2,M_3,M_4)=(17,17,15,15,17)
\]
for one choice of primitive fifth root. Equation (60.13) is impossible:
\(\sum m_i=9\) and \(\sum m_i^2=17\) force the multiset
\(\{2,2,2,2,1\}\), whose four nontrivial autocorrelations are all
16. Thus this complete HI solution cannot arise from that adjoint
construction in any linear basis.

The other order-9 representative, \((5,1)\), has multiplicities
\((17,16,16,16,16)\), so it passes this necessary test. This does
not construct its phase matrix, much less an infinite family. It
shows that the adjoint approach, if successful, must select suitable
branches. The exact criterion (60.11) is the remaining operator target;
one still needs full-Q phase candidates for unbounded orders whose
corrected operators satisfy it.

## 60.4 The consecutive-ratio bound also survives in characteristic 2

The obstruction of Section 46 has an algebraic version requiring no
absolute values. Let k be any field containing a primitive n-th root
\(\zeta\), let \(W_0^2=1\), and suppose
\(W_aW_{-a}=\delta\ne1\) for \(a\ne0\). Assume all phases are
nonzero. If
\[
 \frac{W_a}{W_{a-1}}=\frac{P(\zeta^a)}{Q(\zeta^a)},\qquad
 \deg P,\deg Q\le r,\qquad Q(\zeta^a)\ne0
\]
for every a, then \(2r\ge n-2\).

Indeed the inverse norms make the consecutive ratios at a and
\(1-a\) equal for \(a\notin\{0,1\}\). Therefore
\[
 z^r\bigl(P(z)Q(\zeta/z)-Q(z)P(\zeta/z)\bigr)
\]
is a polynomial of degree at most \(2r\) vanishing at the \(n-2\)
distinct points \(\zeta^a\), \(2\le a<n\). Its value at 1 is
nonzero: the ratios at 0 and 1 differ by the nontrivial factor
\(\delta^{-1}\). This proves the bound in every characteristic.

Thus characteristic 2 does not permit a fixed number of nonsingular
cyclic-hypergeometric factors to provide all the phases in unbounded
order. A quantum-dilogarithm approach to (60.11) would need a different
extraction of phase data, or a separately proved treatment of the
exceptional indices. Neither that extraction nor infinitude is
established here.

---

# 61. A fixed elliptic curve parametrizes the characteristic-2 phase space

The multiplicative parameters in (58.9) have a geometric realization on
one curve, independent of \(k\). This identifies a possible setting for
addition identities, but does not make the quadratic or cubic equations
automatic.

## 61.1 Frobenius, inverse norms, and rational interpolation

Work over \(\mathbb F_4\), with \(\omega^2+\omega+1=0\), and put
\[
 E:\quad y^2+y=x^3+\omega,\qquad c=\omega^2.
 \tag{61.1}
\]
Negation sends \((x,y)\) to \((x,y+1)\). The tangent formula gives
\[
 [2](x,y)=(x^4,x^6+x^3+y+1)=(x^4,y^4),
 \tag{61.2}
\]
where the second equality uses (61.1). Thus the fourth-power Frobenius
is exactly \([2]\), as an endomorphism of the curve.

For any odd-order point \(P\) and any rational function
\(r\in\mathbb F_4(x)\), define, wherever the values are nonzero and
finite,
\[
 W_0=1,\qquad
 W_a=c\,\frac{y(aP)+r(x(aP))}{y(aP)+r(x(aP))+1}
 \quad(a\ne0).
 \tag{61.3}
\]
At a pole of \(r\), the displayed quotient is interpreted as 1,
so \(W_a=c\). More concretely, for \(r=A/B\) use
\[
 W_a=c\,\frac{y(aP)B(x(aP))+A(x(aP))}
                  {(y(aP)+1)B(x(aP))+A(x(aP))}.
 \tag{61.4}
\]
Negation and (61.2) immediately give
\[
 W_aW_{-a}=\omega,\qquad W_{2a}=W_a^4.
 \tag{61.5}
\]
The prescribed value at zero is essential: the underlying rational
function in (61.3) has value \(c\), rather than 1, at the identity of
the curve. Indeed \(y\) has pole order 3 there, whereas a rational
function of \(x\) has even pole order if it has a pole at all. Their
leading poles cannot cancel.

**Proposition.** Fix \(n=3^k\) and a point \(P\) of order \(n\).
Every phase sequence satisfying (58.5) and (58.8) has a representation
(61.3) for some \(r\in\mathbb F_4(x)\). Conversely, every such rational
function, written without common numerator and denominator zeros at the
relevant points, gives a valid sequence satisfying those two conditions.

**Proof.** Suppose \(aP\) has order \(3^j\), and put \(s=3^{j-1}\).
Since \(2^s\equiv-1\pmod{3^j}\), (61.2) shows that
\[
 x(aP)^{4^s}=x(aP),\qquad y(aP)^{4^s}=y(aP)+1.
 \tag{61.6}
\]
The degree of \(x(aP)\) over \(\mathbb F_4\) is exactly \(s\):
an earlier Frobenius return would give
\(2^b\equiv\pm1\pmod{3^j}\) for \(0<b<s\).
In particular \(y(aP)\notin\mathbb F_{4^s}\).

For \(W_a\ne c\), prescribe
\[
 r(x(aP))=\frac{W_a}{W_a+c}+y(aP);
 \tag{61.7}
\]
for \(W_a=c\), prescribe the value \(\infty\).
Inverse norms make these prescriptions identical at \(aP\) and
\(-aP\); Frobenius covariance makes them compatible under fourth
powers. By (61.6), each finite value belongs to \(\mathbb F_{4^s}\).

The polynomial
\[
 \Psi_P(X)=\prod_{a=1}^{(n-1)/2}(X-x(aP))
 \tag{61.8}
\]
is squarefree over \(\mathbb F_4\). It has one irreducible factor of
each degree \(1,3,\ldots,3^{k-1}\). Chinese remaindering constructs
polynomials \(A,B\) over \(\mathbb F_4\) with the prescribed projective
values: on each finite-value factor set \(B=1\) and prescribe \(A\);
on each infinite-value factor set \(B=0,A=1\). Both polynomials may be
chosen with degree less than \((n-1)/2\). They have no common zero on
this finite set, and their quotient gives (61.3).

Conversely, a finite value of \(r(x(aP))\) lies in
\(\mathbb F_{4^s}\), while \(y(aP)\) does not. Thus neither numerator
nor denominator in (61.3) can vanish. A pole gives the nonzero value
\(c\). Equations (61.5) finish the proof. ∎

In particular the phase space in (58.9) is, after choosing \(P\),
\[
 \prod_{j=1}^k\mathbb P^1(\mathbb F_{4^{3^{j-1}}}).
 \tag{61.9}
\]
Its factor sizes are exactly \(4^{3^{j-1}}+1\), agreeing with the
norm-torus counts. The proposition concerns the norm and Frobenius
constraints only. Its interpolation degree grows with \(n\), and it
provides no nonemptiness theorem for the full HI equations.

## 61.2 A recurrence fitting three orders fails at the fourth

Rational interpolation of the known phase data suggested the following
particularly short recurrence. For each \(\eta\in\mathbb F_4^\times\),
put
\[
 \begin{aligned}
 r_1^{(\eta)}(x)&=\eta^2,\\
 s_k(x)&=r_k^{(\eta)}(\eta(x+c)),\\
 r_{k+1}^{(\eta)}(x)&=c^2s_k(x)^3+\eta^2s_k(x)^2+\frac c x+c.
 \end{aligned}
 \tag{61.10}
\]
The next two values are independent of \(\eta\):
\[
 r_2(x)=\frac c x,\qquad
 r_3(x)=\frac{cx^4+x^3+x^2+x+c}
                  {x^4+cx^3+c^2x^2+x}.
 \tag{61.11}
\]
Both identities follow by direct substitution, and the program checks
them symbolically. At orders 3, 9 and 27, evaluating these functions
on suitable torsion points gives full HI solutions. At order 81,
however, none of the three functions \(r_4^{(\eta)}\) works.

`hi_char2_elliptic.py` verifies this without reading saved HI data. It
constructs a basis of \(E[n]\), certifies its independence with the
Weil pairing, and enumerates every primitive point modulo doubling.
There are \(4n/3\) such orbits: the number of primitive points is
\(8n^2/9\), and each orbit has length \(2n/3\). Since the functions
are defined over \(\mathbb F_4\), vanishing of all Q is unchanged
under this orbit operation. The exact search gives:

| Order | Distinct functions | Function/point-orbit evaluations | First diagonal Q survivors | Full-Q survivors |
|---:|---:|---:|---:|---:|
| 3 | 3 | 12 | 7 | 7 |
| 9 | 1 | 12 | 3 | 1 |
| 27 | 1 | 36 | 1 | 1 |
| 81 | 3 | 324 | 0 | 0 |

Every full-Q survivor in this table is exported and checked against
**every cubic** by `hi_finite_field_certificate.py`. The order-27
candidate passes all 729 Q and all 531,441 C. At order 81, the
nonzero first diagonal residual already rules out each candidate,
including all 5,832 primitive torsion points for each function.

Thus (61.10) is an exact fit to three successive orders whose proposed
inductive continuation is false. The geometric parametrization (61.3)
remains available, but a successful rational-function construction
needs additional structure beyond this cubic recurrence. Neither an
unbounded family of complete certificates nor infinitude is established.

---

# 62. Every order-13 quadratic phase solution satisfies the cubics

The circuit model of Section 57 also permits imposing all Q directly,
without first selecting phases by H.

**Theorem (exact computation).** At \(n=13\), every complex phase
solution of (Q), with the prescribed inverse norms and normalization,
satisfies every (C). Its row algebra over \(K=\mathbb Q(\delta)\) is
a field of degree 12, and its phase algebra has dimension 156 over K.

**Proof.** Let \(\mathcal A_{13}\) be the full one-column row algebra
of Section 54, of dimension 924. Let \(I_Q\) be the ideal generated
in it by the remaining quadratic residuals. Section 57's integral
circuit matrices give a specialization at
\[
 q=32059,\qquad\delta\mapsto1153.
\]
All the hypotheses for the integral model are checked, including the
units required in the row reconstruction. Rank specialization for the
map with images generating \(I_Q\) gives
\[
 \dim_K\mathcal A_{13}/I_Q
 \le\dim_{\mathbb F_q}\overline{\mathcal A}_{13}/\overline I_Q.
 \tag{62.1}
\]

The exact Krylov presentation of the specialized algebra is
\(\mathbb F_q[t]/(F(t))\), with \(F\) squarefree of degree 924.
In every irreducible factor, reconstruct the entire matrix and test
all nonexceptional Q. Exactly one factor, of degree 12, survives.
This counts the full quotient over the algebraic closure, including
points not rational over \(\mathbb F_q\); the right side of (62.1)
is 12.

Independently, `hi_stark_run(13)` supplies an exact full Q/C solution
in a field of absolute degree 24. A row coordinate has minimal
polynomial of degree 24 and the dimension generates a quadratic
subfield. Thus this row point has residue field of degree 12 over K.
Evaluation gives a surjection
\[
 \mathcal A_{13}/I_Q\longrightarrow L,\qquad [L:K]=12,
\]
where every cubic residual vanishes. The upper bound forces this
surjection to be an isomorphism. Hence all cubics vanish identically
in the full Q quotient, proving the implication for all its complex
points, at either dimension embedding.

Finally the character-gauge extension
\(X^{13}=\delta\prod_{a=2}^{12}R_a\) is finite étale of degree 13.
The phase algebra therefore has dimension \(13\cdot12=156\). ∎

`hi_column_fullq.py` regenerates the critical matrices and the modular
quotient, then reruns the independent exact cubic construction and
degree checks. No H equation is imposed. The verified orders for the
full phase implication are now
\[
 n=3,5,7,9,11,13.
\]
The matrix construction is uniform, but neither the required quotient
dimension nor a cubic lower bound is proved for unbounded orders.

---

# 63. The norm recursion permutes Frobenius branches

The failed norm prescription in Section 58 used a single branch at a
time. The ray-class structure instead predicts a permutation of
branches. This permutation has a uniform description, and the saved
finite certificates satisfy its norm laws exactly.

## 63.1 A uniform class-order and Frobenius relation

Put
\[
 n=3^k,\qquad D=n^2+4,\qquad d=\frac{n+\sqrt D}{2},
 \qquad\mathcal O=\mathbb Z[d].
\]
Here \(\mathcal O\) means the order of discriminant D, even when it
is not maximal. Use the ray modulus
\(\mathfrak m=(d-1)\) together with the real place at which \(d>0\).
Let \(G\) be this ray class group of \(\mathcal O\), and write
\(h(D)=|\operatorname{Pic}(\mathcal O)|\).

**Theorem.** Let \(\overline{\mathfrak p}=(3,d+1)\), and let
\(\beta\in G\) be its ray class. Then
\[
 \begin{gathered}
 1\longrightarrow(\mathbb Z/n\mathbb Z)^\times
 \longrightarrow G\longrightarrow\operatorname{Pic}(\mathcal O)
 \longrightarrow1,\\
 \operatorname{ord}_{\operatorname{Pic}(\mathcal O)}
     [\overline{\mathfrak p}]=k,\qquad
 \beta^k=\operatorname{Frob}_{(2)},\qquad
 \operatorname{ord}(\beta)=k\varphi(n).
 \tag{63.1}
 \end{gathered}
\]
In particular \(k\mid h(D)\). On the \(h(D)\) cosets of
\(\langle\operatorname{Frob}_{(2)}\rangle\), multiplication by
\(\beta\) consists of \(h(D)/k\) cycles, each of length k.

**Proof.** First \(d\) is a fundamental unit of \(\mathcal O\).
If a unit \(u\) satisfied \(1<u<d\), write
\(u-u'=b\sqrt D\), where \(b\) is a positive integer and
\(u'=\pm u^{-1}\). Since \(d+d^{-1}=\sqrt D\),
\[
 0<b\le\frac{u+u^{-1}}{\sqrt D}<1,
\]
a contradiction. Thus \(\mathcal O^\times=\{\pm d^j:j\in\mathbb Z\}\).

The quotient \(\mathcal O/(d-1)\) is \(\mathbb Z/n\mathbb Z\).
In the ray-class exact sequence, d has image \((1,+1)\) and
\(-1\) has image \((-1,-1)\). Dividing
\((\mathbb Z/n\mathbb Z)^\times\times\{\pm1\}\) by this latter
diagonal subgroup gives the first line of (63.1). This uses the
exact sequence for orders in [Kopp–Lagarias, Corollary 6.7](https://arxiv.org/html/2212.09177v3), so no maximal-order
or squarefreeness hypothesis is being inserted.

The two primes above 3 are coprime to the conductor of \(\mathcal O\),
and
\[
 (d-1)=\mathfrak p^k,\qquad
 (d+1)=\overline{\mathfrak p}^{k}.
 \tag{63.2}
\]
To prove that the class order is exactly k, suppose
\(\overline{\mathfrak p}^{e}=(\alpha)\) for \(0<e<k\).
Then \(|N\alpha|=N=3^e\le n/3\). Multiplying by a power of d
and by a sign, arrange
\[
 \sqrt{N/d}\le\alpha<\sqrt{Nd}.
\]
Writing \(\alpha-\alpha'=b\sqrt D\), now with \(b\in\mathbb Z\),
gives
\[
 |b|\sqrt D\le\alpha+N/\alpha
 \le\sqrt N(\sqrt d+1/\sqrt d)<\sqrt D.
\]
For the last inequality use
\(N(\sqrt D+2)\le(n/3)(\sqrt D+2)<D\).
Hence \(b=0\), so \(\alpha\) is an integer. Its principal ideal
has equal valuations at the two primes above 3, contradicting
\((\alpha)=\overline{\mathfrak p}^{e}\).

In the ray group, (63.2) gives
\(\beta^k=[(d+1)]=[(2)]\), because \(d+1\equiv2\pmod{\mathfrak m}\)
and both generators are positive at the selected real place.
The image of \([(2)]\) in the local kernel is 2, which has order
\(\varphi(3^k)\). Since the image of \(\beta\) in the ordinary
class group has order k, its ray order is \(k\varphi(n)\).
The coset-cycle statement follows. ∎

The prime 2 is inert in the quadratic field and is coprime to the
order conductor and the ray modulus. Thus, for the ray class field
\(L\) of this order, its residue algebra at 2 has the form
\[
 \mathcal O_L/2\mathcal O_L
 \cong\prod_{h(D)}\mathbb F_{4^{\varphi(n)}}.
 \tag{63.3}
\]
This is a theorem about the arithmetic field. Identifying this algebra
with an algebra of full HI solutions would require an additional proof.

`hi_char2_ray_indices.gp` certifies the class groups and units with
`bnfcertify`, then checks the ray groups, the prime classes, and
\(\beta^k=\operatorname{Frob}_{(2)}\):

| \(n\) | \(h(n^2+4)\) | Ray group invariant factors | Frobenius order | Cycles of \(\beta\) on Frobenius cosets |
|---:|---:|---|---:|---|
| 3 | 1 | 2 | 2 | one cycle of length 1 |
| 9 | 2 | 12 | 6 | one cycle of length 2 |
| 27 | 3 | 54 | 18 | one cycle of length 3 |
| 81 | 8 | 216, 2 | 54 | two cycles of length 4 |
| 243 | 25 | 4050 | 162 | five cycles of length 5 |
| 729 | 36 | 2916, 6 | 486 | six cycles of length 6 |
| 2187 | 84 | 30618, 2, 2 | 1458 | twelve cycles of length 7 |

The first three arithmetic Frobenius indices agree with the complete
phase-orbit counts of Section 58. The later entries are arithmetic
counts, not established HI orbit counts.

The nonmaximal-order distinction already matters at \(n=3^8=6561\):
the discriminant is \(43046725=5^2\cdot1721869\). The same script
certifies class number 384 for \(\mathbb Z[d]\), compared with 96
for the maximal order, and verifies that the conjugate prime has
order 8 in the former class group. It obtains the order class group
as the maximal-order ray group modulo the conductor, divided by the
image of the rational residue units. Thus the uniform theorem does
not rely on the first seven displayed orders happening to be maximal.

## 63.2 The saved phases obey the branch-permuting norm laws

At orders 9 and 27, number the saved Frobenius representatives in their
existing JSON order, \(j=0,\ldots,k-1\). On tuples of field elements
define
\[
 (Tx)_0=x_{k-1}^4,\qquad (Tx)_j=x_{j-1}\ (j>0).
 \tag{63.4}
\]
Then \(T^k\) is componentwise fourth-power Frobenius, exactly the
relation in (63.1). For \(3^s\Vert a\) with \(s<k-1\), set
\[
 r_s=2\cdot3^{k-s-1},\qquad
 \nu_s(x)=\omega^2
 N_{\mathbb F_{4^{r_s}}/\mathbb F_{4^{r_s/3}}}(x).
 \tag{63.5}
\]
The scalar factor is essential: an ordinary degree-three field norm
sends the norm coset to the norm-one group.

**Exact finite result.** The complete saved phase families satisfy
\[
 \boxed{(W_{3a}^{(j)})_j
       =T\bigl(\nu_s(W_a^{(j)})_j\bigr)}
 \qquad(n=9,27;\quad 3a\ne0).
 \tag{63.6}
\]
In the exponent coordinates of (58.9), the order-9 top exponents
\((1,5)\) give lower exponents
\((4\cdot5,1)\bmod5=(0,1)\). At order 27,
\[
 \begin{aligned}
 i_0&=(1509,3577,6763),\\
 i_1&=(4\cdot6763,1509,3577)\bmod65=(12,14,2),\\
 i_2&=(4\cdot2,12,14)\bmod5=(3,2,4).
 \end{aligned}
 \tag{63.7}
\]
These are precisely the independent stratum values found by the search.

`hi_char2_twisted_norm.py` checks (63.6) directly from the saved row
certificates, without using their search exponents. Frobenius covariance
gives \(R_2=W_1^{-2}\), so the unique characteristic-two square root
recovers \(W_1\); prefix reconstruction then recovers every phase.
All 12 order-9 and all 72 order-27 norm comparisons pass. The
same-branch prescription fails in every comparison. At order 27,
omitting the fourth-power twist at the return to branch zero causes
24 failures.

This is a norm relation among branches and conductor strata at a
**fixed** order. It is not an induction from order \(3^k\) to
order \(3^{k+1}\). At order 81, (63.1) supplies two arithmetic cycles
of four branches; a construction based on it should allow that
permutation and its Frobenius twist. The present data neither produce
those HI branches nor prove the required cubic identities in unbounded
order. Infinitude remains unresolved.

---

# 64. A uniform obstruction to small-field and quotient inflation constructions

The smallest characteristic-two field and a natural quotient induction
can now be excluded uniformly. These are obstructions to particular
constructions, not obstructions to HI existence at the corresponding
orders. They explain why extending the finite certificates requires
more than repeating their values on larger groups.

## 64.1 No Frobenius-covariant quadratic solution over the four-element field

Let \(G\) be any nontrivial finite abelian group of odd order. Work
in characteristic two, put \(\omega^2+\omega+1=0\) and
\(c=\omega^2\), and write the phase quadratic residual as
\[
 F(g,h)=\sum_{m\in G}
 W_mW_{h-m}W_{-m-g}W_{m+g-h}\qquad(g,h\ne0).
 \tag{64.1}
\]
The norm and Frobenius conditions are
\[
 W_0=1,\qquad W_aW_{-a}=\omega\ (a\ne0),
 \qquad W_{2a}=W_a^4.
 \tag{64.2}
\]
The nonexceptional equations (Q) are exactly \(F(g,h)=0\).

**Theorem.** There is no solution of (64.1)–(64.2) with every
\(W_a\in\mathbb F_4\).

**Proof, first step: eliminate the third nonzero value.** In this field,
Frobenius covariance means \(W_{2a}=W_a\). Put
\[
 T_g=\sum_m W_mW_{m-g}W_{m+g},\qquad S_g=W_g+W_{-g}.
\]
The identity
\(W_{-a}=\omega W_a^2+c\delta_{a,0}\) gives, without assuming Q,
\[
 F(g,g)=cT_g^2+S_g.
 \tag{64.3}
\]
Indeed, expand the two reversed factors in (64.1); the two boundary
terms are \(W_g^2W_{2g}^2=W_g\) and \(W_{-g}\).
Pairing the remaining terms of \(T_g\) under \(m\mapsto-m\)
gives
\[
 T_g=\omega+S_g^2+b_g,\qquad b_g\in\mathbb F_2.
 \tag{64.4}
\]
Away from \(m=0,\pm g\), the paired products are inverses in
\(\mathbb F_4^\times\), so their sum lies in \(\mathbb F_2\).
The three exceptional positions contribute the displayed terms.

If \(W_g=c\), its norm partner is also c, so \(S_g=0\).
Then (64.4) makes \(T_g\) either \(\omega\) or c, and (64.3)
cannot vanish. Thus Q forces
\[
 W_a\in\{1,\omega\}\quad(a\ne0).
 \tag{64.5}
\]

**Second step: an additive closure contradiction.** Write
\(W_a=1+c f(a)\), where \(f:G\to\mathbb F_2\), including
\(f(0)=0\). The norm and Frobenius laws become
\[
 f(-a)=1+f(a)\quad(a\ne0),\qquad f(2a)=f(a).
 \tag{64.6}
\]
Let \(\mu=(|G|-1)/2\pmod2\). In the group algebra
\(\mathbb F_2[G]\), write \(f^-\) for index reversal and J for
the sum of all group elements. Then
\[
 f^2=f,\qquad f^-=J+1+f,\qquad ff^-=\mu J.
\]
Consequently every two-point correlation is \(\mu\), including
the zero shift.

For \(g,h,g-h,g+h\ne0\), the following identity holds before
imposing Q:
\[
 \boxed{\displaystyle
 \operatorname{Tr}_{\mathbb F_4/\mathbb F_2}
       \bigl(\omega F(g,h)\bigr)
 =y+(x+y)z+(x+y+1)v,
 }
 \quad
 \begin{cases}
 x=f(g),&y=f(h),\\
 z=f(h-g),&v=f(h+g).
 \end{cases}
 \tag{64.7}
\]
Here is an expansion check of this identity. Define
\(t(a,b)=\sum_m f(m)f(m+a)f(m+b)\). On substituting
\(W=1+cf\) and the reversed-factor formula into (64.1), the
constant, linear, quadratic and quartic contributions to the trace
vanish. For the quadratic terms use the constant two-point correlation.
The two boundary terms also have zero trace after multiplication by
\(\omega\): their sum is \(u+\omega u^{-1}\in c\mathbb F_2\),
where \(u=W_gW_hW_{g+h}^2\in\mathbb F_4^\times\).
The remaining trace is
\[
 t(g,h)+t(-g,-h)+t(g,-h)+t(-g,h).
\]
For nonzero distinct a and b, expanding (64.6) at the three
exceptional positions gives
\[
 t(a,b)+t(-a,-b)
 =f(a)f(b)+f(b)+(f(a)+f(b))f(b-a).
\]
Apply this twice to obtain (64.7).

Now let \(S=\{a:f(a)=1\}\). It contains exactly one element from
each pair \(\{a,-a\}\), so is nonempty and excludes zero.
If distinct \(g,h\in S\), they cannot be negatives of each other.
Putting \(x=y=1\) in (64.7), Q forces \(f(g+h)=1\).
For \(g=h\), the same conclusion follows from \(f(2g)=f(g)\).
Thus S is closed under addition. A nonempty additive subsemigroup of
a finite group contains zero, a contradiction. ∎

This proof applies to every odd abelian group, although the companion
computations use cyclic groups. In the specified Frobenius gauge, the
smallest possible finite coefficient field therefore has 16 elements:
\(\omega\) already requires an even extension degree over
\(\mathbb F_2\), degree two is excluded, and the saved order-3
certificate attains degree four. The theorem makes no claim about
arbitrary gauges or about all solutions over a fixed larger field.

## 64.2 No inflation constant on nonzero quotient cosets

**Theorem.** Let \(K\) be a proper nontrivial subgroup of an odd
finite abelian group G. Over any field of characteristic two containing
\(\omega\), a solution of Q and (64.2) cannot be constant on each
coset \(a+K\) with \(a\notin K\).

**Proof.** Suppose it were, and put \(V=W|_K\). For
\(g,h\in K\setminus\{0\}\), all summands outside K in
(64.1) are \(\omega^2\), by the norm law and coset constancy.
There are an even number of them. Therefore
\[
 F_G(g,h)=F_K(g,h),
\]
so V satisfies every quadratic on K.

Next take \(0\ne g\in K\) and \(h\notin K\). Splitting
the sum into the cosets K, \(h+K\), and their complement gives
\[
 \begin{aligned}
 F_G(g,h)
 &=\omega\sum_{a\in K}
       \bigl(V_aV_{-g-a}+V_aV_{g-a}\bigr)+\omega^2\\
 &=\omega\bigl(V_{g/2}^2+V_{-g/2}^2\bigr)+\omega^2.
 \end{aligned}
 \tag{64.8}
\]
The second equality uses cancellation of the nonfixed pairs in a
characteristic-two convolution on an odd group. The complement of
the two cosets has odd cardinality, giving the final \(\omega^2\).

Vanishing of (64.8), for every g, forces
\(V_a+V_{-a}=c\). Together with \(V_aV_{-a}=\omega\), this
puts every nonzero-index value among the roots of
\[
 X^2+cX+\omega=(X+1)(X+\omega).
\]
Hence V takes values in \(\mathbb F_4\), inherits (64.2), and
satisfies every quadratic on K. Section 64.1 excludes this. ∎

Thus a successful induction through cyclic quotients must change the
values within some nonzero cosets. This obstruction does not exclude
the branch-permuting norm relation of Section 63.

## 64.3 Exact checks and the next-smallest field

`hi_char2_small_field_obstruction.py` checks (64.3)'s diagonal
exclusion and the off-solution trace formula on norm/Frobenius inputs
at twelve odd orders through 127. The larger binary assignment spaces
are sampled with a fixed seed; these checks are diagnostics for the
uniform proof, not exhaustive existence searches. At every tested
binary assignment it also exhibits a failed additive closure and
independently evaluates the corresponding nonzero quadratic.
Independent off-solution checks of both identities in Section 64.2
pass at group/kernel orders
\((9,3),(15,5),(21,7),(27,9),(35,7),(63,9)\), using general
\(\mathbb F_{16}\) norm inputs without assuming Q or Frobenius.

The script separately exhausts the norm/Frobenius ansatz over
\(\mathbb F_{16}\) at orders 3, 11 and 43. Each doubling orbit
at these orders has length twice an odd number, with inversion halfway
around the orbit. Thus its initial phase satisfies \(W^5=\omega\)
and has precisely five choices. There is one orbit at 3 and 11 and
three at 43. The exact full-Q counts are
\[
 \begin{array}{c|r|r}
 n&\text{assignments}&\text{full-Q assignments}\\\hline
 3&5&2\\
 11&5&2\\
 43&125&0.
 \end{array}
\]
These counts exclude only the stated field and Frobenius gauge.
They do not exclude HI categories at order 43, nor an infinite family
over larger finite fields. A construction satisfying the additive
equations in unbounded order is still missing; infinitude is unproved.

## 64.4 An involution interchanging the dimension roots gives a norm obstruction

Let k be a characteristic-two field with an involution sigma such
that \(\sigma(\delta)=\delta^2\), where
\(\delta^2+\delta+1=0\). Let L be its fixed field and put
\(c=\delta^2\). Suppose normalized phases on a nontrivial finite
odd abelian group satisfy
\[
 W_0=1,\qquad W_aW_{-a}=\delta\ (a\ne0),\qquad
 W_{2a}=W_a^4.
\]
This involution is different from the field involutions fixing delta
that occur in the norm towers of Sections 58 and 65.

**Theorem.** Neither of the following additional conditions is
compatible with all the quadratic equations:

1. \(W_a\in cL^\times\) for every nonzero a;
2. \(W_a\sigma(W_a)=1\) for every nonzero a.

In the first case every diagonal quadratic residual is nonzero.
In the second case a vanishing diagonal residual at a forces
\(W_a\in\{1,\delta\}\).

**Proof.** Write \(F_a=F(a,a)\), using (64.1), and
\(t=W_a^2\). The summands at \(m=0,a,-a\) give
\[
 E_a=\delta+\delta/t+\delta^2t.
\]
All other summands have four nonzero phase factors; denote their
sum by \(B_a\), so \(F_a=E_a+B_a\).

In the fixed-field-line case, \(\sigma(W_b)=cW_b\), hence
\(\sigma(B_a)=cB_a\). In the relative-norm-one case,
\(\sigma(W_b)=W_b^{-1}=cW_{-b}\) for nonzero b. Reindexing
the bulk sum by \(m\mapsto-m\) gives the same identity.
In the first case \(\sigma(t)=\delta t\), and in the second
\(\sigma(t)=t^{-1}\); in either case
\(\sigma(E_a)=E_a+1\). Therefore the following identity holds
**before imposing any quadratic**:
\[
 \boxed{\displaystyle
 \sigma(F_a)+\delta^2F_a
 =t+\delta+\frac{\delta^2}{t}
 =\left(\frac{(W_a+1)(W_a+\delta)}{W_a}\right)^2.}
 \tag{64.8}
\]
If \(F_a=0\), this forces \(W_a=1\) or \(W_a=\delta\).
Neither is in \(cL^\times\), since \(\delta\notin L\),
proving the first assertion. In the second case, all diagonal
quadratics would put every phase in \(\mathbb F_4\). Section 64.1
then excludes the full quadratic system. ∎

There is a useful explicit application. For \(z\in L\), put
\[
 U(z)=\delta\frac{z+\delta}{z+\delta^2}.
 \tag{64.9}
\]
It extends projectively with \(U(0)=1\) and \(U(\infty)=\delta\),
and satisfies
\[
 U(z)\sigma(U(z))=1,\quad U(z)U(z^{-1})=\delta,\quad
 U(z)^4=U(z^4).
\]
Consequently any nonzero input sequence in L with
\(z_{-a}=z_a^{-1}\), \(z_{2a}=z_a^4\) produces phases
\(W_a=U(z_a)\) satisfying the two ambient constraints, after
setting \(W_0=1\). Nevertheless (64.8) becomes
\[
 \boxed{\displaystyle
 \sigma(F_a)+\delta^2F_a
   =\frac{\delta z_a^2}{(z_a^2+z_a+1)^2}\ne0.}
 \tag{64.10}
\]
The denominator is nonzero because L does not contain a primitive
cube root of unity. Thus every diagonal quadratic fails for inputs
in \(L^\times\); allowing 0 and infinity can only lead to the
four-element-field obstruction if all diagonals vanish.

For example, let \(p\equiv7\pmod8\) be prime,
\(r=\operatorname{ord}_p(2)\), and
\(L=\mathbb F_{2^r}\subset k=\mathbb F_{2^{2r}}\), with
\(\sigma(x)=x^{2^r}\). The integer r is odd. For a primitive
p-th root xi in L, the quadratic-character permutation
\[
 z_a=\xi^{a^{(p+3)/2}}\quad(a\in\mathbb F_p^\times)
 \tag{64.11}
\]
satisfies both input laws: \((p+3)/2\) is odd and
\(2^{(p+3)/2}=4\pmod p\). Neither \(W_a=cz_a\) nor
\(W_a=U(z_a)\) can satisfy even the first diagonal quadratic.
This rejects these formulas uniformly, rather than only at the
orders where they were tested.

`hi_char2_conjugate_norm.m` checks the rational identities exactly
and verifies (64.8) on 20,736 diagonal residuals from deliberately
unconstrained norm/Frobenius inputs. The checks use r=1,3,5,7 and
n=3,7,9,15,23,31,47,71,127, in both restricted families. Whenever
an input lies entirely in \(\{1,\delta\}\), the script also
constructs and evaluates the failed off-diagonal quadratic from
Section 64.1. The explicit construction (64.11) is checked at
p=7,23,31,47,71,79,103, including the nonzero projected residual
(64.10). All checks pass. These are restrictions on the additional
conjugation conditions; the general existence problem remains open.

---

# 65. The first phase forces the full field, and every relative norm has cubic lifts

The characteristic-two tower has a forced field size, rather than merely
an ambient field convenient for search. Its relative norm steps also
admit an explicit cubic construction. Both results hold uniformly;
neither asserts nonemptiness of the full additive system.

## 65.1 A single quadratic detects a collapsed top orbit

Let \(n=3^k\), \(k\ge2\), and put \(g=n/3\). Assume the
norm conditions in (64.2), and suppose only that the unit-index phases
are periodic under translation by g:
\[
 W_{a+g}=W_a\qquad(3\nmid a).
 \tag{65.1}
\]
No periodicity is imposed on the nonunit indices. For every unit h,
the phase residual (64.1) then satisfies
\[
 \boxed{F(g,h)=\omega(W_g+W_{-g})^2+\omega^2.}
 \tag{65.2}
\]

**Proof.** Split the sum into the three cosets of
\(H=3\mathbb Z_n\). At \(m\in H\), the unit factors
\(W_{h-m}W_{m+g-h}\) multiply to \(\omega\), using (65.1).
At \(m\in h+H\), the other two unit factors multiply to
\(\omega\). In the third coset all four indices are units and
their product is \(\omega^2\); this coset has odd size. Thus
\[
 F(g,h)=\omega\sum_{a\in H}
       (W_aW_{-g-a}+W_aW_{g-a})+\omega^2.
\]
Each convolution is the square at its unique fixed index, because
all other terms pair and cancel in characteristic two. Since g has
order three, those two fixed indices are g and \(-g\). This is
(65.2). ∎

If the bottom phases additionally satisfy Frobenius covariance, then
\(W_{-g}=W_{2g}=W_g^4\) and \(W_g^5=\omega\). The right side
of (65.2) is **always nonzero**. Indeed, its vanishing would give
\(W_g+W_{-g}=\omega^2\). The norm would then put both phases
among the roots of
\[
 X^2+\omega^2X+\omega=(X+1)(X+\omega).
\]
Both lie in \(\mathbb F_4\), where fourth powering fixes them,
contradicting their sum \(\omega^2\ne0\).

In fact the five possible bottom phases lie in \(\mathbb F_{16}\),
and (65.2) takes the three values \(1,\omega,\omega^2\), with
multiplicities 2, 2 and 1 respectively. Thus this obstruction needs
no estimate, field search, or unknown lower-stratum data.

## 65.2 Exact field degree at every power of three

**Theorem.** At \(n=3^k\), suppose the norm and Frobenius laws
(64.2) hold. For \(k\ge2\), assume the single quadratic
\(F(n/3,1)=0\); for \(k=1\), assume \(F(1,1)=0\).
Then
\[
 \boxed{
 [\mathbb F_4(W_1):\mathbb F_4]=2\cdot3^{k-1}=2n/3.
 }
 \tag{65.3}
\]
Consequently this holds for every full-Q solution in this gauge.
Every phase and row coordinate belongs to this field, and already
\(R_2=B_{1,2}\) generates it. The exact field of all coefficients,
including \(\omega\), is therefore
\(\mathbb F_{2^{4n/3}}\).

**Proof.** Put \(r=2\cdot3^{k-1}\). Doubling generates the units
modulo n. Its orbit closure and halfway inversion give
\[
 W_1\in\mathbb F_{4^r},\qquad
 W_1^{1+4^{r/2}}=\omega.
\]
Let \(e=[\mathbb F_4(W_1):\mathbb F_4]\), so \(e\mid r\).
If e is odd, it divides \(r/2\), and the norm equation becomes
\(W_1^2=\omega\). Hence \(W_1=\omega^2\) and \(e=1\).
Otherwise e is twice a power of three.

For \(k\ge2\), every proper possibility for e therefore divides
\(r/3\). The element
\[
 u=2^{r/3}\pmod n
\]
has order three and equals \(1+t(n/3)\), with \(t\not\equiv0\pmod3\).
Because \(W_1^{4^{r/3}}=W_1\), Frobenius covariance gives
\(W_{ua}=W_a\) for every unit a. The three labels in this
u-orbit are \(a,a+n/3,a-n/3\). This is exactly (65.1), which
contradicts the assumed quadratic by Section 65.1.

For \(k=1\), the only proper degree is one; then both nonzero
phases equal \(\omega^2\), and direct substitution gives
\(F(1,1)=\omega\ne0\). This proves (65.3).

The orbit closure at every other conductor stratum puts all phases
in \(\mathbb F_{4^r}\), as in Section 58. Finally,
\[
 R_2=\frac{W_1^2}{W_2}=W_1^{-2}.
\]
Squaring is an automorphism of a finite field, so
\(\mathbb F_4(R_2)=\mathbb F_4(W_1)\). The other row entries
are rational expressions in the phases and \(\omega\), proving
the remaining claims. ∎

In particular, all full-Q Frobenius orbits have length exactly
\(2n/3\). Their scalar stabilizer is trivial, since every scalar
unit is a power of 2. This recovers the residue-field degree predicted
by Section 63 directly from the phase equations, without identifying
their solution algebra with a ray class field or assuming their
number is a class number. At order 81, any such solution necessarily
has first phase of degree 54 over \(\mathbb F_4\), and coefficient
field \(\mathbb F_{2^{108}}\).

## 65.3 A uniform cubic lift for every prescribed normalized norm

Let \(q=4^s\), \(s\ge1\), and fix
\(Y\in\mathbb F_{q^2}\) with \(Y^{q+1}=\omega\). For
\(t\in\mathbb F_{q^2}\), define
\[
 \boxed{P_{Y,t}(X)=X^3+tX^2+Yt^qX+\omega Y.}
 \tag{65.4}
\]

**Theorem.** Precisely \(q(q-1)/3\) of the \(q^2\) choices of t
make (65.4) irreducible over \(\mathbb F_{q^2}\). Every root x
of every such irreducible cubic satisfies
\[
 x\in\mathbb F_{q^6}\setminus\mathbb F_{q^2},\qquad
 x^{q^3+1}=\omega,\qquad
 \omega^2N_{\mathbb F_{q^6}/\mathbb F_{q^2}}(x)=Y.
 \tag{65.5}
\]
Conversely every x satisfying (65.5) is obtained in this way, with
\(t=\operatorname{Tr}_{\mathbb F_{q^6}/\mathbb F_{q^2}}(x)\).

**Proof.** Write \(N=\omega Y\); then \(N^{q+1}=1\) and
\(Y=\omega^2N\). The polynomial is
\(X^3+tX^2+\omega^2Nt^qX+N\). Its roots are preserved by
\[
 \rho(x)=\omega/x^q,
\]
as is checked by the identity
\[
 x^{3q}P_{Y,t}(\omega/x^q)=N P_{Y,t}(x)^q.
\]
For an irreducible cubic, \(\rho^2(x)=x^{q^2}\) acts on its
three roots as a 3-cycle. Therefore \(\rho\) itself is a 3-cycle,
and \(\rho^3(x)=\omega/x^{q^3}=x\). This proves the first
norm in (65.5). The constant coefficient is N, proving the second.

Conversely take \(x^{q^3+1}=\omega\), outside the base field,
with ordinary relative norm N. Put \(t=x+x^{q^2}+x^{q^4}\).
The second elementary symmetric coefficient is
\[
 N(x^{-1}+x^{-q^2}+x^{-q^4})=\omega^2Nt^q=Yt^q.
\]
Thus its minimal polynomial is (65.4).

For the count, the top norm coset is
\(\omega^2\mu_{q^3+1}\), and the ordinary relative norm maps it
onto \(\mu_{q+1}\). Each fiber has size
\[
 (q^3+1)/(q+1)=q^2-q+1.
\]
Exactly one element of each fiber lies in the base field. To see this,
write a base-field phase as \(\omega^2\eta\), with
\(\eta\in\mu_{q+1}\). Its ordinary relative norm is
\(\eta^3\), and cubing is bijective on \(\mu_{q+1}\), since
\(q+1\equiv2\pmod3\). The other \(q^2-q\) elements form
disjoint triples of conjugate roots of distinct irreducible cubics.
Their number is \(q(q-1)/3\). ∎

There is also an explicit normalization that separates the prescribed
norm from the trace choice. Put
\[
 H=q^2-q+1,\qquad
 x_0=\omega^2(\omega Y)^{(q+2)/3}.
\]
This is the unique base-field point of the norm fiber. Every cubic
lift is
\[
 x=x_0\zeta,\qquad \zeta\in\mu_H\setminus\{1\},\qquad
 t=x_0(\zeta+\zeta^{q^2}+\zeta^{q^4}).
 \tag{65.6}
\]
Indeed \(\gcd(H,q^2-1)=1\), so only \(\zeta=1\) can leave x
in the base field. On setting \(X=x_0Z\) and \(u=t/x_0\), the
cubic becomes
\[
 x_0^{-3}P_{Y,t}(x_0Z)=Z^3+uZ^2+u^qZ+1.
 \tag{65.7}
\]
Thus the permitted normalized traces are one fixed set of cubic
Gaussian periods, independent of Y. Formula (65.6), or enumeration
of the irreducible cubics, constructs the lifts without an HI seed.

For the step from \(\mathbb F_{4^{2\cdot3^{j-1}}}\) to
\(\mathbb F_{4^{2\cdot3^j}}\), use \(q=4^{3^{j-1}}\).
These are exactly the degree-three steps between the conductor
strata of Section 58. All non-base-field roots produced by (65.4)
have the full degree over \(\mathbb F_4\) at this step: the
proper-divisor argument in Section 65.2 applies to their norm coset.

If the branch-permuting prescription of Section 63 is imposed on
candidate tuples, take the target normalized norm to be the
corresponding component of \(T^{-1}W_{3a}\). Equation (65.4)
then provides a nonempty, explicit choice of cubic lifts at every
step, including the required Frobenius twist. Iterating this procedure
constructs candidate norm towers of arbitrary height. The theorem
does **not** say that those towers satisfy Q or C, or that the norm
prescription has been proved necessary for every HI solution.
The remaining problem is to select the trace parameters t so that
the additive equations hold in unbounded order.

## 65.4 Exact verification

`hi_char2_field_tower.py` checks the off-solution identity (65.2)
at orders 9, 27, 81 and 243, with general nonunit norm data and all
five possible bottom phases. The unit h is exhaustive through 81
and sampled at 243. Every resulting residual is nonzero. It also
checks directly that \(R_2\) in every saved order-3, order-9 and
order-27 Frobenius representative has degree 2, 6 and 18 over
\(\mathbb F_4\), respectively.

For the cubic theorem, the script exhausts all 16 traces for each
of the five normalized norms at \(q=4\), finding four irreducible
cubics per norm. At \(q=64\), it exhausts all 4096 traces for
three specified normalized norms, finding 1344 in each case. It
constructs all 20 cubic extensions from the first test and one from
each of the latter three tests, and independently checks both norms
in (65.5), the norm-fiber parameter, and the cubic-period trace in
the resulting extension fields. All exact checks pass.
Infinitude of HI categories remains unproved.

---

# 66. Two quadratics, full field degree, and the obstruction to local inflation

The searches along powers of three admit a substantially smaller finite
acceptance test. Its field-degree condition is essential: omitting it
permits explicitly false candidates in unbounded order.

## 66.1 Exact completion from two quadratics at the first three orders

Retain the phase residual F of (64.1), the norm and Frobenius laws
(64.2), and \(n=3^k\). Consider just
\[
 F(1,1)=F(2,1)=0.
 \tag{66.1}
\]

**Finite theorem.** For \(n=3,9,27\), conditions (64.2), (66.1),
and
\[
 [\mathbb F_4(W_1):\mathbb F_4]=2n/3
 \tag{66.2}
\]
imply every quadratic and cubic. Conversely, every full cubic phase
solution in this Frobenius gauge satisfies these conditions.

**Proof by exhaustive finite algebra.** The parametrization (58.9)
exhausts the norm/Frobenius solutions over the algebraic closure.
The modified `hi_char2_frobenius.py` records the survivors of (66.1)
and the first-phase degrees, before applying the remaining Q filters:

| n | Solutions of (66.1) | First-phase degrees over \(\mathbb F_4\) | Full Q and C |
|---:|---:|---|---:|
| 3 | 2 | 2 points of degree 2 | 2 |
| 9 | 12 | 12 points of degree 6 | 12 |
| 27 | 72 | 18 points of degree 6; 54 of degree 18 | 54 |

At each order, the full-Q subset has exactly the cardinality of the
subset satisfying (66.2); the program also checks that each full-Q
point belongs to that subset. Hence the subsets coincide. All
Frobenius representatives are passed afresh through the independent
complete Q/C verifier. The converse follows from C implying Q and
the uniform field-degree theorem of Section 65. ∎

At order 27, the finite étale algebra cut out by (66.1) inside the
norm/Frobenius scheme is consequently
\[
 (\mathbb F_{4^{18}})^3\times(\mathbb F_{4^6})^3;
\]
the full-Q/C quotient retains precisely the first three factors.
For a degree-six first phase, all lower-stratum phases already lie
in \(\mathbb F_{4^6}\), so the degree counts also give the
degrees of the entire tuples. The norm/Frobenius algebra is a
product of separable finite fields; taking equation quotients here
introduces no hidden nilpotents.

By Section 65, the three equations
\[
 F(1,1)=F(2,1)=F(n/3,1)=0
 \tag{66.3}
\]
therefore suffice at these three orders as well. This presents a
concrete smaller system to investigate in unbounded order. Neither
the implication from (66.1)–(66.2) to C for arbitrary k, nor the
nonemptiness of that system for unbounded k, has been proved.

## 66.2 A uniform origin-patched inflation identity

Let M be odd, let \(N=sM\) with odd \(s>1\), and suppose V
is phase data on \(\mathbb Z_M\) satisfying the norm law.
Set \(c=\omega^2\), and define
\[
 W_0=1,\qquad
 W_a=\begin{cases}
       V_{a\bmod M},&a\not\equiv0\pmod M,\\
       c,&a\equiv0\pmod M,\ a\ne0.
      \end{cases}
 \tag{66.4}
\]
These phases satisfy the norm law on \(\mathbb Z_N\), and inherit
Frobenius covariance whenever V has it. Denote their residuals by
\(F_N\), and the seed residuals by \(F_M\).

**Theorem.** If reduction modulo M is injective on the distinct
elements of
\[
 E(g,h)=\{0,h,-g,h-g\}\subset\mathbb Z_N,
\]
then
\[
 F_N(g,h)=F_M(g\bmod M,h\bmod M).
 \tag{66.5}
\]
At the first newly split origin collision, one instead has
\[
 \boxed{F_N(M-h,h)=F_M(-h,h)+1}
 \qquad(1\le h<M).
 \tag{66.6}
\]

**Proof.** Replace the value at zero in both V and W by c. The
resulting background sequences are exactly periodic with period M.
Their quartic sums agree, since each seed summand is repeated s
times and s is odd in characteristic two. Restoring the value 1 at
zero changes only the summands indexed by E. When its distinct
positions remain distinct modulo M, these corrections correspond
one to one and agree, proving (66.5).

For \(g=M-h\), the two distinct positions h and \(-g=h-M\)
merge modulo M. All other corrections still match. At the merged
seed position the background term is
\(c^2V_hV_{-h}=c\), and the restored term is \(\omega\);
their difference is 1. At each of the two separate positions in
\(\mathbb Z_N\), the background term is c and the restored
term is \(cV_hV_{-h}=1\). Their two equal corrections cancel.
This proves (66.6). ∎

For a full-Q seed of order \(M\ge5\), the inflated phases
therefore satisfy (66.1) at every odd multiple \(N>M\), but
\[
 F_N(M-1,1)=1.
 \tag{66.7}
\]
Taking either saved order-9 orbit gives such counterexamples for
every \(N=3^k\), \(k\ge3\), and more generally for every
larger odd multiple of 9. Their first-phase degree remains six.
At powers of three they also have
\(F_N(N/3,1)=\omega^2\), as follows from (65.2).
Thus they are false partial candidates, not new HI certificates.

At order 27, inflating the 12 full-Q order-9 points accounts for
12 of the 18 degree-six solutions in the table. Each passes
\(F(3,1)=0\) by (66.5), and fails \(F(8,1)=0\) by (66.6).
The remaining six partial points fail \(F(3,1)=0\). This is
exactly the filter history recorded by the exhaustive search.

`hi_char2_partial_completion.py` independently reconstructs all saved
order-9 and order-27 representative phases, checks their Q equations,
and applies (66.4) with multipliers 3, 5 and 9. It verifies the norm
and Frobenius laws, every local Q with
\(1\le g,h\le(M-1)/2\), and the nonzero residual (66.7).
All checks pass. They verify the claimed failure of partial
sufficiency, not existence at the inflated orders.

## 66.3 The counts do not give a degree-six rational iteration

The numbers \(2,12,72\) in the first column of the table suggest
testing a fixed rational preimage recursion. That precise test fails.
Let \(E_3,E_9,E_{27}\in\mathbb F_4[X]\) be the monic products
over the distinct first-phase coordinates of the solutions of
(66.1). Their degrees are 2, 12 and 72, respectively; for example
\(E_3=X^2+\omega X+\omega\).

**Exact finite obstruction.** No degree-six rational map
\(f=A/B\in\mathbb F_4(X)\) has both
\[
 B^2E_3(A/B)\ \text{proportional to }E_9,
 \qquad
 B^{12}E_9(A/B)\ \text{proportional to }E_{27}.
 \tag{66.8}
\]
Here A and B are coprime with maximum degree six.

`hi_char2_rational_recursion.py` rebuilds these eliminants from fresh
exhaustive searches. To exhaust the first identity, choose a root r
of \(E_3\) in \(\mathbb F_{16}\). The factorization of
\(E_9\) over this field consists of four irreducible cubics in
two fourth-power-conjugate pairs. The polynomial \(A+rB\) must
choose one factor from each pair. There are four such choices, and
five scalar choices modulo \(\mathbb F_4^\times\), hence 20
rational maps in total. Every map is checked against the first
identity, and every one fails the second identity exactly.

The weaker proposal of following just one branch also fails. Over
\(\mathbb F_4\), write \(E_9=b_0b_1\), where the two irreducible
degree-six factors have ascending coefficient lists
\[
 b_0:[1,\omega^2,0,\omega^2,0,1,1],\qquad
 b_1:[1,\omega,1,\omega,\omega^2,\omega^2,1].
\]
For either choice b, exactly ten degree-three maps \(f=A/B\)
satisfy \(B^2E_3(A/B)\propto b\): two choices of a cubic factor
over \(\mathbb F_{16}\), times five scalars as above. The program
checks all twenty maps. For none of them is \(B^6b(A/B)\)
proportional to any of the three degree-eighteen factors of
\(E_{27}\). Those three factors are precisely the full-Q branches
by Section 66.1. Hence no stationary degree-three rational map in
this first-phase coordinate follows even one branch through
orders 3, 9 and 27. Maps varying with the level, changes of coordinates
varying with the level, and multivariable recursions remain open.

This excludes a particular one-variable iteration. It leaves open
the coupled trace construction in Section 65, and does not change
the missing requirements for infinitude: nonempty full-degree
solutions in unbounded order and a uniform proof of the remaining
additive equations.

---

# 67. Patching the origin does not permit bounded rational ratios

Section 60.4 left open a separately defined exceptional phase. The
Frobenius relation closes this escape for rational consecutive-ratio
formulas in characteristic two. The proof below is uniform in every
odd order; it is not restricted to powers of three.

Let k be an algebraically closed field of characteristic two, let
\(\omega^2+\omega+1=0\), and put \(c=\omega^2\). Suppose
\[
 W_0=1,\quad W_a\ne0,\quad W_aW_{-a}=\omega\ (a\ne0),
 \quad W_{2a}=W_a^4.
 \tag{67.1}
\]
Write \(r_a=W_a/W_{a-1}\), with cyclic indices, and let \(\zeta\)
be a primitive n-th root of unity. Assume that a rational function
\(R=P/Q\), with \(\deg P,\deg Q\le r\), interpolates only
\[
 R(\zeta^a)=r_a\qquad(2\le a<n),
 \tag{67.2}
\]
with no zero or pole at these sample points. Nothing is prescribed
for R at 1 or \(\zeta\); in particular, (67.2) allows arbitrary
separate treatment of the ratios adjoining the origin.

**Theorem.** If \(n>4r+3\), then every nonzero-index phase equals c,
and the first phase quadratic has residual
\[
 F(1,1)=\sum_m W_m^2W_{1-m}W_{-1-m}=\omega\ne0.
 \tag{67.3}
\]
Consequently any full-Q solution satisfying (67.1) and (67.2) has
\(4r\ge n-3\). The coefficients of R may vary with n and may
belong to an arbitrarily large extension field.

**Proof.** Inverse norms first give
\(r_a=r_{1-a}\) for \(a\notin\{0,1\}\). The polynomial
\[
 z^r\bigl(P(z)Q(\zeta/z)-Q(z)P(\zeta/z)\bigr)
\]
has degree at most \(2r\) and vanishes at the \(n-2\) sample
points. The assumed inequality therefore proves the rational identity
\[
 R(z)=R(\zeta/z).
 \tag{67.4}
\]
Frobenius covariance gives an independent ratio identity, valid even
at the exceptional indices:
\[
 r_{2a}r_{2a-1}=r_a^4.
 \tag{67.5}
\]
All three ratios in (67.5) are among the prescribed samples unless
\(a\in\{0,1,(n+1)/2\}\). Thus the polynomial
\[
 H(z)=P(z^2)P(\zeta^{-1}z^2)Q(z)^4
       -Q(z^2)Q(\zeta^{-1}z^2)P(z)^4
 \tag{67.6}
\]
vanishes at \(n-3\) distinct points. It has degree at most \(8r\)
and contains only even powers of z. Since k is perfect, it is the
square of a polynomial of degree at most \(4r\). Its square root
has the same distinct zeros. Hence \(n>4r+3\) implies \(H=0\), or
\[
 R(z^2)R(\zeta^{-1}z^2)=R(z)^4.
 \tag{67.7}
\]

Here is the rigidity in (67.7). Let \(D=\operatorname{div}R\),
regarded as a finitely supported integer vector on the geometric
points of \(\mathbb P^1\). Both \(\pi:z\mapsto z^2\) and
\(L:z\mapsto\zeta z\) permute these points. Pullback by \(\pi\)
has multiplicity two at every point. Taking divisors in (67.7),
pushing forward by \(\pi\), and dividing the integer multiplicities
by two gives
\[
 D+L_*D=2\pi_*D.
 \tag{67.8}
\]
Equip these finitely supported vectors with their ordinary real
Euclidean norm; no norm on k is used. The two permutations preserve
this norm, so squaring (67.8) gives
\(\langle D,L_*D\rangle=\lVert D\rVert^2\). It follows that
\(D=L_*D\).

Every zero or pole of R in \(k^\times\) would now occur on an
entire n-element orbit under multiplication by \(\zeta\). But
\(r<n\), so R has degree less than n and cannot contain such an
orbit in either its zero or its pole divisor. Its divisor is supported
at 0 and infinity, and therefore \(R(z)=\kappa z^s\). Reflection
(67.4) forces \(s=0\), and (67.7) then gives
\(\kappa^2=\kappa^4\). Since \(\kappa\ne0\), characteristic two
implies \(\kappa=1\).

Equation (67.2) now makes \(W_1,\ldots,W_{n-1}\) equal. Their
inverse norm makes this common value the unique square root
\(c=\omega^2\) of \(\omega\). In (67.3), the terms at
\(m=0,1,-1\) sum to \(c^2+c^3+c^3=\omega\). The other
\(n-3\) equal terms cancel in characteristic two. This proves the
theorem. ∎

`hi_char2_ratio_bound.py` independently reconstructs the saved phases
and checks (67.5), reflection, and the constant-phase residual. It
then solves the exact rational interpolation problems (67.2), with
the denominator required to be nonzero at every sample. The minimum
degrees are 0 at order 3, 4 for each order-9 branch, and 12 for each
order-27 branch. It also checks the square-root polynomial and its
\(n-3\) required zeros in (67.6). These finite checks verify the
algebra used in the proof; they do not supply an existence argument.

The theorem concerns rational functions of the cyclic parameter
\(\zeta^a\). It does not apply to arbitrary rational functions on
the elliptic curve of Section 61, or to the double-sine product of
Section 51. The variational candidate of Section 53 also remains
available at every odd order. Its full additive identities, and
infinitude itself, are still unproved.

---

# 68. The first quadratic is linear in all lower Frobenius seeds

There is a constructive elimination step that avoids searching the
lower norm tori independently. It applies before their inverse norms
are imposed, and does not assume any of the other additive equations.

Fix \(n=3^k\) and write \(N=2n/3\). All Frobenius-covariant phases
can be placed in \(E=\mathbb F_{2^{2N}}\), as in Section 58. Fix the
top seed \(x=W_1\), with
\(x^{2^N+1}=\omega\). Its iterated fourth powers determine every
\(W_a\) with \(3\nmid a\); denote these fixed values by \(U_a\).
On \(H=3\mathbb Z_n\), write the remaining phases as \(V_t\),
retaining \(V_0=1\). For the moment impose Frobenius covariance but
allow arbitrary lower values, including zeros.

**Uniform affine elimination theorem.** The first quadratic is
\[
 \boxed{\displaystyle
 F(1,1)=\sum_{t\in H}\bigl(a_t V_t^2+b_t V_t\bigr),\qquad
 a_t=U_{1-t}U_{-1-t},\quad
 b_t=U_{1-t}^2U_{t-2}+U_{-1-t}^2U_{t+2}.
 }\tag{68.1}
\]
Consequently \(F(1,1)=0\) is an affine \(\mathbb F_2\)-linear
system in exactly \(N-2\) lower seed coordinates, with values in
\(K=\mathbb F_{2^N}\). Its constant term is
\[
 \kappa_x=\omega+\omega^2(x+\omega/x)^2.
 \tag{68.2}
\]
Thus the equation has the form
\[
 L_x(v)=\kappa_x,\qquad
 L_x:\mathbb F_2^{N-2}\longrightarrow\mathbb F_2^N.
 \tag{68.3}
\]
All solutions, or a certificate of inconsistency, can be obtained by
binary linear algebra once x is supplied.

**Proof.** In
\(F(1,1)=\sum_m W_m^2W_{1-m}W_{-1-m}\), split m into its three
residue classes modulo 3. For \(m\equiv0\), use \(t=m\).
For \(m\equiv1\), use \(t=1-m\); for \(m\equiv-1\), use
\(t=-1-m\). In each class all the other displayed indices are
units modulo 3. This gives (68.1) directly. The only powers of the
lower phases are first and second powers, both binary linear.

For \(1\le s<k\), the stratum \(3^s\parallel a\) is one
doubling orbit of length \(2\cdot3^{k-s-1}\). Its seed is an
arbitrary element of
\(\mathbb F_{2^{4\cdot3^{k-s-1}}}\), and the other values are its
iterated fourth powers. No norm relation is needed for this assertion.
The lower seed space therefore has binary dimension
\[
 \sum_{s=1}^{k-1}4\cdot3^{k-s-1}
 =2(3^{k-1}-1)=N-2.
 \tag{68.4}
\]
At \(t=0\), the top norm gives \(a_0=\omega\). Using
\(U_{\pm2}=U_{\pm1}^4\) gives
\(b_0=\omega^2(U_1+U_{-1})^2\), which proves (68.2).

For completeness, the target field in (68.3) also does not require
the lower norms. For arbitrary phase data, reindexing the summation
proves
\[
 F(g,h)=F(-g,h)=F(g,-h)=F(h,g).
 \tag{68.5}
\]
Frobenius covariance gives \(F(g,h)^4=F(2g,2h)\). Since
\(2^{n/3}\equiv-1\pmod n\), iterating this equality gives
\(F(1,1)^{2^N}=F(-1,-1)=F(1,1)\). Hence every value of the
affine map lies in K, proving (68.3). ∎

The lower norm equations must still be imposed on the affine solution
space. For a seed \(y_s=W_{3^s}\), they are
\[
 y_s^{2^{2\cdot3^{k-s-1}}+1}=\omega.
 \tag{68.6}
\]
These are quadratic equations in the binary coordinates, because the
displayed Frobenius power is binary linear. This yields a precise
uniform procedure: choose x on its norm torus, solve (68.3), impose
(68.6) on its kernel parameters, and then test the remaining Q and C.
It does not assert that a suitable choice of x exists at every order.

`hi_char2_firstq_linear.py` implements this reduction independently of
the exhaustive search. It checks (68.1) on lower data not satisfying
the norms, checks the target field and affine constant, and solves the
linear systems for each saved first phase. The results are:

| order | saved branch | lower binary dimension | rank of \(L_x\) | norm-compatible lower solutions |
|---:|---:|---:|---:|---:|
| 3 | 0 | 0 | 0 | 1 |
| 9 | 0 | 4 | 4 | 1 |
| 9 | 1 | 4 | 4 | 1 |
| 27 | 0 | 16 | 16 | 1 |
| 27 | 1 | 16 | 15 | 1 |
| 27 | 2 | 16 | 16 | 1 |

The recovered values are compared exactly with every saved lower
phase. At order 27, branch 1, the first quadratic alone has two lower
solutions; exactly one satisfies all lower norms. Thus even the saved
solutions do not justify assuming full rank uniformly.

The program also exhausts all 65 top norm choices at order 9. Of
these, 23 give consistent affine systems; imposing the lower norms
leaves a total of 24 first-Q candidates, agreeing with the independent
exhaustive search. Twelve of these pass the remaining equations, as
already certified in Section 58.

At order 81 it samples 64 top norm choices. The 63 nonconstant choices
give ranks 51 or 52; nineteen of their affine systems are consistent,
but none of their lower solutions satisfies all inverse norms. The
constant top choice has rank 2 and a large kernel; its kernel is not
enumerated by this check. Such a collapsed top seed cannot give full
Q by Section 65. These are finite sample results, not a search of the
entire order-81 norm torus. The new result is the uniform linear
elimination, while nonempty full solutions at unbounded orders remain
to be constructed.

---

# 69. Relative traces and a linear number of quadratic orbits

Two further uniform reductions apply to the characteristic-two search.
They reduce the equations to be solved; neither asserts that they have
solutions at unbounded orders.

## 69.1 Pairing each quadratic into a relative trace

Let \(n=3^k\), \(N=2n/3\), \(E=\mathbb F_{2^{2N}}\), and
\(K=\mathbb F_{2^N}\). Retain
\[
 W_0=1,\qquad W_aW_{-a}=\omega\quad(a\ne0),\qquad
 W_a^4=W_{2a},\qquad \omega^2+\omega+1=0.
\]
Write \(\bar z=z^{2^N}\). Since \(2^{n/3}\equiv-1\pmod n\),
Frobenius covariance implies \(\overline{W_a}=W_{-a}\), including
at zero. For \(g,h\ne0\), set
\[
 T_m=W_mW_{h-m}W_{-m-g}W_{m+g-h},\qquad
 \iota(m)=h-g-m.
\]
Direct substitution gives \(T_{\iota(m)}=\overline{T_m}\).
The involution has the unique fixed point \(m_0=(h-g)/2\).
If \(a=(h-g)/2\) and \(b=(h+g)/2\), its summand is
\[
 T_{m_0}=(W_aW_{-a})(W_bW_{-b})
 =\begin{cases}\omega,&h=g\text{ or }h=-g,\\
                 \omega^2,&h\ne\pm g.
   \end{cases}
\]
Thus, for any set \(M_{g,h}\) containing one element of each
nontrivial orbit of \(\iota\),
\[
 \boxed{\displaystyle
 F(g,h)=\epsilon_{g,h}
  +\operatorname{Tr}_{E/K}\!\left(\sum_{m\in M_{g,h}}T_m\right),
 \quad
 \epsilon_{g,h}=\begin{cases}\omega,&h=\pm g,\\
                              \omega^2,&h\ne\pm g.
              \end{cases}}
 \tag{69.1}
\]
There are exactly \((n-1)/2\) terms inside the trace. This proof
uses only the displayed norms and involution, so the same pairing
identity holds over any characteristic-two field with an involution
sending \(W_a\) to \(W_{-a}\) and fixing \(\omega\).

## 69.2 Exactly \((n-1)/2\) orbit representatives suffice for Q

In the Frobenius gauge, the identities
\[
 F(g,h)=F(-g,h)=F(g,-h)=F(h,g),\qquad
 F(2g,2h)=F(g,h)^4
 \tag{69.2}
\]
reduce vanishing of all nonzero-index quadratics to a linear number
of residuals. This statement needs no inverse norms.

For a pair \((g,h)\), put
\(s=\min(v_3(g),v_3(h))\), \(M=3^{k-s}\), and divide both
indices by \(3^s\). At least one resulting index is a unit modulo
M; exchange them if necessary and normalize that index to 1.
Every unit modulo M is a power of 2. Consequently this normalization
preserves vanishing by (69.2). The remaining ratio \(t\ne0\) is
identified with \(-t\); when t is a unit, it is also identified
with \(t^{-1}\) by exchanging the two indices. Representatives
can therefore be taken as
\[
 (3^s,3^s t),\quad
 1\le t\le(M-1)/2,\quad
 t\le\min(t^{-1}\bmod M,-t^{-1}\bmod M)
 \text{ if }3\nmid t.
 \tag{69.3}
\]
There are \((M/3-1)/2\) nonunit ratio classes. For unit ratios,
Burnside's lemma applied to negation and inversion gives
\[
 \frac{\varphi(M)+2}{4}=\frac{M/3+1}{2}
\]
classes: inversion fixes exactly 1 and -1, negation fixes none,
and \(t^2=-1\) has no solution modulo 3. The total at this
stratum is M/3. Summing over s proves
\[
 \boxed{\#\{\text{quadratic orbits}\}
       =\sum_{j=1}^{k}3^{j-1}=\frac{n-1}{2}.}
 \tag{69.4}
\]
This counts orbits under the stated symmetries; it does not claim
algebraic independence of the residuals.

The residual at a stratum of order \(M=3^j\) lies in
\(\mathbb F_{2^{2M/3}}\): iterate (69.2) \(M/3\) times and
use simultaneous sign reversal. Thus the representative equations
can be written using at most
\[
 \sum_{j=1}^k 3^{j-1}\,(2\cdot3^{j-1})
 =\frac{n^2-1}{4}
 \tag{69.5}
\]
binary coordinate equations. In particular, order 81 has 40
representative residuals, with 1640 such coordinates altogether.

`hi_char2_quadratic_orbits.py` implements (69.3) and verifies every
nonzero pair, its exchange, its sign reversal, and its doubling
through order 729. Its exact counts are 1, 4, 13, 40, 121, and 364.

## 69.3 An exact Boolean search, with independent acceptance

`hi_char2_sat.py` now encodes the norm equations and the quadratic
representatives using CryptoMiniSat's native XOR clauses. The seed
coordinates use normal bases, making fourth powers coordinate
permutations. Products are simplified using inverse norms, squares,
and doubling before Boolean multiplication gates are introduced.
Equation (69.1) cuts the quartic summation in half. Full top degree,
which is necessary by Section 65, is imposed explicitly.

The default search starts with two quadratics and adds a failed
representative whenever a model is found. The `--all-quadratics`
option encodes every representative at startup. Any proposed model
is checked by separate integer finite-field arithmetic against every
Q, and any existence claim additionally requires the independent
complete GP cubic verifier. `--skip-cubic` explicitly produces only
unverified-for-C full-Q data.

The smaller encoding used 55,892 auxiliary variables for the first
two order-27 equations and 981,919 at order 81 in the initial trace
runs, down from 165,395 and 2,997,151 in the direct encodings.
Canonicalizing the representative indices can slightly change these
circuit counts. The complete order-27 representative encoding has
113,644 auxiliary variables. These are implementation sizes, not
mathematical bounds on proof complexity.

`hi_char2_sat_checks.py` fixes norm-compatible seed assignments and
compares the encoded formula with direct finite-field evaluation at
orders 3, 9, 27, and 81. The order-9, -27, and -81 assignments have
nonzero quadratic residuals, so these checks also test the formula
away from its zero locus. All comparisons pass. Fresh SAT searches
at orders 3 and 9 pass every Q and every C independently; their logs
are in `hi_char2_sat_results.txt`.

The bounded two-equation order-27 run reached its time limit without
a SAT or UNSAT conclusion. Larger searches are exploratory. No
order-81 certificate or infinitude theorem follows from this work.
A solver timeout is not evidence of nonexistence.

Reproduction with the currently available Python binding is:

```sh
PYTHONPATH=/tmp/hi_boolean_solver39 /usr/bin/python3.9 hi_char2_sat.py --order 9 --all-quadratics
PYTHONPATH=/tmp/hi_boolean_solver39 /usr/bin/python3.9 hi_char2_sat_checks.py
python hi_char2_quadratic_orbits.py
```

The binding is CryptoMiniSat 5.14.7 for Python 3.9, installed outside
the workspace in the displayed temporary directory. The
[project documentation](https://github.com/msoos/cryptominisat)
describes its XOR clause interface. Recreating that temporary
installation may be necessary in a later environment.

---

# 70. Complete characteristic-two quadratic-to-cubic ideals through 13

Magma gives a second finite completion theorem, now entirely in
characteristic two and without the Frobenius ansatz of Sections
58 and 66.

**Finite ideal theorem.** For each
\(n\in\{3,5,7,9,11,13\}\), every characteristic-two phase
solution of the inverse norms and all Q satisfies all C. More
strongly, each cross-free balanced cubic residual belongs to the
ideal generated by the inverse norms and Q over \(\mathbb F_4\).
The quadratic phase algebra is nonzero and has the following
lengths, counting any scheme multiplicity:

| n | norm/Q generators used | Groebner basis size | phase algebra length | cross-free cubic orbit representatives |
|---:|---:|---:|---:|---:|
| 3 | 2 | 3 | 6 | 1 |
| 5 | 5 | 10 | 20 | 2 |
| 7 | 9 | 28 | 42 | 6 |
| 9 | 14 | 126 | 108 | 14 |
| 11 | 20 | 194 | 132 | 17 |
| 13 | 27 | 301 | 156 | 30 |

Here the ambient ring is
\[
 R=\mathbb F_4[W_1,\ldots,W_{n-1}],\qquad W_0=1,
\]
and the ideal contains \(W_aW_{-a}-\omega\) for
\(1\le a\le(n-1)/2\), together with
\(F(g,h)\) for \(1\le g\le h\le(n-1)/2\).
No phase variable needs an additional saturation equation: the
inverse norms already make every nonzero-index phase a unit.
Identity (68.5) proves coverage of the remaining Q; the program
also independently reduces every omitted nonzero-index Q to zero.

For a balanced cross-free pair \((a,c)\) of triples, define
\[
 S_{a,c}=\sum_m\prod_{i=1}^3W_{m+a_i}
                   \prod_{j=1}^3W_{-m+c_j},\qquad
 P_{a,c}=\prod_{i,j=1}^3W_{a_i+c_j}.
\]
The normalized cubic is
\(\omega^2 S_{a,c}=(\omega-1)P_{a,c}\).
Since \(\omega^2=\omega-1\), its residual is simply
\(S_{a,c}-P_{a,c}\). The program computes a Groebner basis of I
and verifies
\[
 \operatorname{NormalForm}(S_{a,c}-P_{a,c},I)=0
 \tag{70.1}
\]
for every cross-free orbit representative from the already verified
balanced-index reduction. The remaining cubic cases follow from
norms and Q by Sections 34--40. This is ideal membership, not just
vanishing on a selected list of roots.

The positive lengths prove that these finite quadratic schemes have
points over finite extensions of \(\mathbb F_4\). Equation (70.1)
makes each point a complete cubic certificate. Section 58 therefore
supplies complex categorification at these six finite orders. This
recovers finite existence without reading any saved HI matrices.
The calculation does not impose Frobenius covariance, scalar H,
or any predetermined extension degree.

`hi_char2_phase_ideal.py` generates the exact Magma input; the
completed output is saved in `hi_char2_phase_ideal_results.txt`.
With the user-provided Magma 2.28-4 installation, reproduction is:

```sh
python hi_char2_phase_ideal.py --source /tmp/hi_char2_phase_ideal.m
/home/tzuchen/Software/Magma/magma -b /tmp/hi_char2_phase_ideal.m
```

The computations use the documented
[Groebner-basis and normal-form operations](https://magma.maths.usyd.edu.au/magma/handbook/groebner_bases).
The higher-order calculations have not supplied a completed result.
No uniform ideal containment, uniform nonemptiness, or infinitude
is asserted. In particular, the proof in this section is specific
to characteristic two; transferring a finite algebra-length bound
to characteristic zero would require a separate argument.

---

# 71. The cubics force a unique Frobenius gauge

The Frobenius gauge is now justified uniformly for every full
characteristic-two phase solution. This changes the interpretation
of the earlier finite searches: at the cubic level the gauge loses
no phase solutions. It also gives an explicit finite etale algebra
whose nonvanishing is the remaining existence question.

## 71.1 A convolution identity from the diagonal cubics

Work in characteristic two with the normalized matrix A and
\(\delta=\omega\). Fix \(g\ne0\). For sequences on
\(\mathbb Z_n\), let
\((x*y)_s=\sum_t x_t y_{s-t}\), let e be the delta sequence
at zero, and use square brackets to denote pointwise powers.
Define
\[
 u_s=A_{s,g},\quad v_s=A_{g,-s},\quad
 f_s=A_{s,2g},\quad w=u^{[2]},\quad z=v^{[2]}.
\]
The Q column at g is exactly \(u*v=e\), so its square gives
\(w*z=e\). The cubic with indices \((g,g,k,k)\), using
\(A_{g+k,k}=A_{-k,g}\), is exactly
\[
 f*z=w. \tag{71.1}
\]
Multiplying by w and using \(z*w=e\) yields \(f=w*w\).
In characteristic two all terms of this self-convolution cancel
in pairs except the unique term at \(t=s/2\). Consequently
\[
 f_s=w_{s/2}^2=A_{s/2,g}^4.
\]
Conversely this identity and Q imply (71.1). The fixed axis entries
handle \(g=0\) directly. We have therefore proved the uniform
polynomial equivalence
\[
 \boxed{\displaystyle
 Q+\{C(g,g,k,k):g,k\in\mathbb Z_n\}
 \quad\Longleftrightarrow\quad
 Q+\{A_{2a,2b}=A_{a,b}^4:a,b\in\mathbb Z_n\}.}
 \tag{71.2}
\]
This argument uses the order-three symmetry and the normalized
matrix equations; it does not use the phase parametrization.
It involves no square-root choice or division by an unknown.

There are also exact identities away from Q and C. Set
\[
 q=u*v-e,\qquad D=f*z-w,\qquad H=f-w*w.
\]
Then
\[
 \boxed{\displaystyle
 D=H*z+w*q^{[2]},\qquad
 H=D*w+f*q^{[2]}.}
 \tag{71.3}
\]
Indeed \(w*z=e+q^{[2]}\), and both identities follow by
associativity. Thus (71.2) is an equality of the corresponding
ideals after Q is imposed, not merely a pointwise implication.
The proof works over arbitrary commutative characteristic-two
coefficient rings.

## 71.2 Unique normalization of the phases

Assume now the inverse-normalized phase parametrization. Since
\(\omega\in\mathbb F_4\), equation (71.2) also gives
\(B_{2a,2b}=B_{a,b}^4\). Define
\[
 r(a)=\frac{W_a^4}{W_{2a}},\qquad r(0)=1.
\]
For \(a+b\ne0\), substitute
\(B_{a,a+b}=W_aW_b/W_{a+b}\) into matrix covariance to obtain
\[
 r(a)r(b)=r(a+b).
\]
For \(a+b=0\), the same equality follows from
\(r(a)r(-a)=\omega^4/\omega=1\). Thus r is a character of
\(\mathbb Z_n\), in particular \(r(a)^n=1\).

A character change \(W'_a=\chi(a)W_a\) leaves A unchanged and
changes the ratio to \(r'(a)=\chi(a)^2r(a)\). Since n is odd,
squaring is an automorphism of the character group. The unique
choice giving \(r'=1\) is
\[
 \boxed{\displaystyle
 \chi(a)=r(a)^{-(n+1)/2},\qquad
 W'_a=\chi(a)W_a,\qquad (W'_a)^4=W'_{2a}.}
 \tag{71.4}
\]
All divisions here are by units already supplied by the inverse
norms. This normalization is therefore defined over the original
coefficient algebra, with no field extension or root choice.
It applies to every full cubic phase solution. It also applies
whenever Q and just the diagonal cubics hold.

## 71.3 An explicit field bound and finite etaleness

Put \(r_n=\operatorname{ord}_n(2)\) and
\(E_n=\mathbb F_{4^{r_n}}\). Iterating (71.4) gives
\((W'_a)^{4^{r_n}}=W'_a\). Also \(n\mid4^{r_n}-1\), so
all character values lie in \(E_n\). Hence the original phases,
as well as their canonical normalization, lie in \(E_n\).
Matrix covariance directly gives the same upper field bound for
A, even before a phase parametrization is assumed.

The reasoning is valid in the universal coordinate algebra of
the full phase equations. In particular it proves
\[
 W_a^{4^{r_n}}-W_a=0
 \tag{71.5}
\]
there. These polynomials are separable. The full phase coordinate
algebra is consequently a quotient of a finite etale algebra over
\(\mathbb F_4\), and is itself finite etale, possibly zero.
This supplies a characteristic-two reducedness theorem without
assuming nonemptiness. In particular the lengths in Section 70
are also the numbers of geometric points.

For \(n=3^k\), \(r_n=2n/3\). Section 65 shows that the
canonical first phase, and already the invariant row entry
\(R_2=(W'_1)^{-2}\), generates \(E_n\) over \(\mathbb F_4\).
Since R is unchanged by character gauge, every full phase solution
at this order has its matrix entries generating exactly
\[
 \boxed{E_n=\mathbb F_{2^{4n/3}}.} \tag{71.6}
\]
This is an equality of minimal fields in the stated normalized
phase framework, not only an available ambient field.

## 71.4 The remaining nonemptiness problem

Let \(\mathcal Z_k\) be the full cubic phase scheme at
\(n=3^k\), with Frobenius covariance imposed. Equations
(71.4)--(71.6) show that there is an integer \(b_k\ge0\) such
that
\[
 \boxed{\displaystyle
 \mathcal O(\mathcal Z_k)\cong
 \bigl(\mathbb F_{2^{4n/3}}\bigr)^{b_k}
 \quad\text{as }\mathbb F_4\text{-algebras}.}
 \tag{71.7}
\]
For \(b_k=0\) the algebra is zero and the scheme is empty.
Every nonempty factor has the full displayed residue field:
smaller factors are excluded by the necessary quadratic of
Section 65.

The full phase scheme before normalization is
\(\mu_n\times\mathcal Z_k\), by the unique normalization.
Since \(E_n\) contains all n-th roots of unity, its coordinate
algebra is \(E_n^{n b_k}\). Thus its geometric length is
\(n(2n/3)b_k\), while the canonical length is \((2n/3)b_k\).

The exhaustive finite searches and full cubic checks in Section 58
now prove the complete phase classifications
\[
 b_1=1,\qquad b_2=2,\qquad b_3=3,
\]
with canonical lengths 2, 12, 54 and total phase lengths 6, 108,
1458, respectively. These are complete classifications of the
characteristic-two solutions in the phase parametrization, not
merely searches in an optional Frobenius subfamily. They do not
classify arbitrary complex categories or prove that every complex
category has good reduction at 2.

For this construction route, infinitude is reduced to showing
\(b_k>0\) for unbounded k. Neither finite etaleness nor the
prescribed residue field proves that inequality. The arithmetic
branch counts of Section 63 suggest values for \(b_k\), including
8 at order 81, but identifying these integers with class numbers
remains an unproved additive construction statement.

`hi_char2_cubic_frobenius.py` checks both identities (71.3) on
arbitrary norm phases with nonzero Q and Frobenius defects at
orders 3, 5, 7, 9, 11, and 13. It separately verifies matrix
covariance on every saved characteristic-two branch at 3, 9, and
27, twists each by every cyclic character, and recovers the
original phases using (71.4). All exact checks pass; results are
saved in `hi_char2_cubic_frobenius_results.txt`.

**Infinitude remains unproved.** The new result removes the
Frobenius-gauge qualification from the full characteristic-two
phase search and identifies precisely which finite etale algebras
must be shown nonzero.

---

# 72. General doubling-orbit searches and complete finite counts through 31

The forced gauge of Section 71 gives a uniform search parametrization
for every odd cyclic order, including orders where 2 is not primitive
on the units. This leads to new exact workspace certificates at
15, 21, 23, and 31, and complete phase counts at every odd order
through 31. These remain finite results.

## 72.1 Arbitrary odd orders: paired orbits and norm orbits

Partition the nonzero indices into doubling orbits. Let O be the
orbit of a, of length r. Frobenius covariance says that its seed
\(x=W_a\) belongs to \(\mathbb F_{4^r}\), and determines all
other entries on O.

If \(-O\ne O\), the seed is any nonzero element of
\(\mathbb F_{4^r}\); the opposite orbit is then determined by
\(W_{-b}=\omega/W_b\). There are exactly \(4^r-1\) choices
for this pair of orbits.

If \(-O=O\), then r is even and \(2^{r/2}a=-a\). The seed
must satisfy
\[
 x^{2^r+1}=\omega,\qquad x\in\mathbb F_{2^{2r}}.
 \tag{72.1}
\]
There are exactly \(2^r+1\) choices, because this is a relative
norm fiber over \(\mathbb F_{2^r}\). The scalar
\(c=\omega^2\) has the required norm, so the fiber is
\(c\mu_{2^r+1}\).

These choices are independent across orbit pairs. Conversely they
produce every inverse-normalized Frobenius-covariant phase sequence.
All fields embed in \(E_n=\mathbb F_{4^{\operatorname{ord}_n(2)}}\).
Thus there is a finite, explicit search containing every full cubic
phase solution, with no assumption that its entries have the largest
possible field degree.

`hi_char2_general_search.py` implements this parametrization. Its
current C++ backend supports at most three independent seeds and
binary field degree below 63; these are implementation limits, not
mathematical restrictions. A common cyclic parameter group makes
all Q evaluations exact XORs of finite-field power-table entries.
The Q representatives use sign reversal, exchange, and doubling;
no unproved Galois action of other units is used.

## 72.2 Completed searches and independent verification

The following searches are exhaustive in the parametrization above.
Every resulting Frobenius orbit passes the independent verifier's
complete Q and C loops, including all exceptional indices.

| n | ambient binary field degree | independent seed-set sizes | assignments tested | canonical phase points | Frobenius orbits |
|---:|---:|:---|---:|---:|---:|
| 15 | 8 | 255, 17, 5 | 21,675 | 24 | 6 |
| 17 | 16 | 257, 257 | 66,049 | 16 | 2 |
| 19 | 36 | 262,145 | 262,145 | 36 | 2 |
| 21 | 12 | 4,095, 63, 5 | 1,289,925 | 48 | 8 |
| 23 | 22 | 4,194,303 | 4,194,303 | 44 | 4 |
| 25 | 40 | 1,048,577, 17 | 17,825,809 | 40 | 2 |
| 29 | 56 | 268,435,457 | 268,435,457 | 60 | 3 |
| 31 | 10 | 1,023, 1,023, 1,023 | 1,070,599,167 | 60 | 12 |

At every listed order other than 29, all orbits have length
\(\operatorname{ord}_n(2)\). At 29 the lengths are 28, 28,
and 4. The smaller orbit must be retained; imposing maximal first
phase degree would incorrectly discard valid full solutions.

For example, the order-31 first Q accepts 1,046,076 assignments,
whereas all Q accept only 60. At order 29, in contrast, all 60
first-Q assignments already pass the remaining Q and C. No uniform
first-Q completion statement is inferred.

By Section 71 these give complete classifications of the normalized
characteristic-two **phase points** at these orders, modulo cyclic
character gauge. They are not counts of inequivalent fusion categories.
The raw phase counts are n times the canonical counts. Together
with Sections 58 and 70, complete characteristic-two phase counts
and hence complex existence certificates are now available at every
odd order \(3\le n\le31\).

The saved JSON files have names
`hi_finite_field_certificates/hi_finite_field_N_char2_general_J.json`.
The combined log is `hi_char2_general_search_results.txt`.
Reproduction uses:

```sh
python hi_char2_general_search.py --orders 15 17 19 21 25
python hi_char2_general_search.py --orders 23 31 --max-table 5000000
python hi_char2_general_search.py --orders 29 --max-table 300000000
```

The last run uses about four GiB for its two power tables. The
third coefficient table has just one entry after dividing each
quadratic by \(\omega^2\): only a term with two zero indices
needs that coefficient, and its remaining indices are an inverse
pair. This optimization was checked against the completed order-15
and order-17 counts and their complete cubic certificates.

## 72.3 Completion of the full quadratic ideal at order 17

The previously running Magma calculation has completed. The full
order-17 Q ideal over \(\mathbb F_4\), with inverse norms and
without Frobenius covariance, has a Groebner basis of size 694 and
quotient dimension 272. Its source and output are saved as
`hi_char2_phase17_length.m` and `hi_char2_phase17_length_results.txt`.

Independently, the exhaustive search above and Section 71 give
exactly \(17\cdot16=272\) geometric points of the full C phase
scheme. That scheme is finite etale. The surjection from the Q
coordinate algebra to the Q-and-C coordinate algebra is therefore
between two vector spaces of dimension 272, and is an isomorphism.
Equivalently, the 272 distinct cubic points already exhaust the
entire length of the quadratic algebra, leaving no extra points
or nonreduced structure.
This proves
\[
 \boxed{Q\Longrightarrow C\quad\text{at }n=17
        \text{ in characteristic two}.} \tag{72.2}
\]
It also proves reducedness of that Q algebra. This argument does
not infer a characteristic-zero Q-to-C implication from a finite
special-fiber dimension; such an inference would need additional
control of specialization.

## 72.4 The full quadratic ideal also completes at order 15

A separate Magma run now gives the full order-15 quadratic algebra,
again without Frobenius covariance or a prescribed extension field.
Its 35 norm/Q generators produce a Groebner basis of size 693,
dimension zero, and quotient length 360. The completed basis
calculation used 57.570 CPU seconds in the saved run.

Section 72.2 independently gives 24 canonical cubic points and
therefore exactly \(15\cdot24=360\) raw cubic points. The same
surjection and length comparison as in Section 72.3 proves
\[
 \boxed{Q\Longrightarrow C\quad\text{at }n=15
        \text{ in characteristic two},}
\]
and proves that its full quadratic algebra is reduced. Combining
this with Sections 70 and 72.3 establishes the characteristic-two
implication at **every odd order from 3 through 17**. This is a
finite implication theorem, not a proof in unbounded order.

The source `hi_char2_phase1519_length.m` performs the order-15
calculation and then starts the same test at 19. Its output is
`hi_char2_phase1519_length_results.txt`. The order-19 computation
stopped without returning a basis or length; its execution handle
is now absent. A length
of 684 would match the independently known 36 canonical cubic
points, whereas any larger length would require further analysis;
neither result is assumed here.

The reduced order-81 SAT run, meanwhile, completed its one-hour
budget with neither SAT nor UNSAT. Its log is preserved in
`hi_char2_sat81_search_results.txt`. It supplies no existence or
nonexistence conclusion.

## 72.5 A separate benchmark with Frobenius covariance imposed

`hi_char2_canonical_ideal.py` generates Magma computations of the
norm/Q ideal together with every equation \(W_a^4=W_{2a}\).
The order-9 benchmark has 16 generators, a Groebner basis of size
29, and quotient length 12, as expected. The order-27 calculation
has 52 generators and stopped without returning a basis or a length;
its execution handle is now absent. Output is saved in
`hi_char2_canonical_ideal_results.txt`. This is a benchmark for a
different search formulation, not another existence certificate.

These canonical computations impose a substantive additional
condition compared with Sections 72.3--72.4. Their ambient Frobenius
algebra is already finite etale: each doubling orbit eliminates to
\(X^{4^r}-X\), whose derivative is -1. Consequently every quotient
of that ambient algebra is also reduced. In particular, the previously
exhaustive equality of canonical Q and C point sets through order 31
already implies equality of their canonical ideals. A new canonical
length computation at one of those orders would not strengthen this
to Q implies C without Frobenius covariance.

---

# 73. The count must include quadratic overorders

The complete finite counts reveal a more precise arithmetic target.
Counting the ray group of just one quadratic order misses genuine
solutions at orders 11 and 29.

Let
\[
 D=n^2+4=F^2D_0,\qquad
 K=\mathbb Q(\sqrt{D_0}),\qquad
 d=\frac{n+\sqrt D}{2},\qquad O_F=\mathbb Z[d].
\]
Here \(D_0\) is fundamental. For every \(f\mid F\), write
\(O_f=\mathbb Z+fO_K\), let \(h_f\) be its ordinary class
number, and set
\[
 m_f=[O_f^\times:O_F^\times].
\]
All these orders contain the norm-minus-one unit d. In particular
ordinary and narrow class numbers agree.
The symbol + in the ray modulus below means positivity at the
real embedding where \(d>0\).

## 73.1 A positive arithmetic count, proved independently of HI

The element d is the smallest unit greater than 1 in \(O_F\).
Indeed, for any such unit u, write
\(u-u'=b\sqrt D\), with a nonzero integer b. Since \(u>1\)
and \(u'=\pm u^{-1}\), b is positive. If the norm is -1, then
\(u+u^{-1}\ge\sqrt D=d+d^{-1}\), giving \(u\ge d\).
If the norm is +1, then \(u-u^{-1}\ge\sqrt D\), which gives
\(u>d\). Thus, if \(\epsilon_f>1\) generates the positive
unit group of \(O_f\), then \(d=\epsilon_f^{m_f}\).

Also \(\gcd(F,n)=1\). The quotient
\(O_f/(d-1)O_f\) is therefore \(\mathbb Z/n\mathbb Z\),
as is clear first for \(O_F\) by setting d equal to 1, and
then for every overorder by localization away from its index.
The image of \(\epsilon_f\) in this quotient has order exactly
\(m_f\). For \(0<a<m_f\), one has
\[
 0<\left|N_{K/\mathbb Q}(\epsilon_f^a-1)\right|<n,
\]
where the even-a norm is smaller than
\(\epsilon_f^a-\epsilon_f^{-a}\), and the odd-a norm equals
that number. Such an element cannot lie in an ideal of norm n.

The ray-class exact sequence, with the positivity condition at
one real place, consequently gives
\[
 \left|\operatorname{Cl}_{(d-1),+}(O_f)\right|
 =\frac{h_f\varphi(n)}{m_f}. \tag{73.1}
\]
Define the total arithmetic count
\[
 \boxed{\displaystyle
 \mathcal R(n)=\varphi(n)\sum_{f\mid F}\frac{h_f}{m_f}>0.}
 \tag{73.2}
\]
Every summand is an integer ray-class degree. This positivity is
an arithmetic theorem; it does not supply a phase solution.
The ray-class formalism for orders is the one used in Sections
32 and 63 and in
[Kopp--Lagarias, Corollary 6.7](https://arxiv.org/html/2212.09177v3#S6.SS2).

For explicit evaluation, put
\(u_f=[O_K^\times:O_f^\times]\) and \(m=u_F\). The quadratic
order class-number formula gives
\[
 h_f=\frac{h_1}{u_f}\,f\prod_{p\mid f}
                    \left(1-\frac{(D_0/p)}p\right),
 \qquad m_f=\frac m{u_f}.
\]
Thus the unit indices cancel inside the sum:
\[
 \boxed{\displaystyle
 \mathcal R(n)=\frac{h_1\varphi(n)}m
  \sum_{f\mid F} f\prod_{p\mid f}
                    \left(1-\frac{(D_0/p)}p\right).}
 \tag{73.3}
\]

## 73.2 Exact finite comparison and the corrected prediction

The canonical phase counts proved in Sections 58, 70, and 72 are

| n | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 29 | 31 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| canonical points | 2 | 4 | 6 | 12 | 12 | 12 | 24 | 16 | 36 | 48 | 44 | 40 | 54 | 60 | 60 |
| \(\mathcal R(n)\) | 2 | 4 | 6 | 12 | 12 | 12 | 24 | 16 | 36 | 48 | 44 | 40 | 54 | 60 | 60 |

At 11 the discriminant is \(5^2\cdot5\). The maximal order
contributes \(10/5=2\) and \(\mathbb Z[d]\) contributes 10,
for a total of 12.

At 29 the discriminant is \(13^2\cdot5\). The maximal order
contributes \(28/7=4\), while the order of conductor 13 has
class number 2 and contributes 56. The observed split into
Frobenius orbit lengths \(4,28,28\) matches these ray degrees.
This is an equality of finite counts; it is not by itself a
constructed bijection between points and ray classes.

**Proposed uniform count, still unproved.** The canonical full
characteristic-two phase algebra has dimension \(\mathcal R(n)\)
over \(\mathbb F_4\) for every odd \(n\ge3\).
A uniform construction giving even one point for unbounded n
would suffice for the user's infinitude goal; proving this entire
count formula is stronger than necessary. Its arithmetic right
side is already positive at every n.

This corrects the use of a single order class number as the full
prediction in nonfundamental discriminants. At \(n=6561=3^8\),
for example, \(F=5\), \(D_0=1721869\), and the unit index m
is 1. The maximal and conductor-5 class numbers are 96 and 384.
Formula (73.2) therefore predicts \(b_8=96+384=480\) in the
notation of Section 71, rather than 384. No HI solution is claimed
at that order. At 81 the discriminant is fundamental, so the
prediction remains 432 canonical points, or \(b_4=8\).
At 39 the predicted count is \(24+96=120\); existence and the
count there are also not established here.

`hi_char2_ray_count.py` certifies each maximal class group with
`bnfcertify`, computes the order unit indices exactly, evaluates
(73.1) for all overorders, and compares (73.2) with every completed
finite phase count. All comparisons pass. Its additional arithmetic
outputs at 39, 81, and 6561 explicitly make no HI assertion.

**Infinitude remains unproved.** The missing step is an additive
construction or lower bound for the full phase algebra, not the
existence or positivity of the ray-class inputs.

---

# 74. The scalar action, a split quotient, and a stronger finite ray comparison

The count in Section 73 admits a more informative comparison: the complete
action of \(U_n=(\mathbb Z/n\mathbb Z)^\times\), including its stabilizers.
There is also a uniform descent statement for the quotient by this action.
These results identify additional structure a construction must preserve;
they do not establish that the solution scheme is nonempty in new orders.

## 74.1 The quotient by scalar reindexing is split over \(\mathbb F_4\)

Let \(Z_n\) be the full cubic phase scheme in the unique Frobenius gauge
of Section 71, and let \(\mathcal A_n\) be its coordinate algebra over
\(\mathbb F_4\). This is finite étale, possibly the zero algebra. Scalar
reindexing acts by
\[
 (s\cdot W)_a=W_{sa},\qquad s\in U_n.
\]
Reindexing the summation variable proves preservation of all Q and C;
the inverse norms and canonical gauge are preserved as well.

**Theorem.** On \(Z_n\), field Frobenius \(W\mapsto W^4\) is exactly
the action of \(2\in U_n\). Consequently
\[
 \boxed{\mathcal A_n^{U_n}\cong\mathbb F_4^{\,c_n}}
 \tag{74.1}
\]
for an integer \(c_n\ge0\). It counts scalar orbits of canonical phase
points over the algebraic closure. In particular every such orbit is
defined over \(\mathbb F_4\), even when no point in that orbit is
\(\mathbb F_4\)-rational.

**Proof.** Section 71 gives the coordinate identities
\(W_a^4=W_{2a}\). Therefore, for every polynomial function f with
coefficients in \(\mathbb F_4\), one has \(f^4=2\cdot f\) in
\(\mathcal A_n\). An invariant f satisfies \(f^4=f\). The invariant
algebra is finite and reduced, and every residue field is consequently
\(\mathbb F_4\). This proves (74.1). Equivalently, on geometric points,
Frobenius acts within each scalar orbit. No averaging by \(|U_n|\) is
used; that number is even and is not invertible here. ∎

The same finite étaleness and split-quotient conclusions hold for the
**full normalized matrix scheme** defined by the order-three symmetry,
Q and C, without requiring a phase parametrization or nonzero generic
entries. Indeed (71.2) was proved at that matrix level. Each coordinate
satisfies \(A_{a,b}^{4^{r_n}}=A_{a,b}\), so this matrix scheme too is a
quotient of a finite étale scheme; on its coordinate algebra fourth
power is scalar reindexing by 2. This is a characteristic-two rigidity
statement for the normalized matrix equations. It is not a
nonemptiness theorem or an assertion that all matrix solutions have
the phase form.

More explicitly, let \(H\le U_n\) be the stabilizer of one point and set
\[
 r_H=\min\{r>0:2^r\in H\}.
\]
Its scalar orbit is the transitive \(U_n\)-set \(U_n/H\). Frobenius
has cycles of length \(r_H\) on this orbit, so its finite étale algebra is
\[
 \boxed{\left(\mathbb F_{4^{r_H}}\right)^{[U_n:H]/r_H}.}
 \tag{74.2}
\]
Thus stabilizers and their multiplicities determine both the complete
scalar action and the field-factor decomposition. This is stronger than
knowing the total number of geometric points.

There is a small uniform restriction on H: \(-1\notin H\). Otherwise
the inverse norm gives \(W_a^2=\omega\), hence
\(W_a=\omega^2\) for every nonzero a. The residual \(F(1,1)\) is then
\(\omega\ne0\), contradicting Q. In particular H has odd order when
n is an odd prime power, because \(U_n\) is cyclic with unique involution
\(-1\). This does not classify the possible stabilizers.

The quotient in (74.1) is a quotient of the displayed matrix/phase
scheme. No extra claim about descent of associators, or about equivalence
classes of all fusion categories, is needed for this statement.

## 74.2 The arithmetic action and its exact finite match

Retain \(D=n^2+4=F^2D_0\), \(O_f\), \(h_f\), and \(m_f\) from
Section 73. Let
\[
 H_f=\langle\epsilon_f\bmod(d-1)\rangle\le U_n,
 \qquad |H_f|=m_f.
\]
The one-positive-place ray-class exact sequence gives
\[
 1\longrightarrow U_n/H_f
 \longrightarrow\operatorname{Cl}_{(d-1),+}(O_f)
 \longrightarrow\operatorname{Pic}(O_f)\longrightarrow1.
 \tag{74.3}
\]
Hence, as a \(U_n\)-set, this ray group is a disjoint union of
\(h_f\) copies of \(U_n/H_f\). The choice of an origin in each copy
is not canonical. Since \(D_0\equiv5\pmod8\), the prime 2 is inert
in the quadratic field; it is coprime to F and to the odd ray modulus.
Its Artin element is the local class of the positive generator 2.
Thus Frobenius over the residue field \(\mathbb F_4\) acts by the same
element \(2\in U_n\). This uses the ray-class convention already fixed
in Sections 63 and 73 and the exact sequence for orders in
[Kopp--Lagarias, Corollary 6.7](https://arxiv.org/html/2212.09177v3#S6.SS2).

The strengthened proposed correspondence is therefore
\[
 \boxed{Z_n(\overline{\mathbb F}_2)
 \ \cong\ \coprod_{f\mid F}\coprod_{j=1}^{h_f} U_n/H_f}
 \quad\text{as }U_n\text{-sets},
 \tag{74.4}
\]
with Frobenius acting by 2 on both sides. It would imply the count of
Section 73, the predicted residue fields, and
\(c_n=\sum_{f\mid F}h_f\). Formula (74.4) is **not proved uniformly**.

**Exact finite result.** Formula (74.4), as an abstract equivariant
bijection, holds at every odd \(3\le n\le31\). The numbers of scalar
orbits are

| n | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 29 | 31 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| scalar orbits | 1 | 1 | 1 | 2 | 2 | 1 | 3 | 1 | 2 | 4 | 2 | 2 | 3 | 3 | 2 |

All stabilizers are trivial except the following two single orbits:
\[
 \begin{array}{c|c|c}
 n&H&\text{orbit size}\\\hline
 11&\{1,3,4,5,9\}=\langle4\rangle&2\\
 29&\{1,7,16,20,23,24,25\}=\langle24\rangle&4.
 \end{array}
\]
These are exactly the maximal-order unit images in the two
\(\mathbb Q(\sqrt5)\) cases. At 31, for example, the twelve Frobenius
orbits of length 5 combine into two scalar orbits of length 30, rather
than twelve different scalar orbits.

`hi_char2_scalar_action.py` reconstructs the canonical phases from the
independently verified row certificates, generates every Frobenius
conjugate, and checks closure under every unit reindexing. It computes
the actual stabilizer subgroups, not only their orders. On the arithmetic
side it certifies the maximal class number and computes the unit images
exactly. Matching transitive-orbit stabilizers and multiplicities proves
the claimed abstract finite bijections. It does not construct a Stark
unit or a distinguished assignment of phase solutions to ideal classes.
The additional arithmetic outputs at 39, 81, and 6561 remain predictions
without HI existence assertions.

In particular (74.1) does not turn the problem into finding a rational
point on a known nonempty scheme: the integer \(c_n\) can still be zero
without contradicting any of its uniform proof. A nonzero map from a
constructed ray-class family to the phase scheme, or another uniform
positive lower bound, remains missing. **Infinitude is not established.**

---

# 75. A fixed-period lens product for the uniform analytic candidate

The Shintani candidate of Section 51 has a second exact expression, with
one pair of positive periods for each n. This connects it directly to
the lens quantum dilogarithm, and recovers the exceptional phase at zero
from the same product. The additive HI identities remain unproved.

## 75.1 The product and its origin value

Put
\[
 d=\frac{n+\sqrt{n^2+4}}2,\quad
 \omega_1=d,\quad\omega_2=d^{-1},\quad
 \omega_1-\omega_2=n,
\]
and write \([b]_n\in\{0,\ldots,n-1\}\) for the least residue. Extend
the notation for the double sine by homogeneity in its two periods.

**Theorem.** For every odd \(n\ge3\) and \(1\le a<n\), the positive
number \(q_a\) of (51.3) is
\[
 \boxed{\displaystyle
 q_a=\prod_{j=0}^{n-1}
 \operatorname{Sin}_2\!\left(
 \frac{a+\omega_2+j\omega_1+[-a-1-j]_n\omega_2}{n};
 \omega_1,\omega_2\right).}
 \tag{75.1}
\]
The same displayed product at \(a=0\) equals d. Thus, defining
\(q_0=d\), the single formula
\[
 W_a=-(-1)^{a(a+n)/2}\sqrt{q_a/d},\qquad 0\le a<n,
 \tag{75.2}
\]
recovers all phases of Section 51, including \(W_0=-1\).

Every double-sine argument in (75.1) is in its positive strip. Indeed
the numerator is positive and is at most
\(a+(n-1)\omega_1+n\omega_2<n(\omega_1+\omega_2)\), since
\(a<n<\omega_1\).

Here is the change of variables proving (75.1). In the original basis
of Section 23, let
\[
 \tau=d^{-1},\quad
 P=\begin{pmatrix}1&n\\n&n^2+1\end{pmatrix},\quad
 \mathbf r=\frac an\binom11.
\]
Then \(P\tau=\tau\), and
\(\mathbf r-P\mathbf r=(-a,-(n+1)a)^{\mathsf T}\).
The positive characteristic here is the inverse label to the negative
characteristic used for \(q_a\). Its Shintani cocycle has absolute
value \(q_a^{-1}\), by Section 51 and its inverse symmetry.

Use the unnormalized lens function \(\gamma_M\) with the conventions
\(M=\left(\begin{smallmatrix}-p&-s\\k&-r\end{smallmatrix}\right)\)
of [Sarkissian--Spiridonov, Section 2](https://arxiv.org/html/1910.11747#S2).
For P these parameters are
\[
 k=n,\quad p=-1,\quad r=-n^2-1,\quad s=-n.
\]
Before scaling the periods, take \((\Omega_1,\Omega_2)=(d^2,1)\).
Its denominator argument is \((\mu+m)/n\). Substitution of the
characteristic gives
\[
 m=-(n+1)a-1,\qquad \mu=1+a(\tau+n)=1+ad.
 \tag{75.3}
\]
Indeed \((\mu+m)/n=a(\tau-1)/n\), and the numerator argument is
\((m+1)P\tau+(\mu+m)/(n(n\tau+n^2+1))\), modulo the integer a.
These are exactly the two arguments in the Shintani cocycle ratio.
The equality holds first in the upper half-plane, with the periods
and \(\mu\) varying as prescribed by \(\tau\), and then by analytic
continuation at the RM point. It does not cancel two divergent products
on the unit circle.

The unnormalized lens function is periodic in m, so reduce
\(m\equiv-a-1\pmod n\). Replacing \(r=-n^2-1\) by \(-1\)
changes its base parameter \(\tau\) by an integer n and leaves the
unnormalized function unchanged. The corresponding modular matrix is
\(L_n=\left(\begin{smallmatrix}1&0\\n&1\end{smallmatrix}\right)\).
The finite-product identity for this function has summation pairs
\((j,\gamma)\) satisfying \(j+\gamma\equiv m\pmod n\).
Taking its absolute value at positive real periods gives
\[
 q_a^{-1}=\prod_{j=0}^{n-1}
 \operatorname{Sin}_2\!\left(
 \frac{1+ad+jd^2+[-a-1-j]_n}{n};d^2,1\right)^{-1}.
\]
Scaling both periods and arguments by \(d^{-1}\) proves (75.1).
This remains the order-\(\mathbb Z[d]\) candidate of Section 51;
no maximal-order substitution is being made.

For the origin assertion, the arguments in (75.1) become
\(\omega_2+j\). Reflection pairs j with n-j for
\(1\le j<n\), because
\(\omega_1+\omega_2=n+2\omega_2\). Their factors cancel.
The remaining factor is
\[
 \operatorname{Sin}_2(\omega_2;\omega_1,\omega_2)
 =\sqrt{\omega_1/\omega_2}=d,
\]
which proves the asserted origin value. ∎

## 75.2 An explicit sign and the remaining integral problem

The normalization in the cited paper can also be made explicit here.
For \(0\le m<n\), its normalized lens gamma for \(L_n\) satisfies
\[
 \Gamma_{L_n}(\mu,m;\omega_1,\omega_2)
 =(-1)^{m(m+3)/2}
 \prod_{j=0}^{n-1}
 \operatorname{Sin}_2\!\left(
 \frac{\mu+j\omega_1+[m-j]_n\omega_2}{n};
 \omega_1,\omega_2\right)^{-1}.
 \tag{75.4}
\]
In particular (75.1) is an evaluation along the discrete line
\(\mu=a+\omega_2,\ m=[-a-1]_n\), with a specified sign, rather
than an unspecified normalization of the lens function.

For completeness the phase cancellation is an elementary calculation.
Set \(S_m=\sum_{j=0}^{n-1}j[m-j]_n\). Splitting the sum at j=m gives
\[
 S_m=\frac{n(n^2-1)}6+\frac{nm(n-m-2)}2.
\]
The difference between the sum of the n Bernoulli polynomials in the
product and \(1/n\) times the unshifted Bernoulli polynomial is
\(- (n-1)^2/(2n)+2S_m/n^2\). Adding the normalization phase
\((n-1)(n-5)/(12n)+(n+1)m(m+2)/(2n)\) leaves
\(m(m+3)/2\), proving (75.4). This calculation is independent of
the RM equation and of the continuous argument \(\mu\).

The two elementary period shifts also give a useful equation along the
sampling line. With \(x=(\mu+m\omega_2)/(n\omega_2)\), their quotient
is
\[
 \frac{\Gamma_{L_n}(\mu+n,m)}{\Gamma_{L_n}(\mu,m)}
 =\frac{\sin(\pi x)}{\sin(\pi(x-\mu+\omega_2))}.
 \tag{75.5}
\]
Here one first shifts by \(\omega_1\) and then back by \(\omega_2\);
the two changes of the discrete index cancel. The difference between
the two sine arguments is \(\mu-\omega_2\), since
\(\omega_1-\omega_2=n\) and \(\omega_1\omega_2=1\).
At \(\mu=\omega_2+a\), with integer a and nonzero denominator, the
ratio is \((-1)^a\). At the exceptional point
\((\mu,m)=(\omega_2,-1)\), the ratio is a removable \(0/0\): its
limit is \(\omega_1/\omega_2=d^2\). Thus the sampling line has a
specific exceptional multiplier. The shift formula alone supplies no
finite-sum identity for its values.

The published lens identities include a continuous integral in addition
to the finite sum. Applying the six-factor identity to the HI candidate
still requires a reduction of that integral and a treatment of the
square roots in (75.2).
[Sarkissian--Spiridonov, Sections 3--4](https://arxiv.org/html/1910.11747#S3).
There is a concrete mismatch in the direct substitution: three factors
with shifts \(a_i\) and three with shifts \(c_j\) on our line have
continuous parameter sum
\[
 6\omega_2+\sum_i a_i+\sum_j c_j.
\]
The HI balance makes the integer sum a multiple of n, whereas the
six-factor integral balance requires \(\omega_1+\omega_2=n+2\omega_2\).
Their difference cannot vanish for any choice of integer lifts, because
\(4\omega_2\) is irrational. The discrete parameter sum is
\(-6\pmod n\), while the same integral requires \(-2\pmod n\),
which also fails at every odd \(n\ge3\). Thus the direct line evaluation
does not apply that theorem. This calculation does not exclude a transformation
with additional factors, a different integral identity, or a suitable
finite invariant subspace of the integral operator.

`hi_shintani_lens.py` checks the Bernoulli/sign calculation exactly off
the RM locus. It also compares the two independently evaluated positive
double-sine products and their inverse norms numerically, and recovers
the origin value. These checks verify the implementation of the proved
change of variables; they do not replace the missing additive proof.
**Infinitude remains unproved.**

---

# 76. The Shintani product is the square of one double sine

The square-root difficulty left in Section 75 can be removed uniformly.
The candidate phases themselves, with their fixed signs, are values of
one ordinary double sine. Its meromorphic extension has an exact jump
on integer translates that accounts for the exceptional origin.

## 76.1 A product identity away from the RM specialization

Write \(S(z;u,v)=\operatorname{Sin}_2(z;u,v)\), in the convention
of Section 51. For every integer \(N\ge1\), \(b>0\), and
\(0<v<b+1\), one has
\[
 \boxed{\displaystyle
 \prod_{j=0}^{N-1}S(b+v+j;b+N,b)
 =\frac{S(v;b,1)}{S(v;b+N,1)}.}
 \tag{76.1}
\]
All the arguments are in their positive convergence strips.

**Proof.** Insert the integral (51.8), in its homogeneous two-period
form, on both sides. In the sum of its hyperbolic-sine terms use
\[
 \sum_{j=0}^{N-1}\sinh((N-2v-2j)t/2)
 =\frac{\sinh(Nt/2)}{\sinh(t/2)}\sinh((1-2v)t/2),
\]
and
\[
 \frac{\sinh(Nt/2)}{\sinh((b+N)t/2)\sinh(bt/2)}
 =\coth(bt/2)-\coth((b+N)t/2).
\]
Expanding the two hyperbolic sines on the right of (76.1) gives this
same expression; their cosh terms cancel. The linear subtraction terms
also agree, by \(N/(b(b+N))=1/b-1/(b+N)\). The convergent logarithmic
integrals are therefore equal. Positivity proves the stated identity
without a root-of-unity ambiguity. ∎

## 76.2 The formula with one factor per phase

Retain \(d=(n+\sqrt{n^2+4})/2\), and put
\[
 \lambda=\frac{d}{d+1}=\frac{d-1}{n}.
\]

**Theorem.** At every odd \(n\ge3\), the numbers of Sections 51 and 75
satisfy
\[
 \boxed{\displaystyle
 q_a=S(1+\lambda a;d,1)^2,\qquad 0\le a<n,}
 \tag{76.2}
\]
with \(q_0=d\). Consequently the candidate phases are exactly
\[
 \boxed{\displaystyle
 W_a=-\frac{(-1)^{a(a+n)/2}}{\sqrt d}\,
 S(1+\lambda a;d,1),\qquad 0\le a<n.}
 \tag{76.3}
\]
In particular there is no square root of a special-function value in
this expression. The positive constant \(\sqrt d\) and the displayed
elementary signs fix its normalization.

**Proof.** Let \(1\le a<n\), \(b=d^{-1}\), and \(v=a/(d+1)\).
In (75.1), the arguments with \(0\le j<n-a\) are \(b+v+j\);
the other a arguments are \(b+v+j+b\). Shifting those latter factors
back by b gives
\[
 q_a=
 \frac{\prod_{j=0}^{n-1}S(b+v+j;d,b)}
      {\prod_{k=1}^{a}2\sin(\pi(k-v)/d)}.
 \tag{76.4}
\]
Use (76.1), \(d=b+n\), and homogeneity to replace the numerator by
\(S(dv;d,1)/S(v;d,1)\). The a shifts by the period 1 give
\[
 \frac{1}{\prod_{k=1}^{a}2\sin(\pi(k-v)/d)}
 =\frac{S(a+1-v;d,1)}{S(1-v;d,1)}.
\]
Here \(a+1-v=1+dv\). Reflection and the period-d shift imply
\(S(v;d,1)S(1-v;d,1)=2\sin(\pi v)\), while the period-1 shift gives
\(S(dv;d,1)=2\sin(\pi v)S(1+dv;d,1)\). Substitution into (76.4)
proves (76.2), since \(dv=\lambda a\).

At a=0 use \(S(1;d,1)=\sqrt d\). Every factor in (76.2) is positive,
so taking the positive square root recovers (76.3) exactly. ∎

The inverse norms now follow immediately from reflection:
\(1+\lambda(n-a)=d-\lambda a\). Combining this with the opposite
signs at a and n-a gives \(W_aW_{n-a}=-d^{-1}\). This proves the
normalization, but still does not prove any of the missing additive
equations.

## 76.3 A meromorphic interpolation and an exact integer jump

Define the meromorphic function
\[
 f_n(z)=-d^{-1/2}e^{\pi i z(z+n)/2}S(1+\lambda z;d,1).
\]
It agrees with \(W_a\) at \(a=0,\ldots,n-1\). The two elementary
shifts and reflection of the double sine prove
\[
 \boxed{\displaystyle
 \frac{f_n(z+n)}{f_n(z)}
 =-e^{\pi i n z}
   \frac{\sin(\pi z/(d+1))}{\sin(\pi\lambda z)},}
 \tag{76.5}
\]
and
\[
 \boxed{\displaystyle
 f_n(z)f_n(-z)
 =d^{-1}e^{\pi i z^2}
   \frac{\sin(\pi\lambda z)}{\sin(\pi z/(d+1))}.}
 \tag{76.6}
\]
These are identities of meromorphic functions, with removable values
interpreted by limits.

Since \(\lambda+1/(d+1)=1\), for every nonzero integer a the sine
ratio in (76.5) is \((-1)^{a+1}\). Its prefactor cancels this sign.
At zero the ratio is \(1/d\), and hence
\[
 f_n(a+n)=f_n(a)\ (a\in\mathbb Z\setminus\{0\}),\quad
 f_n(0)=-1,\quad f_n(n)=d^{-1}.
\]
Equivalently, the entire integer sequence obeys
\[
 \boxed{\displaystyle
 f_n(a+n)-f_n(a)=(1+d^{-1})\,\mathbf1_{a=0}.}
 \tag{76.7}
\]
No nonzero integer makes either sine vanish, because the two slopes are
irrational. Thus this argument includes negative integer a, without
omitting other exceptional residues. Equation (76.6) likewise gives
\(f_n(a)f_n(-a)=-d^{-1}\) at every nonzero integer, and the limiting
value 1 at zero.

This gives a precise possible starting point for a contour or
periodization argument: the finite matrix phases are one period of a
specified meromorphic function, whose integer period defect is exactly
one delta term. Such an argument still has to prove the finite sums Q
and C. The interpolation identities do not imply those sums by
themselves. The direct balancing calculation of Section 75 concerned
the lens integral; (76.3) removes its square-root issue by passing to an
ordinary double sine, but supplies no completed integral-to-finite-sum
reduction.

`hi_shintani_single.py` verifies (76.1) numerically away from the RM
specialization, compares (76.2) with the earlier continued-fraction
product, and checks Q and all cross-free cubic orbits numerically at
the requested finite orders. These numerical checks support the
implementation of the proved formulas. **The additive identity, and
therefore infinitude, remains unproved.**

---

# 77. The full lens product factors, and its contour boundary terms

The simplification in Section 76 extends off the sampling line. This
gives an explicit integrand for further work with the lens beta identity.
It also makes two limitations of a direct contour argument precise.

## 77.1 Two factors at every continuous argument

Set \(b=d^{-1}\), and for \(0\le m<n\) define
\[
 P_n(\mu,m)=\prod_{j=0}^{n-1}
 S\!\left(\frac{\mu+jd+[m-j]_n b}{n};d,b\right).
\]
Then, as an identity of meromorphic functions of \(\mu\),
\[
 \boxed{\displaystyle
 P_n(\mu,m)=
 S\!\left(\frac{d\mu+m}{n};d,1\right)
 S\!\left(\frac{d(n-m)-\mu}{n};d,1\right).}
 \tag{77.1}
\]
The product identity itself works for every integer \(n\ge1\).
We retain odd \(n\ge3\) for the HI application.

**Proof.** Put \(a=n-m-1\) and
\(v=(\mu+(m-n)b)/n\). Initially choose real \(0<v<1\),
so all the factors below are in their positive strips. The arguments
with \(j\le m\) are \(b+v+j\), while those with \(j>m\)
are \(b+v+j+b\). The same shifts as in (76.4) give
\[
 P_n(\mu,m)=
 \frac{S(dv;d,1)}{S(v;d,1)}
 \frac{S(a+1-v;d,1)}{S(1-v;d,1)}.
\]
Since \(S(v)S(1-v)=2\sin(\pi v)\) and
\(S(dv)=2\sin(\pi v)S(1+dv)\), this equals
\(S(1+dv)S(n-m-v)\). The two arguments are respectively
\((d\mu+m)/n\) and \((d(n-m)-\mu)/n\).
Meromorphic continuation proves (77.1) at all other arguments. ∎

Consequently the normalized lens gamma of Section 75 has the formula
\[
 \Gamma_L(\mu,m)=
 \frac{(-1)^{m(m+3)/2}}
 {S((d\mu+m)/n;d,1)S((d(n-m)-\mu)/n;d,1)}.
 \tag{77.2}
\]
Here m is the representative \(0,\ldots,n-1\); one must retain
the prescribed discrete normalization when changing representatives.

The two arguments coincide precisely on \(\mu+m=d-1\).
At \(\mu=a+b\), \(m=n-a-1\), both equal
\(1+da/(d+1)\). Thus (76.2) is the restriction of (77.1)
to this diagonal, including its removable endpoint at a=0.

There is also an exact normalization at the pole used in beta-integral
residue arguments. The period-1 shift and \(S(1;d,1)=\sqrt d\)
give \(S(z;d,1)\sim2\pi z/\sqrt d\) at zero. Reflection gives
\(S(d;d,1)=1/\sqrt d\). Therefore
\[
 P_n(\mu,0)\sim\frac{2\pi\mu}{n},\qquad
 \boxed{\operatorname*{Res}_{\mu=0}\Gamma_L(\mu,0)
 =\frac{n}{2\pi}.}
 \tag{77.3}
\]
This agrees with the general normalization in the residue computation
preceding the theorem of
[Sarkissian--Spiridonov, Section 3](https://arxiv.org/html/1910.11747#S3).
The present derivation uses only the two ordinary factors.

## 77.2 Integer values and derivatives have different shift defects

Let \(f=f_n\) be (76.3)'s meromorphic interpolation, and retain
\(\nu=1/(d+1)\), \(\lambda=1-\nu\). Although f has the
single integer-value defect (76.7), its derivatives have additional
terms at every nonzero integer a:
\[
 \boxed{\displaystyle
 f'(a+n)-f'(a)=
 \pi\bigl(in+\cot(\pi\nu a)\bigr)f(a).}
 \tag{77.4}
\]
For the second logarithmic derivative one similarly has
\[
 \left(\frac{f'}f\right)'(a+n)
 -\left(\frac{f'}f\right)'(a)
 =\pi^2(\lambda-\nu)\csc^2(\pi\nu a).
 \tag{77.5}
\]
These formulas involve no choice of logarithm.

**Proof.** Logarithmically differentiate the meromorphic ratio (76.5).
Its first derivative is
\[
 \pi in+\pi\nu\cot(\pi\nu z)
          -\pi\lambda\cot(\pi\lambda z).
\]
At a nonzero integer, \(\cot(\pi\lambda a)=-\cot(\pi\nu a)\),
and the ratio itself is 1. This proves (77.4). A further derivative,
using \(\csc^2(\pi\lambda a)=\csc^2(\pi\nu a)\), gives
(77.5). Irrationality of the slopes ensures all these evaluations are
regular. At zero the removable ratio gives instead
\(f'(n)=-f'(0)/d+\pi in/d\). ∎

Thus a contour with multiple poles at the integers cannot treat the
derivative contributions as periodic up to the single origin term.
Equations (77.4)--(77.5) supply the missing terms explicitly.

## 77.3 A growth obstruction for the direct vertical integral

Rescale the periods to
\[
 A=d+1,\qquad B=1+d^{-1},\qquad
 A-B=n,\quad AB=A+B=:Q_*.
\]
Homogeneity gives
\(S(1+\lambda z;d,1)=S(B+z;A,B)\).
The usual positive-period asymptotic is
\[
 \log|S(u+iy;A,B)|
 =-\frac{\pi|y|}{AB}\left(u-\frac{A+B}{2}\right)+o(1)
 \quad(y\longrightarrow\pm\infty),
 \tag{77.6}
\]
for fixed real u. For these quadratic-irrational periods this follows
directly from the convergent upper-half-plane expansion in
[Koyama--Kurokawa, Theorem 2](https://doi.org/10.1112/S0010437X04000521),
and real conjugation gives the lower half-plane. Their double-sine
convention is the same as ours.

Let \(a_1,\ldots,a_r,c_1,\ldots,c_r\) be real numbers with
\(\sum_i a_i+\sum_jc_j=0\), and set \(s=\sum_i a_i\).
The balanced product
\[
 \Phi_r(z)=\prod_{i=1}^r f(z+a_i)
           \prod_{j=1}^r f(c_j-z)
\]
then satisfies the uniform formula
\[
 \boxed{\displaystyle
 \log|\Phi_r(x+iy)|=
 \frac{\pi r n}{Q_*}|y|-2\pi(rx+s)y-r\log d+o(1).}
 \tag{77.7}
\]
Indeed, the elementary Gaussian factors contribute
\(-2\pi(rx+s)y\). The sum of the real sine arguments minus
their half-period centers is \(2rB-r(A+B)=-rn\), proving
the remaining exponential term by (77.6).

At every fixed x, at least one vertical end has positive exponential
growth. Multiplication by an exponential \(e^{2\pi itz}\), with
real t, cannot change the sum of the two growth rates. Thus this
balanced product does not by itself give an absolutely convergent
vertical integral.

Even the simple-pole kernel \(1/\sin(\pi z)\) is insufficient
for both the quadratic and cubic products, r=2 and r=3. It subtracts
\(\pi|y|\) from (77.7), whereas
\[
 \frac{2n}{Q_*}>1\qquad(n\ge3).
\]
For this last inequality, \(Q_*=\sqrt{n^2+4}+2<2n\), as
is seen by squaring \(\sqrt{n^2+4}<2n-2\).
Higher-order poles can supply sufficient decay, but introduce the
derivative terms in Section 77.2. This rules out the indicated direct
absolutely convergent integrals, not deformed contours, subtraction
procedures, or other reductions of the beta identity.

## 77.4 Repairing the beta balance with four explicit shifts

There is nevertheless a convergent ordinary beta integral containing
the desired six sine factors. Write \(S_*(x)=S(x;A,B)\).
Let \(a_1,a_2,a_3,c_1,c_2,c_3\) satisfy
\[
 \sum_i a_i+\sum_j c_j=n.
 \tag{77.8}
\]
Initially impose
\(a_1,a_2,c_1,c_2<0\) and \(a_3,c_3<A\), so the six
gamma parameters used below are positive. Then
\[
 \boxed{\displaystyle
 \int_{-i\infty}^{i\infty}
 \frac{\prod_{i=1}^3S_*(B+z+a_i)S_*(B-z+c_i)}
      {\prod_{i=1}^2
       2\sin(\pi(z+a_i)/B)\,2\sin(\pi(c_i-z)/B)}
 \frac{dz}{i\sqrt{AB}}
 =
 \frac{2\sin(\pi(A-a_3-c_3)/B)}
      {\prod_{i,j=1}^2 2\sin(\pi(a_i+c_j)/B)}
 \prod_{i,j=1}^3 S_*(B+a_i+c_j).}
 \tag{77.9}
\]
Removable factors on either side are interpreted by continuation of the
whole expression. More general parameters require the usual continued
contour separating the two families of gamma poles.

**Proof.** Put \(\gamma_*(x)=1/S_*(x)\). Apply the ordinary
three-plus-three hyperbolic beta integral, the k=1 case of
[Sarkissian--Spiridonov, equation (69)](https://arxiv.org/html/1910.11747#S4),
to the parameters
\[
 (-a_1,-a_2,A-a_3),\qquad
 (-c_1,-c_2,A-c_3).
\]
Their sum is \(2A-n=A+B\), exactly the required balance.
Reflection and the period-A shift give
\[
 \gamma_*(A-x)=S_*(B+x),\qquad
 \gamma_*(-x)=-\frac{S_*(B+x)}{2\sin(\pi x/B)},
\]
and
\[
 \gamma_*(2A-x)=2\sin(\pi(A-x)/B)S_*(B+x).
\]
The four shifted factors on the left give the four sine denominators;
their four minus signs cancel. On the right, the pairs with i,j at
most 2 give four denominators and four cancelling minus signs. The
pair (3,3) gives the displayed numerator, while the other four pairs
are unshifted. This proves (77.9). ∎

For these real parameters its integrand has modulus asymptotic to a
constant times \(e^{-2\pi|\operatorname{Im}z|}\). Indeed, (77.8)
changes the six-sine growth rate to \(2\pi n/(AB)\), and the four
denominators subtract \(4\pi/B\); their difference is exactly
\(-2\pi\), since \(AB=A+B\).

The normalization also agrees exactly with that of the desired finite
identity. Define the canonical cyclic samples
\[
 V_a=(-1)^{a(a+n)/2}S_*(B+a)=-\sqrt d\,W_a,
 \qquad 0\le a<n.
\]
For balanced residues with no \(a_i+c_j=0\) modulo n, the cross-free
HI cubic identity is equivalent to
\[
 \boxed{\displaystyle
 \frac1{\sqrt{AB}}\sum_{m\in\mathbb Z_n}
   \prod_{i=1}^3V_{m+a_i}\prod_{j=1}^3V_{c_j-m}
 =\prod_{i,j=1}^3V_{a_i+c_j}.}
 \tag{77.10}
\]
This follows by substituting \(W=-V/\sqrt d\) into the beta form
of C, and using \((d+1)/\sqrt d=\sqrt{AB}\).
Equation (77.10) is the **unproved target**, not a consequence of
(77.9). The sine denominators and numerator in (77.9), the passage
from the continuous contour to canonical samples, and the origin
corrections still have to be accounted for. The quadratic and collision
equations also remain to be established uniformly. The four-shift
calculation supplies a correctly balanced integral for that work.

`hi_shintani_beta.py` checks the normalization of (77.9) independently
by numerical integration at n=3 and
\(a=c=(-1/2,-1/2,5/2)\). With 64 Gauss--Legendre nodes on each
half of the truncated contour, the integral and product agree to
\(4.9\times10^{-20}\). This is a numerical check of the continuous
identity; it does not verify an integral-to-finite-sum reduction.

`hi_shintani_meromorphic.py` independently compares the n-factor lens
product with (77.1) off the diagonal, checks (76.5)--(76.7) at complex
and integer arguments, and recovers (77.3) by a symmetric numerical
limit. The saved runs at n=3,7,11 all pass. No finite additive equation
is deduced from these meromorphic formulas; **infinitude remains
unproved**.

---

# 78. Rational monodromy of the quadratic and cubic kernels

The same two rational functions control the n-shift of all the
double-sine factors in a summation kernel. Their degrees depend on
the number of factors, rather than on n.

## 78.1 A rational function of degree r

Retain \(A=d+1\), \(B=1+d^{-1}\), so
\(A-B=n\), \(AB=A+B\), and \(A^{-1}+B^{-1}=1\).
Put
\[
 F(z)=S(B+z;A,B)=S(1+z/B;d,1).
\]
The period shifts give the meromorphic identity
\[
 \frac{F(z+n)}{F(z)}
 =\frac{\sin(\pi z/A)}{\sin(\pi z/B)}.
 \tag{78.1}
\]
For r=2 or r=3 choose integer lifts \(a_i,c_j\) satisfying
\[
 \sum_i a_i+\sum_jc_j=(r-2)n,
 \qquad
 \Psi_r(z)=\prod_iF(z+a_i)\prod_jF(c_j-z).
\]
The r=2 balance is that of the quadratic kernel; the r=3 balance
is the one used in (77.8). Define
\[
 q=e^{2\pi i/d},\qquad
 \alpha_i=e^{2\pi ia_i/A},\qquad
 \beta_j=e^{2\pi i(c_j-n)/A},
\]
\[
 P(X)=\prod_i(1-\alpha_iX),\qquad
 D(X)=\prod_j(1-X/\beta_j),\qquad H(X)=P(X)/D(X).
\]
The balance and \(n/A=1-d^{-1}\) imply
\[
 \prod_i\alpha_i\prod_j\beta_j=q^2,
 \qquad H(0)=1,\qquad H(\infty)=q^2.
 \tag{78.2}
\]
For \(x=e^{2\pi iz/A}\), \(y=e^{-2\pi iz/B}\), and
\(t=e^{2\pi iz}\), one has \(x=ty\) and
\[
 \boxed{\displaystyle
 \frac{\Psi_r(z+n)}{\Psi_r(z)}=\frac{H(x)}{H(y)}.}
 \tag{78.3}
\]

**Proof.** Apply (78.1) to the positive arguments and its inverse
to the negative arguments. Write each sine as a difference of
exponentials. The facts that the lifts are integers and
\(A^{-1}+B^{-1}=1\) identify the two sets of exponential
parameters. For example,
\(e^{2\pi ia_i/B}=\alpha_i^{-1}\).
The constant left by these conversions is removed by (78.2),
giving (78.3). All steps are meromorphic identities, so the
formula extends across removable zero-over-zero expressions. ∎

At a regular integer m, \(x=y\), and the shift ratio is one.
The exceptional integers are among \(-a_i\) and \(c_j-n\),
where the origin jump of an individual factor can occur. In
particular, this statement does not discard the canonical-sample
corrections of Sections 76--77.

## 78.2 A nonsingular matrix of size two or three

Define the symmetric Bezout polynomial
\[
 \mathcal B(X,Y)=
 \frac{P(X)D(Y)-P(Y)D(X)}{X-Y}
 =\sum_{i,j=0}^{r-1} b_{ij}X^iY^j.
\]
It has degree at most r-1 in each variable. Equation (78.3) gives
the exact divided difference
\[
 \boxed{\displaystyle
 \frac{\Psi_r(z+n)-\Psi_r(z)}{e^{2\pi iz}-1}
 =\Psi_r(z)\frac{y\,\mathcal B(x,y)}{D(x)P(y)}.}
 \tag{78.4}
\]
The matrix \(\mathsf B_r=(b_{ij})\) satisfies
\[
 \det\mathsf B_r=(-1)^{r(r-1)/2}\operatorname{Res}(P,D),
 \qquad
 \operatorname{Res}(P,D)
 =\frac{\prod_{i,j}(1-\alpha_i\beta_j)}
        {(\prod_j\beta_j)^r}.
 \tag{78.5}
\]
The second equality follows by evaluating D at the roots
\(\alpha_i^{-1}\) of P, with multiplicities; the first is the
Bezout determinant identity. The exact polynomial checks in the
script below verify the determinant signs for both r=2 and r=3.

If all \(a_i+c_j\ne0\pmod n\), these determinants are nonzero.
Indeed, \(\alpha_i\beta_j=1\) would imply
\((a_i+c_j-n)/A\in\mathbb Z\); since A is irrational, this
forces \(a_i+c_j=n\), contrary to the cross-free condition.
Thus H has degree exactly r and \(\mathsf B_r\) has rank r.
Repeated lifts within one of the two lists cause no difficulty.

At every nonexceptional integer m, differentiating (78.3) yields
\[
 \frac{\Psi_r'(m+n)}{\Psi_r(m+n)}-
 \frac{\Psi_r'(m)}{\Psi_r(m)}
 =2\pi i\,x\frac{H'(x)}{H(x)},
 \qquad x=e^{2\pi im/A}.
 \tag{78.6}
\]
Correspondingly, the removable value of (78.4) is
\(\Psi_r(m)xH'(x)/H(x)\). This is a weighted value, not
the unweighted summand required by Q or C.

For r=2, write
\(P=1-pX+sX^2\) and \(D=1-\rho X+\tau X^2\).
Then explicitly
\[
 \mathcal B(X,Y)=(\rho-p)+(s-\tau)(X+Y)
                    +(p\tau-\rho s)XY.
\]
Away from the diagonal, the relation \(H(X)=H(Y)\) is the
graph of the Möbius involution
\[
 Y=-\frac{(\rho-p)+(s-\tau)X}
          {(s-\tau)+(p\tau-\rho s)X}.
\]
For r=3 the corresponding relation has bidegree at most (2,2).
No nonsingularity or genus claim about that curve is needed here.

For a quadratic with nonzero external residues g,h, one can take
\(a=(0,g-h)\) and \(c=(h,-g)\). For the cubic, use the
balanced lifts of (77.10). Thus the matrix sizes in (78.4) are
uniformly two and three. The Gaussian signs and exceptional origin
values must still be restored when passing from \(\Psi_r\) to
the canonical finite products of V or W.

In particular, dividing by \(H(x)-H(y)\) to create poles at
integer z also introduces zeros of \(\mathcal B(x,y)\) into
the denominator. Their contributions cannot be omitted without
an additional argument. Equations (78.3)--(78.6) reduce the
analytic shift problem; they do not prove the finite sums.

`hi_shintani_monodromy.py` verifies the generic Bezout identities
symbolically for r=2,3 and independently checks (78.3)--(78.4)
using double-sine evaluations at two complex arguments, for both
kernels at n=3,7,11. The largest numerical discrepancy in the
saved 50-digit run is below \(2\times10^{-49}\). The identities
above have direct proofs; the numerical run checks their
implementation and conventions. **Infinitude remains unproved.**

---

# 79. Canonical balanced lifts remove all signs from the cross-free targets

The origin jump in Section 76 does not require corrections inside
the desired cross-free sums if their integer representatives are
chosen appropriately. Such representatives always exist. Together
with the earlier collision reduction, this gives two finite
double-sine identities whose uniform proof would suffice for
existence.

## 79.1 The canonical-lift lemma

Let \(p_1,\ldots,p_r,q_1,\ldots,q_r\in\mathbb Z_n\), with
r=2 or r=3, satisfy
\[
 \sum_i p_i=\sum_j q_j,\qquad p_i\ne q_j\quad\text{for all }i,j.
\]
Here p are the zeros of the positive-index factors, so
\(a_i=-p_i\), and q are the zeros of the negative-index factors,
so \(c_j=q_j\).

**Lemma.** After a common cyclic translation of p and q, and,
only if necessary for r=3, interchanging the two lists, there
are integer lifts with
\[
 \boxed{\displaystyle
 -(n-1)\le a_i\le0,\qquad 0\le c_j\le n-1,
 \qquad \sum_i a_i+\sum_jc_j=(r-2)n.}
 \tag{79.1}
\]
These operations preserve the finite sum: translation reindexes
its summation variable, while interchange also reverses that
variable. The cross-sum product for r=3 is preserved as well.

**Proof.** Use representatives in \(\{0,\ldots,n-1\}\) and set
\[
 k(t)=\frac{\sum_j[q_j-t]_n-\sum_i[p_i-t]_n}{n},
 \qquad t\in\mathbb Z_n.
\]
These are integers in \(\{-(r-1),\ldots,r-1\}\), and
their average over t is zero. Their successive changes are
\[
 k(t+1)-k(t)=\#\{j:q_j=t\}-\#\{i:p_i=t\}.
 \tag{79.2}
\]
The two counts cannot both be nonzero by the cross-free condition.

For r=2, suppose no k(t) is zero. Then all k(t) are in
\(\{-1,1\}\), so all jumps in (79.2) are even. Each list
must therefore consist of two copies of one point, say p and q.
The balance gives \(2p=2q\pmod n\). Since n is odd this
forces p=q, a contradiction. Thus k(t)=0 occurs.

For r=3, at least one point in either list has odd multiplicity,
so (79.2) has an odd jump. Hence some k(t) is odd. Its bound
implies k(t)=1 or -1. Interchanging the lists changes its sign,
so k(t)=1 is obtainable. In either case put
\(a_i=-[p_i-t]_n\), \(c_j=[q_j-t]_n\). ∎

## 79.2 Exact cancellation of the interpolation signs

For the lifts in (79.1) and every \(m=0,\ldots,n-1\), all
arguments \(m+a_i\) and \(c_j-m\) lie in
\([-(n-1),n-1]\). In this interval the integer interpolation
f from Section 76 equals the canonical phase \(W_{[u]_n}\),
including at u=0. No argument is a positive multiple of n.
The same holds for every nonzero cross argument \(a_i+c_j\).

Write \(F(u)=S(B+u;A,B)\) as in Section 78 and put
\[
 E=\frac12\sum_i\bigl(a_i^2+c_i^2+n(a_i+c_i)\bigr)
 \in\mathbb Z.
\]
Since \(V_{[u]_n}=e^{\pi iu(u+n)/2}F(u)\) on this
integer interval, direct expansion gives
\[
 \prod_iV_{m+a_i}\prod_jV_{c_j-m}=(-1)^E\Psi_r(m).
 \tag{79.3}
\]
Indeed, the remaining exponent is
\(rm^2+(2\sum_i a_i-(r-2)n)m\), an even integer for every
integer m because n is odd. Thus the sign is independent of m.

For r=3 define
\[
 J=\frac12\sum_{i,j}(a_i+c_j)(a_i+c_j+n).
\]
If \(s=\sum_i a_i\), \(t=\sum_jc_j\), so s+t=n, then
\[
 J-E=\sum_i(a_i^2+c_i^2)+st+n^2\equiv0\pmod2.
\]
Here the sum of the squares is odd, st is even, and \(n^2\)
is odd. Consequently
\[
 \prod_{i,j}V_{a_i+c_j}=(-1)^E\prod_{i,j}F(a_i+c_j).
 \tag{79.4}
\]
The two signs cancel exactly in (77.10).

## 79.3 Two explicit unweighted identities suffice

For each odd n, with \(A=d+1\), \(B=1+d^{-1}\), the analytic
existence problem is now reduced to the following statements for
integer lifts satisfying (79.1) and \(a_i+c_j\ne0\):
\[
 \boxed{\displaystyle
 \sum_{m=0}^{n-1}\prod_{i=1}^2F(m+a_i)F(c_i-m)=0
 \quad (\textstyle\sum_i(a_i+c_i)=0),}
 \tag{79.5}
\]
and
\[
 \boxed{\displaystyle
 \frac1{\sqrt{AB}}\sum_{m=0}^{n-1}
       \prod_{i=1}^3F(m+a_i)F(c_i-m)
 =\prod_{i,j=1}^3F(a_i+c_j)
 \quad (\textstyle\sum_i(a_i+c_i)=n).}
 \tag{79.6}
\]
**Equations (79.5) and (79.6) are conjectural uniform identities.**
Their equivalence to the required quadratic and cross-free cubic
identities is proved by the lemma and (79.3)--(79.4). The inverse
norms and origin normalization are already proved in Section 76.
Once (79.5) holds, Section 34.2--34.3 supplies every collision
and boundary cubic by algebraic identities. Hence proving both
displayed sums for unbounded odd n would imply the requested
categorification through Section 52, without first assuming Stark
algebraicity. Conversely, a complete solution by this analytic
candidate must satisfy these two sums.

This also explains exactly what remains in the continuous beta
route. The canonical choice removes the Gaussian signs and the
origin corrections from the finite target. The extra trigonometric
factors and the continuous contour in (77.9) still need to be
converted into (79.6); the lift lemma does not perform that conversion.
The rational shift formulas of Section 78 apply to both targets.

`hi_shintani_canonical.py` exhaustively checks the lift and sign
identities for every balanced cross-free pair of multisets at
n=3,5,7,9,11. At n=11 this covers 330 quadratic pairs and 3520
cubic pairs; 198 cubic pairs use the reversal allowed in the lemma.
Independent numerical double-sine evaluations check (79.5)--(79.6)
on selected representatives at n=3,7,11, with normalized residuals
below \(1.6\times10^{-40}\) in the saved run. These finite
checks support the formulas; they do not prove the conjectural
identities for unbounded n. **Infinitude remains unproved.**

## 79.4 The exact scope of a period-shift recurrence

Reflection gives the useful quotient form
\[
 F(z)F(n-z)=1,\qquad
 \Psi_r(z)=\prod_i\frac{F(z-p_i)}{F(z+n-q_i)},
 \qquad p_i=-a_i,\ q_i=c_i.
\]
For the canonical lifts, this kernel has no poles on the closed
vertical strip \(0\le\operatorname{Re}z\le n\). Indeed,
the zeros and poles of F are respectively
\[
 -B-jA-kB,\qquad A+jA+kB\qquad(j,k\ge0).
\]
The positive-argument factors \(F(z-p_i)\) first have poles
at \(z=p_i+A>n\), while the negative-argument factors
\(F(q_i-z)\) have all their poles at
\(z=q_i-A-jA-kB<0\). All these poles are real. Thus the
finite-sum contour problem can be considered in a strip where
the summation kernel itself is holomorphic.

However, a finite sequence of ordinary period shifts cannot
connect distinct integer residue classes:
\[
 \boxed{(\mathbb ZA+\mathbb ZB)\cap\mathbb Z=n\mathbb Z.}
\]
To prove this, write \(jA+kB=jn+(j+k)B\) and use the
irrationality of B. Adding reflection only changes an integer
argument to one of the form \(\pm u+jn\). Therefore direct
use of shifts and reflection gives the norm and translate laws
already proved, but does not by itself provide a recurrence
between arbitrary labels in the finite target. An additive
summation or integral identity is still needed to bridge that
step. This statement concerns finite compositions of these
operations; it does not exclude limits or other identities of S.

---

# 80. A convergent contour formula for the unweighted sums

The growth obstruction in Section 77 does not prevent an Abel--Plana
representation. Its upper and lower half-plane kernels decay at rate
\(2\pi\), leaving a real-interval integral and endpoint terms.
All of these terms must be retained. The resulting formula is exact
for the canonical kernels in Section 79, although its proposed
evaluation remains unproved.

## 80.1 The two separate period shifts

Use the notation \(P,D,H,q,x,y\) of Section 78. In addition to
the n-shift, the same rational function gives
\[
 \boxed{\displaystyle
 \frac{\Psi_r(z+B)}{\Psi_r(z)}=\frac{q}{H(qx)},\qquad
 \frac{\Psi_r(z+A)}{\Psi_r(z)}=\frac{q}{H(y)}.}
 \tag{80.1}
\]
These are meromorphic identities, including at removable points.
For example, the B-shift of each double sine gives
\[
 \frac{\Psi_r(z+B)}{\Psi_r(z)}
 =\prod_i\frac{\sin(\pi(c_i-z)/A)}
                   {\sin(\pi(B+z+a_i)/A)}.
\]
Converting the sines to exponentials gives \(D(qx)/P(qx)\)
times the constant
\[
 (-1)^r\exp\!\left(\frac{\pi i}{A}
           \left(\sum_i(a_i+c_i)+rB\right)\right)=q.
\]
The A-shift then follows by composing this with the n-shift,
using \(A=n+B\) and \(x(z+n)=q^{-1}x(z)\).
Thus the two first-order difference equations have rational
coefficients of degree r. No convergent infinite q-product is
assumed: here \(|q|=1\).

## 80.2 Exact Abel--Plana representation and its endpoint limits

Fix canonical lifts satisfying (79.1), and write \(\Psi=\Psi_r\).
Then
\[
 \boxed{\displaystyle
 \sum_{m=0}^{n-1}\Psi(m)
 =\int_0^n\Psi(u)\,du+\frac{\Psi(0)-\Psi(n)}2
  +2\int_0^\infty
       \frac{\operatorname{Im}(\Psi(n+it)-\Psi(it))}
            {e^{2\pi t}-1}\,dt.}
 \tag{80.2}
\]
The imaginary part is taken **inside** the integral. Its integrand,
including the factor 2, extends continuously to zero with value
\[
 \frac{\Psi'(n)-\Psi'(0)}{\pi}.
 \tag{80.3}
\]
The numerator before taking its imaginary part need not vanish at
zero, so replacing this by the imaginary part of an ordinary
convergent complex integral is not justified in general.

**Proof.** Section 79.4 gives holomorphy on a neighborhood of the
closed strip \(0\le\operatorname{Re}z\le n\). The kernel is real
on its real interval. The balanced double-sine asymptotic gives,
uniformly on this strip,
\[
 |\Psi(u+it)|=O(e^{2\pi\kappa|t|}),\qquad
 \kappa=\frac{n}{AB}=\frac{d-1}{d+1}<1.
\]
Apply the finite-strip Abel--Plana contour formula: use the
exponentially decaying cotangent correction in each half-plane,
with half residues at the two endpoints. The horizontal edges
at height tending to infinity vanish because \(\kappa<1\).
Subtracting the last endpoint from the inclusive sum yields
(80.2). These are the standard analytic and growth hypotheses
for Abel--Plana; see [DLMF, Section 2.10(i)](https://dlmf.nist.gov/2.10#i).
Taylor expansion at the real endpoints proves (80.3). At infinity
the vertical integrand is
\[
 O(e^{-2\pi(1-\kappa)t})=O(e^{-4\pi t/A}),
\]
so its integral converges absolutely. The implied constant can
depend on n and on the lifts. ∎

The rational monodromy makes the correction in (80.2) explicit.
For \(t>0\), put \(X=e^{-2\pi t/A}\), \(Y=e^{2\pi t/B}\).
Equation (78.4) gives
\[
 \frac{2\operatorname{Im}(\Psi(n+it)-\Psi(it))}{e^{2\pi t}-1}
 =-2e^{-2\pi t}\operatorname{Im}\!\left(
    \Psi(it)\frac{Y\mathcal B(X,Y)}{D(X)P(Y)}\right).
 \tag{80.4}
\]
The denominator is nonzero for every t>0, because its roots have
modulus one whereas \(0<X<1<Y\). The Bezout polynomial occurs
in the numerator. Formula (80.3) supplies the endpoint value.

## 80.3 The remaining evaluation is substantive

Let \(\mathcal L_n(\Psi)\) denote the complete right side of
(80.2). The two uniform targets are now equivalently
\[
 \mathcal L_n(\Psi_2)=0,\qquad
 \mathcal L_n(\Psi_3)=\sqrt{AB}\prod_{i,j=1}^3F(a_i+c_j).
 \tag{80.5}
\]
The formula for \(\mathcal L_n\) is proved; the evaluations in
(80.5) are still conjectural. In particular, the real-interval and
endpoint terms cannot be discarded or replaced by the beta product
in (77.9) without proving an additional identity.

`hi_shintani_abel_plana.py` checks (80.1) directly with double sines
at complex arguments, and independently compares (80.2) with its
finite samples at n=3. It uses the canonical parameters
\(a=(0,-2),c=(1,1)\) for r=2 and
\(a=(0,0,0),c=(1,1,1)\) for r=3. With 64 Gauss--Legendre nodes
and vertical cutoff 12, the two discrepancies are below
\(7.7\times10^{-16}\); the separate period checks are below
\(7.0\times10^{-30}\). These quadrature checks are not interval
certificates. The proof of (80.2) uses analyticity and growth,
independently of the conjectured target values. **Infinitude remains
unproved.**

## 80.4 An exact rational period primitive for every quadratic kernel

For r=2, the rational shift equation has an explicit primitive.
Use P,D,q,x,y from Sections 78 and 80.1, and define
\[
 \kappa=[X]\bigl(D(qX)-P(X)\bigr)
        =\sum_{i=1}^2\alpha_i-q\sum_{j=1}^2\beta_j^{-1}.
\]
The constant terms of D(qX) and P(X) agree. Their quadratic
coefficients agree by (78.2). Consequently
\[
 D(qX)-P(X)=\kappa X.
 \tag{80.6}
\]
The coefficient is nonzero in the cross-free situation. More
explicitly, using \(a_1+a_2+c_1+c_2=0\),
\[
 \kappa=-4e^{\pi i(a_1+a_2)/A}
   \sin\frac{\pi(a_1+c_1)}A\,
   \sin\frac{\pi(a_1+c_2)}A\ne0.
 \tag{80.7}
\]
Here A is irrational and each displayed cross argument is a nonzero
integer. The factorization follows by subtracting the two cosine
sums after extracting \(e^{\pi i(a_1+a_2)/A}\).

**Proposition.** Put
\[
 \mathcal G(z)=\Psi_2(z)\frac{P(x)}{\kappa x},\qquad
 \mathcal V(z)=-\frac{D(qy)}{\kappa y\Psi_2(z)}.
\]
Then, as meromorphic identities,
\[
 \boxed{\mathcal G(z+B)-\mathcal G(z)=\Psi_2(z),\qquad
 \mathcal V(z+A)-\mathcal V(z)=\Psi_2(z)^{-1}.}
 \tag{80.8}
\]

**Proof.** Under the B shift, x changes to qx. Equation (80.1)
therefore gives
\[
 \mathcal G(z+B)=\Psi_2(z)\frac{D(qx)}{\kappa x}.
\]
Subtract \(\mathcal G(z)\) and apply (80.6). Under the A shift,
y changes to \(q^{-1}y\), and the reciprocal kernel is multiplied
by \(P(y)/(qD(y))\). Thus
\[
 \mathcal V(z+A)=-\frac{P(y)}{\kappa y\Psi_2(z)}.
\]
The same polynomial identity proves the second assertion. ∎

The first primitive can also be written without exponentials:
\[
 \mathcal G(z)=\Psi_2(z)
 \frac{\sin(\pi(z+a_1)/A)\sin(\pi(z+a_2)/A)}
      {\sin(\pi(a_1+c_1)/A)\sin(\pi(a_1+c_2)/A)}.
 \tag{80.9}
\]
For canonical lifts it also has the product form
\[
 \mathcal G(z)=
 \frac{\prod_{i=1}^2F(z+a_i-B)\prod_{j=1}^2F(c_j-z)}
      {4\sin(\pi(a_1+c_1)/A)\sin(\pi(a_1+c_2)/A)}.
\]
Its first possible positive-argument poles are at
\(z=A+B-a_i>A\), while all negative-argument poles are to
the left of zero. Thus it is holomorphic on a neighborhood of
\(0\le\operatorname{Re}z\le A\). On this strip its growth is
\(O(e^{2\pi|\operatorname{Im}z|/B})\): multiplying the balanced
kernel by P(x)/x adds \(2\pi/A\) to its growth exponent, and
\(n/(AB)+1/A=1/B<1\). The strict bound permits finite-strip
Abel--Plana manipulations with this primitive as well, with the
boundary terms retained.

This gives an unweighted period difference, stronger than the
weighted divided difference in (78.4). It does **not** yet give the
unweighted finite identity (79.5): its shift is B, not the unit
increment in the summation variable. Direct summation gives only
\[
 \sum_{m=0}^{n-1}\Psi_2(m)
  =\sum_{m=0}^{n-1}\mathcal G(m+B)
   -\sum_{m=0}^{n-1}\mathcal G(m).
\]
In particular, one cannot replace the first sum by the second by
cyclic reindexing. At a regular nonexceptional integer m, with
\(s=e^{2\pi im/A}\), the n-shift of the primitive is
\[
 \frac{\mathcal G(m+n)}{\mathcal G(m)}
       =q\frac{P(q^{-1}s)}{P(s)},
\]
which is not identically one. A contour or other analytic argument
must still establish the required equality of these two sample sums.

## 80.5 The cubic kernel has no rational B-shift primitive

There is a sharp limit to extending (80.8). Retain cross-free
integer lifts and the balance in Section 78, for r=2 or r=3.
Consider a rational function g for which
\[
 \Psi_r(z+B)g(qx)-\Psi_r(z)g(x)=\Psi_r(z).
 \tag{80.10}
\]
No degree bound is imposed on g.

**Theorem.** For r=2 the unique rational solution is
\(g(X)=P(X)/(\kappa X)\). For r=3 there is no rational solution.

**Proof.** Write \(g(X)=P(X)h(X)\). Dividing (80.10) by the
nonzero meromorphic kernel and using (80.1) yields
\[
 qD(qX)h(qX)-P(X)h(X)=1.
 \tag{80.11}
\]
The number q is not a root of unity. No root of P is in the
q-orbit of a root of D: such an intersection would imply
\(\alpha_i\beta_j=q^k\) for an integer k. In the present
coordinates this is equivalent to
\[
 a_i+c_j=(1-k)n,
\]
contradicting cross-freeness. To see the equivalence, compare the
rational and irrational parts of
\(a_i+c_j-n-kB=jA=j(n+B)\).

If h had a pole in \(\mathbb C^\times\), choose the first and
last poles in its finite set on that q-orbit. At the predecessor
of the first pole, (80.11) forces D to vanish at the first pole.
At the last pole it forces P to vanish there. These two roots
would be on the same q-orbit, a contradiction. This argument also
handles repeated roots and higher-order poles. Thus h is a
Laurent polynomial.

Let ell and u be its least and greatest exponents. On a monomial
\(X^k\), the least-degree coefficient in the operator on the
left of (80.11) is \(q^{k+1}-1\). Its greatest-degree coefficient
is
\[
 D_r\bigl(q^{k+r+1}-q^2\bigr),
\]
where \(D_r\ne0\) and \(P_r=q^2D_r\) by (78.2).
If ell were nonnegative, cancellation of the positive highest
degree would force \(u=1-r<0\), a contradiction. Therefore
ell is negative, and cancellation of its coefficient forces
ell=-1. Now \(u\ge-1\), so the highest degree is positive and
its cancellation forces \(u=1-r\). These two requirements are
compatible only for r=2, when \(h=c/X\). Substitution into
(80.11) gives \(c\kappa=1\), proving both existence and uniqueness
in that case and impossibility for r=3. ∎

This obstruction concerns a single rational multiplier for the B
shift. It does not rule out integral identities, multiple terms
with shifted parameters, or other proofs of the cubic finite sum.
It does rule out obtaining the cubic target by increasing the degree
of this particular rational telescoping certificate.

`hi_shintani_telescoper.py` checks the generic quadratic polynomial
identities and the Laurent endpoint coefficients symbolically. It
also solves independent exact rational examples with Laurent
degrees -8 through 8, obtaining the predicted unique quadratic
primitive and no cubic primitive. Direct double-sine evaluations
at two complex arguments for each of n=3,7,11 check both identities
in (80.8) and the trigonometric normalization (80.9), with relative
errors below \(2.7\times10^{-44}\) in the saved run. The uniform
proofs above do not use those numerical checks or assume Q or C.
**The finite summation identities and infinitude remain unproved.**

## 80.6 One convergent vertical contour, with its boundary pair retained

For the quadratic kernel, the new primitive permits a different
contour representation. It has no real-interval integral. This is
a consequence of using a difference of cotangents with the primitive,
not of discarding terms from (80.2).

Retain canonical quadratic lifts, write \(\mathcal G\) as in
(80.9), and put
\[
 \sigma=-\frac12,\qquad
 K_B(z)=\pi\cot(\pi z)-\pi\cot(\pi(z-B))
       =-\frac{\pi\sin(\pi B)}{\sin(\pi z)\sin(\pi(z-B))}.
 \tag{80.12}
\]
The value of B satisfies \(1<B<3/2\) at every odd \(n\ge3\).

**Proposition.** The following integral converges absolutely and
gives the finite sum exactly:
\[
 \boxed{\begin{aligned}
 \sum_{m=0}^{n-1}\Psi_2(m)
  ={}&\mathcal G(A-1)-\mathcal G(B-1)\\
    &-\frac1\pi\int_0^\infty
       \operatorname{Re}\!\left[
        K_B(\sigma+it)
        \bigl(\mathcal G(\sigma+n+it)-\mathcal G(\sigma+it)\bigr)
                         \right]dt.
 \end{aligned}}
 \tag{80.13}
\]

**Proof.** The primitive is holomorphic on a neighborhood of the
closed strip \(\sigma\le\operatorname{Re}z\le\sigma+n\).
Its positive-argument poles start beyond A, and its negative-argument
poles lie at or to the left of
\(\max c_j-A\le-1-B<-2\). Its growth on this strip is
\(O(e^{2\pi|\operatorname{Im}z|/B})\), while K_B decays as
\(O(e^{-2\pi|\operatorname{Im}z|})\). Thus the horizontal
edges of a rectangular contour tend to zero.

Inside this strip the poles of K_B are exactly
\[
 0,1,\ldots,n-1\quad\text{with residue }+1,
\]
and
\[
 B-1,B,\ldots,B+n-2\quad\text{with residue }-1.
\]
Any cancellation by a zero of the primitive is automatically
accounted for by its value in the residue sum. The sum of the
residues of \(K_B\mathcal G\) is therefore
\[
 \begin{aligned}
 &\sum_{m=0}^{n-1}\mathcal G(m)
    -\sum_{m=-1}^{n-2}\mathcal G(m+B)\\
 &\hspace{1cm}=
 \mathcal G(A-1)-\mathcal G(B-1)-\sum_{m=0}^{n-1}\Psi_2(m),
 \end{aligned}
\]
where the last equality uses (80.8). This is the source of the
boundary pair; the two shifted sample windows do not coincide.

Since n is an integer, \(K_B(z+n)=K_B(z)\). Integrating up
the right edge and down the left edge now gives the residue sum as
\[
 \frac1{2\pi i}\int_{\sigma-i\infty}^{\sigma+i\infty}
 K_B(z)\bigl(\mathcal G(z+n)-\mathcal G(z)\bigr)\,dz.
\]
Conjugation across the real axis converts this into the positive
half-line integral in (80.13). Its tail is
\(O(e^{-2\pi(1-1/B)t})=O(e^{-2\pi t/A})\); it is regular
at t=0 because neither vertical edge contains a cotangent pole. ∎

Thus the exact remaining quadratic evaluation is
\[
 \frac1\pi\int_0^\infty\operatorname{Re}\!\left[
 K_B(\sigma+it)
 \bigl(\mathcal G(\sigma+n+it)-\mathcal G(\sigma+it)\bigr)
 \right]dt
   =\mathcal G(A-1)-\mathcal G(B-1).
 \tag{80.14}
\]
**Equation (80.14) remains conjectural uniformly.** The contour
representation is proved, but its two sides have not been evaluated
as equal for unbounded n. The boundary pair is generally nonzero.

There is also a useful check independent of that conjectured equality.
The same representation holds with any \(1<B<3/2\), \(A=n+B\),
and \(F(z)=S(B+z;A,B)\), without assuming \(AB=A+B\).
The first primitive identity follows directly from the period-B
shift and the balanced two-sine addition formula; the contour proof
then uses only the displayed pole locations and B>1. In that
generality the decay rate is \(2\pi(1-1/B)\).

`hi_shintani_quadratic_contour.py` verifies both the primitive and
its n-shift directly before numerical quadrature. At n=3 with
\(a=(0,-2)\), \(c=(1,1)\), it obtains:

| Parameters | Finite sum | Boundary pair | Vertical integral |
|---|---:|---:|---:|
| RM value \(B=1+1/d\) | approximately 0 | -0.981606085906848 | -0.981606085906852 |
| \(B=5/4,\ A=17/4\) | -0.538419808274932 | -1.194238407531538 | -0.655818599256570 |

With 128 Gauss--Legendre nodes and cutoff 24, the discrepancies in
(80.13) are below \(3.7\times10^{-14}\). These are numerical
checks, not interval certificates. The second row confirms a
nonzero finite sum while verifying the same contour bookkeeping;
it does not satisfy the full RM normalization. No uniform Q, C,
or infinitude conclusion follows from these checks.

## 80.7 Elementary series and a uniform bound for real-axis extrapolation

At the real-multiplication parameters both period ratios have the
same exponential:
\[
 e^{2\pi iB/A}=e^{2\pi iA/B}=q=e^{2\pi i/d}.
\]
This gives a useful construction of the analytic candidate with
explicit error bounds. The distinction between the upper half-plane
series and its real boundary values is essential.

Put \(\theta=1/d\), \(\Delta=\sqrt{n^2+4}=d+1/d\).
For k positive, let m be a nearest integer to \(k\theta\).
The algebraic norm identity
\[
 (k\theta-m)(-kd-m)=m^2+nkm-k^2\in\mathbb Z\setminus\{0\}
\]
implies
\[
 \boxed{\|k\theta\|_{\mathbb R/\mathbb Z}
       \ge\frac1{k\Delta+1/2},\qquad
       |q^k-1|\ge\frac4{k\Delta+1/2}.}
 \tag{80.15}
\]
Here \(|-kd-m|\le k\Delta+1/2\), and
\(2\sin(\pi u)\ge4u\) for \(0\le u\le1/2\).
In particular,
\[
 \frac1{k|q^k-1|}\le M_n:=\frac{\Delta+1/2}{4}.
\]
No unquantified Diophantine estimate is needed.

Define the second multiple Bernoulli polynomial by
\[
 \mathcal B_{22}(u)=\frac{u^2-(A+B)u}{AB}
                   +\frac{A^2+3AB+B^2}{6AB}.
\]
For \(\operatorname{Im}z>0\), the double sine in the convention
of these notes satisfies
\[
 \boxed{F(z)=\exp\!\left(
   \frac{\pi i}{2}\mathcal B_{22}(B+z)
   +\sum_{k\ge1}
     \frac{q^ke^{2\pi ikz/A}+e^{2\pi ikz/B}}
          {k(q^k-1)}\right).}
 \tag{80.16}
\]
The series converges absolutely and locally uniformly in the upper
half-plane by (80.15). Its normalization follows by expanding the
two q-Pochhammer logarithms in the double-sine formula of
[Kopp, Theorem 4.23](https://gskopp.com/wp-content/uploads/2025/05/sfcocycle_kopp.pdf).
That formula uses the same inverse-sine period shifts as these notes.
The expansion can be continued to the present positive real period
ratio by approaching d vertically. For the exponential of the period
ratio, radial separation controls indices with \(k\operatorname{Im}\tau\)
bounded below, and (80.15) controls the remaining indices. For the
reciprocal period ratio its real part differs from \(1/d\) by
\(O((\operatorname{Im}\tau)^2)\); splitting the indices in the same
way again gives a common polynomial bound for the inverse denominators.
The exponential numerators then give a summable majorant. Thus this
use of the boundary value does not assume convergence of an infinite
q-product on the unit circle.

For an integer w and h>0 put
\[
 c_k(w)=\frac{q^ke^{2\pi ikw/A}}{k(q^k-1)},\qquad
 L_w(h)=\log|F(w+ih)|.
\]
Using \(1/A+1/B=1\), the other series coefficient at an integer
w is \(-\overline{c_k(w)}\). Taking real parts in (80.16) gives
\[
 \boxed{L_w(h)=\frac{\pi(n/2-w)}{AB}h
  +\sum_{k\ge1}\operatorname{Re}c_k(w)
       \left(e^{-2\pi kh/A}-e^{-2\pi kh/B}\right).}
 \tag{80.17}
\]
If the sum is truncated after K terms, its absolute error is at most
\[
 \boxed{T_K(h)=M_n\left(
 \frac{e^{-2\pi(K+1)h/A}}{1-e^{-2\pi h/A}}
 +\frac{e^{-2\pi(K+1)h/B}}{1-e^{-2\pi h/B}}\right).}
 \tag{80.18}
\]
All quantities in this bound are explicit. At h=0 every finite
partial sum in (80.17) is zero, while the boundary logarithm
generally is not zero. Thus setting h to zero term by term loses
the desired amplitude. The following estimate controls the actual
boundary limit.

**Uniform real-axis approximation theorem.** Let n be odd and at
least 3, \(1\le w\le(n-1)/2\), and p≥2. Set
\[
 h_j=2^{-j-2},\qquad
 \lambda_j=\prod_{\substack{0\le\ell<p\\\ell\ne j}}
                \frac{h_\ell^2}{h_\ell^2-h_j^2},\qquad
 \Lambda_p=\prod_{k=1}^{p-1}\frac{1+4^{-k}}{1-4^{-k}}.
\]
Then
\[
 \boxed{\left|\log F(w)-\sum_{j=0}^{p-1}\lambda_j L_w(h_j)\right|
 \le E_p:=\frac5{2p}\,2^{-p^2-5p}\Lambda_p
 <\frac{15}{2p}\,2^{-p^2-5p}.}
 \tag{80.19}
\]
In particular, the error bound is independent of n and w in this
range. The values F(w) are positive here. If each L is evaluated
by its K-term series, add
\(\sum_j|\lambda_j|T_K(h_j)\) to the right side of (80.19),
in addition to the rounding errors of that finite computation.

**Proof.** The zeros of F are \(-B-jA-kB\) and its poles are
\(A+jA+kB\), with j,k nonnegative. The canonical w under
consideration is more than 2 away from every zero and pole.
For s>2 and u>0, the decreasing lattice sum obeys
\[
 \sum_{j,k\ge0}(u+jA+kB)^{-s}
 \le u^{-s}
 +\frac{(A^{-1}+B^{-1})u^{1-s}}{s-1}
 +\frac{u^{2-s}}{AB(s-1)(s-2)}.
\]
Split off the origin and two axes, then bound the remaining sums
by their one- and two-dimensional integrals. Apply this to
\(u=B+w\) and \(u=A-w\), using u≥2,
\(A^{-1}+B^{-1}=1\), and \(1/(AB)<1\). For every even s≥4,
the sum over distances to all zeros and poles is bounded by
\[
 M_s(w)\le
 2\,2^{-s}\left(1+\frac2{s-1}
                       +\frac4{(s-1)(s-2)}\right)
 <5\,2^{-s}.
 \tag{80.20}
\]
The genus-two product for the double sine implies, on the vertical
line through w,
\[
 |L_w^{(2p)}(h)|\le(2p-1)!M_{2p}(w)
                 \le(2p-1)!5\,2^{-2p}.
\]
Indeed the polynomial terms in that product disappear after four
derivatives, and a vertical displacement cannot decrease the
distance to a real zero or pole. Also L_w is even in h, by real
conjugation. Taylor's theorem therefore gives an error at most
\(5\,2^{-2p}h^{2p}/(2p)\) after its first p even terms.

The interpolation weights satisfy
\[
 \sum_j\lambda_j=1,\qquad
 \sum_j\lambda_j h_j^{2k}=0\quad(1\le k<p),
\]
and their remaining absolute moment is
\[
 \sum_j|\lambda_j|h_j^{2p}
   =2^{-p^2-3p}\Lambda_p.
\]
For example, write the nodes as \(4^{-j}\) after removing the
common factor \(1/16\). The finite q-binomial product gives
\(\sum_j|\lambda_j|4^{-jp}
 =4^{-p(p-1)/2}\Lambda_p\).
These formulas also follow directly by expanding the geometric
products in the displayed weights. Combining the Taylor remainders
proves the first inequality in (80.19).
Finally,
\[
 \log\Lambda_p
 \le\sum_{k\ge1}\frac{2\,4^{-k}}{1-4^{-k}}
 \le\frac89<\log3,
\]
which proves the simpler upper bound. ∎

The inverse-pair formulas now recover every canonical sample from
this positive half:
\[
 F(0)=\sqrt d,\qquad F(n-w)=F(w)^{-1},\qquad
 F(-w)=(-1)^{w+1}F(w)^{-1}\quad(1\le w<n).
\]
Together with Section 76 this gives every W_a with a controlled
relative error. For fixed p the series lengths needed for a common
tail tolerance τ can be bounded by
\[
 K+1\ge\frac{A}{2\pi h_{p-1}}
 \log\!\left(
 \frac{2M_n}{\tau(1-e^{-2\pi h_{p-1}/A})}\right).
\]
In particular, taking τ comparable to \(2^{-p^2-5p}\) requires
\(K=O(n2^p(p^2+\log n))\). This is an effective approximation
theorem for all odd orders; it does not assume Q, C, or Stark
algebraicity.

There is also a direct kernel version. With the balanced integer
lists a,c used above, put
\[
 \alpha_i=e^{2\pi ia_i/A},\quad \gamma_j=e^{2\pi ic_j/A},\quad
 x=e^{2\pi iz/A},\quad v=e^{2\pi iz/B},\quad \kappa=\frac n{AB},
\]
\[
 C_0=\exp\!\left(\frac{\pi i}{2AB}
   \left[\sum_i a_i^2-\sum_j c_j^2-n\Bigl(\sum_i a_i-\sum_j c_j\Bigr)\right]\right),
 \qquad
 C_k=\frac{q^k\sum_i\alpha_i^k-\sum_j\gamma_j^{-k}}{k(q^k-1)}.
\]
For both r=2 and r=3,
\[
 \boxed{\Psi_r(z)=C_0e^{-2\pi i\kappa z}
       \exp\!\left(\sum_{k\ge1}(C_kx^k-\overline{C_k}v^k)\right),
       \qquad\operatorname{Im}z>0.}
 \tag{80.21}
\]
This follows from (80.16) and its lower-half-plane conjugate.
The logarithmic tail after K terms is bounded by (80.18) with
M_n replaced by 2rM_n. It supplies an elementary convergent
representation of the kernels appearing in the contour problem.

`hi_shintani_boundary_series.c` implements (80.17)--(80.19) with
256-bit FLINT/Arb balls and p=8 by default. Both parameters can now
be overridden at compilation, as in Section 90. Its default analytic logarithmic remainder
is \(E_8<3.035\times10^{-32}\). It includes the separate series
tails and every arithmetic rounding error, exponentiates the
resulting logarithm balls, and reconstructs the complete ghost
phase data and A matrix. Streaming the coefficients keeps storage
small. Complex powers are re-evaluated every 32 steps to control
interval wrapping; a long unchecked recurrence would inflate those
balls exponentially.

The saved run evaluates every Q and C residual at three orders:

| n | Q residuals | Bound on every Q magnitude | C residuals | Bound on every C magnitude |
|---:|---:|---:|---:|---:|
| 3 | 9 | \(8.06\times10^{-32}\) | 81 | \(3.08\times10^{-31}\) |
| 7 | 49 | \(1.61\times10^{-30}\) | 2401 | \(9.32\times10^{-30}\) |
| 11 | 121 | \(1.56\times10^{-29}\) | 14641 | \(3.15\times10^{-28}\) |

Every residual ball contains zero. These are rigorous bounds on
the residuals of the analytic candidate, conditional only on the
proved formulas above and correct execution of the interval code;
containing zero does not prove exact vanishing. Peak resident memory
was 13.2 MiB.

`hi_shintani_boundary_series.py` independently verifies the rational
weights and remainder identities, the quadratic norm formula, and
the complex kernel expansion using the integral definition of the
double sine. All nine independently evaluated positive real samples
lie in the printed Arb enclosures. Those integral comparisons are
numerical regressions; the Arb enclosures themselves include the
analytic remainder bounds.

This resolves how to approximate the real samples with uniform,
explicit error control. Uniform cancellation in their finite Q/C
sums would suffice for infinitude; Section 90 gives a weaker
sufficient small-error inequality. No bound meeting that inequality
as n grows has been proved here. Section 89 removes the unitarity
restriction which prevented applying Section 87 to ghost trials.
**Infinitude remains unproved.**

---

# 81. An explicit cyclic pentagon operator at every odd order

The order-five operator sought in Section 60 can be supplied uniformly
as an abstract conjugation operator. A finite cyclic quantum-dilogarithm
matrix gives it over characteristic two. What remains is to connect
this explicit operator to the sparse HI transfer matrix by constructing
the phase data. The operator alone is not a fusion category.

## 81.1 The central fixed point and a finite product matrix

Work in an algebraically closed field of characteristic two. Fix odd
\(n\ge3\), a primitive \(3n\)-th root s, and put
\[
 q=s^3,\qquad \rho=s^n,\qquad \rho^2+\rho+1=0.
\]
Here \(\rho\) denotes a **central fixed point**, not the HI dimension
\(\delta\). Their matching choice in the checks below is
\(\rho=\delta^{-1}\). On a basis indexed by \(j\in\mathbb Z_n\), set
\[
 Xe_j=s q^{2j}e_j,\qquad Ye_j=s e_{j+1}.
\]
Then \(XY=q^2YX\) and \(X^n=Y^n=\rho I\).
Define the cyclic sequence
\[
 b_0=1,\qquad
 b_{j+1}=s^{-2}(1+qs q^{2j})b_j,
 \qquad B_{ij}=q^{-2ij}b_j.
 \tag{81.1}
\]
All factors are nonzero, and the recurrence closes:
\[
 \frac{b_n}{b_0}
 =s^{-2n}\prod_{j=0}^{n-1}(1+qs q^{2j})
 =\rho^{-2}(1+\rho)=1.
\]
The Fourier matrix \((q^{-2ij})\) is invertible because n is odd
and \(q^2\) is primitive. Hence B is invertible.

**Uniform theorem.** The matrix (81.1) satisfies
\[
 BXB^{-1}=Y,\qquad
 BYB^{-1}=X^{-1}(I+qY),\qquad B^5\in k^\times I.
 \tag{81.2}
\]
Consequently \(\operatorname{Ad}(B)^5=I\) at every odd order.

**Proof.** The two intertwining equations follow entrywise from
(81.1). For the second, use \(YB=BX\): its \((i,j)\) entry
reduces precisely to the recurrence for \(b_{j+1}\).
The quantum recurrence \(X_{j+2}=X_j^{-1}(I+qX_{j+1})\), starting
at X,Y, has the five consecutive values
\[
 X,\quad Y,\quad X^{-1}(I+qY),\quad
 Y^{-1}+X^{-1}+q^{-1}X^{-1}Y^{-1},\quad (I+qX)Y^{-1},
\]
and then returns to X,Y. This follows directly from \(XY=q^2YX\).
Conjugation by B therefore has fifth power fixing both X and Y.
These two matrices generate the full matrix algebra: X has distinct
eigenvalues and Y cycles its eigenvectors. Their common commutant
consists of scalars, proving (81.2). ∎

This is a finite characteristic-two realization of the standard
quantum \(A_2\) pentagon mechanism; compare
[Goncharov's quantum-dilogarithm intertwining construction](https://arxiv.org/html/0706.4054v2#S2).
The proof above is algebraic and does not require analytic continuation
of an infinite product. One possible coefficient field is
\(\mathbb F_{4^r}\), where \(r=\operatorname{ord}_{3n}(4)\).
For \(n=3^k\), this is \(r=n\).

## 81.2 The complete Jordan correction at an HI point

There is also a faster exact way to compare (81.2) with a saved HI
point. Assume full Q and C in characteristic two, and put
\(t=\delta^{-1}\). Let \(M(\lambda)\) denote the multiplicity of
a fifth root \(\lambda\) in the corrected operator \(\mathcal P\).
Then
\[
 \boxed{\displaystyle
 M(1)=1+\dim\ker(R-I),\qquad
 M(\lambda)=\dim\ker(R-\lambda I)
       +\mathbf1_{\lambda^2+t\lambda+1=0}\quad(\lambda\ne1).}
 \tag{81.3}
\]
Thus five ranks of the sparse R determine the spectrum; no dense
sixth power is needed.

**Proof.** On \(\operatorname{im}E\), R has the single eigenvalue
t and \(\mathcal P\) has eigenvalue 1. On \(\ker E\), Section 60
gives \(R^5=I+N\), with \(N^2=0\). Every Jordan block there has
size at most two and a fifth-root eigenvalue, because the derivative
of \(X^5-1\) is nonzero at all its roots.

Moreover \(\operatorname{im}N\) is the two-dimensional subspace
\(\operatorname{span}(u,v,w)\cap\ker E\). The restriction of R
to \(\operatorname{span}(u,v,w)\) has characteristic polynomial
\((X+t)(X^2+tX+1)\), with distinct roots. Therefore
\(\operatorname{im}N\) has one eigenline for each root of
\(X^2+tX+1\). Each size-two Jordan block contributes exactly one
line to this image. There is precisely one such block at each of
these two roots, and none elsewhere. Finally \(\mathcal P=R^6\)
removes these size-two nilpotent parts and fixes each fifth-root
eigenvalue. Adding back the one t-eigenline proves (81.3). ∎

## 81.3 Exact spectral comparison through order 27

`hi_char2_transfer_spectrum.py` implements (81.3). At orders 3 and 9
it also computes \(R^6\) and checks its eigenspaces directly.
The three saved order-27 points each give
\[
 (M_0,M_1,M_2,M_3,M_4)=(147,145,146,146,145),
\]
with \(\lambda^2+t\lambda+1=0\) at labels 2 and 3. Each
order-27 calculation used less than one CPU second in the saved
Magma run.

For a comparison independent of primitive-root labeling, write
\(M_t\) for either multiplicity at a root of
\(X^2+tX+1\), and \(M_{t^{-1}}\) for either multiplicity at
the other two primitive fifth roots. With the central parameter
\(\rho=t=\delta^{-1}\), the results are:

| order and HI branch | \((M_0,M_t,M_{t^{-1}})\) for HI | cyclic \(\operatorname{Ad}(B)\) |
|---|---|---|
| 3, branch 0 | (3,2,1) | (3,2,1) |
| 9, branch 0 | (17,17,15) | (17,16,16) |
| 9, branch 1 | (17,16,16) | (17,16,16) |
| 27, branches 0,1,2 | (147,146,145) | (147,146,145) |

The choice \(\rho=\delta^{-1}\) matters: choosing
\(\rho=\delta\) interchanges the two primitive-root pairs in
this comparison. Both operators are semisimple of order dividing
five, so the matching spectra imply abstract linear similarity over
an algebraic closure in the matching finite cases. They do not
provide a uniform similarity transformation with the HI structure.
For example, the order-27 spectrum is the autocorrelation of the
five B-eigenvalue multiplicities \((5,6,5,5,6)\).

`hi_char2_cyclic_pentagon.m` verifies the Weyl relation, both
intertwining equations, the five-step recurrence, and the scalar
fifth power at orders 3,5,7,9,15,27. It calculates the displayed
cyclic spectra separately, including the fifth-root labels relative
to the central parameter. The uniform assertion (81.2) rests on
the direct proof, not on these finite checks.

## 81.4 The missing extraction of phases

A sufficient construction would now supply normalized full-Q phases
W and an invertible T such that
\[
 \boxed{T\,R(W)(I+D(W))=\operatorname{Ad}(B)\,T.}
 \tag{81.4}
\]
Equation (81.2) would then give every C by Section 60, and Section 58
would lift the resulting category to characteristic zero. Neither
the existence of B nor spectral agreement constructs W and T.

A first explicit extraction attempt fails. At n=3,9,27, form all five
spectral projectors of B. Take their columns and their Fourier
transforms of diagonal entries, allow every cyclic translation,
normalize the origin to 1, and allow a common rescaling of the
nonzero phases to obtain inverse norm \(\delta\), if possible.
Also try their relative norms from \(\mathbb F_{4^{2n}}\) to
\(\mathbb F_{4^{2n/3}}\). At orders 9 and 27, none of these
candidates even has constant inverse products before that final
rescaling: respectively 450 and 3780 trials in each of the direct
and relative-norm versions. At order 3, each version has 33
norm-compatible trials, but none passes the first quadratic for
the matching dimension \(\delta=\rho^{-1}\).
Its log is `hi_char2_cyclic_phase_probe_results.txt`.

This excludes those particular coordinate and trace extractions.
It does not exclude other choices of basis or a different use of
the cyclic matrix. In particular, the finite products \(b_j\) in
(81.1) are not asserted to be the HI phases; their bounded-degree
successive ratio would face the obstruction in Section 67.
**The uniform phase extraction, and infinitude, remain unproved.**

---

# 82. The cyclic operator requires a substantial change of basis

The natural Weyl basis in Section 81 does not give the corrected HI
operator by relabeling or rescaling its basis elements. There is a
uniform obstruction, and a growing rank bound on a more general
change of basis. These statements narrow the reconstruction problem;
they do not exclude the unrestricted intertwiner in (81.4).

## 82.1 A triangular quantum-binomial transition matrix

Write \(U=s^{-1}Y\), \(Z=s^{-1}X\), so \(U^n=Z^n=I\).
Use the following basis of the matrix algebra:
\[
 E_{a,b}=q^{-ab}U^aZ^{-b},\qquad (a,b)\in\mathbb Z_n^2.
\]
Let \(\mathsf C\) be the matrix of \(\operatorname{Ad}(B)\)
in this basis. For representatives \(0\le b,h<n\), define
\[
 K_{b,h}=s^{-2b}q^{bh}[T^h]
        \prod_{j=1}^{b}(1+s q^{1-2j}T).
\]
Then
\[
 \boxed{\mathsf C_{(a,b),(c,e)}=\delta_{b,c}K_{b,[a+e]_n}.}
 \tag{82.1}
\]
To verify this, conjugate \(U^cZ^{-e}\) using
\(Z\mapsto U\) and
\(U\mapsto s^{-2}Z^{-1}(I+qsU)\), and collect powers of U.
The factor \(q^{-ab}\) in the basis makes the coefficient depend
on a and e only through their sum.

In particular,
\[
 K_{b,h}=s^{h-2b}q^{-h(b-h)}{b\brack h}_{q^2}\quad(0\le h\le b),
 \qquad K_{b,h}=0\quad(h>b).
 \tag{82.2}
\]
Every displayed quantum binomial is nonzero: its numerator and
denominator involve only \(1-q^{2j}\) with \(1\le j\le b<n\).
Thus the exact number of nonzero entries of \(\mathsf C\) is
\[
 \operatorname{nz}(\mathsf C)=\frac{n^2(n+1)}2.
 \tag{82.3}
\]

## 82.2 Exact support of the corrected HI operator

For any normalized full-Q phase candidate in characteristic two,
write \(\mathcal P=R(I+D)\) and \(t=\delta^{-1}\), as in
Section 60. The vector identities there give the entry formula
\[
\begin{aligned}
 \mathcal P_{(a,b),(c,e)}={}&\delta_{b,c}A_{b,a+e}
 +(t\delta_{a,0}+t^2\delta_{b,0})A_{c,e}
 +t^2\delta_{b,0}\delta_{c,0}\\
 &+(t\delta_{e,0}+t^2\delta_{c,0})A_{b,a}.
\end{aligned}
 \tag{82.4}
\]
All A entries are nonzero; the exceptional ones are
\(A_{0,0}=t\) and \(A_{a,0}=A_{0,a}=\delta=t^2\) for
\(a\ne0\). These facts determine the support in (82.4) exactly:

| number of zero indices among a,b,c,e | nonzero entries |
|---:|---:|
| 0 | \((n-1)^3\) |
| 1 | \(4(n-1)^3\) |
| 2 | \(4(n-1)^2+2(n-1)\) |
| 3 | \(2(n-1)\) |
| 4 | 1 |

For example, with no zero index the only term is the transfer term,
so b=c is necessary and sufficient. With just a=0, the entry is
\((\delta_{b,c}+t)A_{c,e}\), always nonzero; the other three
one-zero cases work the same way. For exactly two zeros, the pairs
(a,e) and (b,c) contribute only when b=c and a+e=0, respectively;
each of the other four pairs contributes its entire square. Direct
substitution of the exceptional entries gives the last two rows.
Hence
\[
 \boxed{\operatorname{nz}(\mathcal P)
       =5n^3-11n^2+11n-4.}
 \tag{82.5}
\]
No cubic equation is used in this count.

The difference between (82.5) and (82.3) is
\[
 \frac{(n-1)(9n^2-14n+8)}2>0.
\]
A monomial change of basis preserves the number of nonzero entries.
Therefore **no permutation and rescaling of the Weyl basis can
identify \(\mathsf C\) with \(\mathcal P\), at any odd n\(\ge3\)**.
This conclusion holds even in the finite cases with matching spectra.

## 82.3 A rank bound beyond basis rescaling

In the same ordered bases, \(\mathsf C-R\) splits, after a row
permutation, into n Hankel-circulant blocks with coefficient rows
\(K_{b,h}-A_{b,h}\). The b=0 block is the constant nonzero
matrix and has rank one. Every other block is nonzero already at
h=0: \(K_{b,0}=s^{-2b}\notin\mathbb F_4\), whereas
\(A_{b,0}=\delta\in\mathbb F_4\). Indeed,
\(s^{-2b}\in\mathbb F_4^\times\) would imply \(n\mid2b\),
which is impossible for \(0<b<n\). Thus
\[
 \operatorname{rank}(\mathsf C-R)\ge n.
 \tag{82.6}
\]

More generally, let S be any invertible diagonal matrix. The zero
pattern in (82.2) still ensures at least n-1 nonzero blocks in
\(S^{-1}\mathsf C S-R\), those with \(0\le b<n-1\).
Suppose \(T\mathcal P=\mathsf C T\), with T invertible, and
\(\operatorname{rank}(T-S)=r\). Conjugate first by S and put
\(T'=S^{-1}T\), so \(\operatorname{rank}(T'-I)=r\). Then
\[
 \operatorname{rank}(S^{-1}\mathsf C S-\mathcal P)
 \le 2r,
\]
by writing the difference as a commutator with \(T'-I\), followed
by multiplication by an invertible matrix. Since
\(\operatorname{rank}(\mathcal P-R)=3\), it follows that
\[
 \boxed{r\ge\left\lceil\frac{n-4}{2}\right\rceil
             =\frac{n-3}{2}\qquad(n\text{ odd}).}
 \tag{82.7}
\]
A correction of fixed rank to a diagonal change of basis therefore
cannot solve the operator reconstruction for unbounded n.

## 82.4 Exact comparisons and a second basis probe

`hi_char2_cyclic_basis.py` verifies (82.1) against direct conjugation
of every Weyl-basis matrix at orders 3 and 9. It checks the supports
and block ranks on all the saved branches at 3,9,27:

| n | \(\operatorname{nz}(\mathcal P)\) | \(\operatorname{nz}(\mathsf C)\) | \(\operatorname{rank}(\mathsf C-R)\) |
|---:|---:|---:|---:|
| 3 | 65 | 18 | 7 |
| 9 | 2849 | 405 | 73 |
| 27 | 90689 | 10206 | 703 |

In these cases the b=0 block has rank one and every other block has
full rank n. Thus an intertwiner with \(S=I\), when one exists,
has \(\operatorname{rank}(T-I)\ge2,35,350\), respectively.
The full-rank assertion for the individual nonzero blocks is only
verified at these finite orders; the uniform bound is (82.6).

A second probe uses the five consecutive quantum variables of
Section 81 and the rays
\((1,0),(0,1),(-1,0),(-1,-1),(0,-1)\).
For a lattice point \(p v_j+r v_{j+1}\) in one of these cones,
take the cluster monomial \(q^{-pr}X_j^pX_{j+1}^r\).
The centered n-by-n square gives a basis in the checked orders 3
and 9. The cyclic operator in that basis has respectively 15 and
416 nonzero entries, so it also fails direct identification with
\(\mathcal P\). Its difference from R has rank 7 at order 3,
and ranks 72 and 73 on the two order-9 branches. This particular
basis does not turn reconstruction into a small-rank correction.
No uniform basis or category theorem is inferred from this probe.

The unrestricted construction of W and T in (81.4) is still open.
**These basis obstructions do not establish infinitude or
nonexistence of HI categories.**

---

# 83. Cayley coordinates and a complete order-33 certificate

There is a useful uniform coordinate system for the infinite sequence
\(n=2^r+1\), with r odd. It handles the inverse norms and Frobenius
covariance exactly, including the points omitted by an affine Cayley
chart. It also makes a complete order-33 search practical. The result
is a new finite existence certificate and a uniform parametrization;
the additive equations have not been solved for unbounded r.

## 83.1 A conic model for the cyclic labels

Put \(q=2^r\), \(n=q+1\),
\[
 F=\mathbb F_q,\qquad K=\mathbb F_{q^2},\qquad
 E=\mathbb F_{q^4},\qquad
 \delta\in\mathbb F_4,\quad\delta^2+\delta+1=0.
\]
Take \(\zeta\in K\) of order n, and set
\[
 x_0=\infty,\qquad
 x_a=\delta+\frac1{1+\zeta^a}\quad(a\ne0).
 \tag{83.1}
\]
Since r is odd, \(\delta^q=\delta+1\), and
\(\zeta^q=\zeta^{-1}\). Thus \(x_a\in F\), and the nonzero
cyclic labels map bijectively onto F. Direct calculation gives
\[
 x_{-a}=x_a+1,\qquad x_{2a}=x_a^2+1,\qquad
 x_{a+b}=\frac{x_ax_b+1}{x_a+x_b+1}.
 \tag{83.2}
\]
The last identity has its projective interpretation when a, b, or
a+b is zero. In particular its denominator vanishes exactly when
b=-a. These formulas use the same conic group law over \(\mathbb F_2\)
at every odd r.

Choose \(\eta\in\mathbb F_{16}\) satisfying
\(\eta^4+\eta=1\). Because r is odd,
\(\eta\notin K\) and \(\eta^{q^2}=\eta+1\). For a function
\(V:F\longrightarrow\mathbb P^1(K)\), define
\[
 W_0=1,\qquad
 W_a=\delta^2\frac{V(x_a)+\eta}{V(x_a)+\eta+1}
 \quad(a\ne0),
 \tag{83.3}
\]
where \(V(x_a)=\infty\) means \(W_a=\delta^2\).
For finite V the numerator and denominator are both nonzero.
Then
\[
 \boxed{\displaystyle
 W_aW_{-a}=\delta\ (a\ne0),\quad W_a^4=W_{2a}
 \quad\Longleftrightarrow\quad
 V(x+1)=V(x)+1,\quad V(x^2)=V(x)^4.}
 \tag{83.4}
\]
Here addition and fourth powers fix infinity. To prove the forward
construction, use (83.2), \(\eta^4=\eta+1\), and
\((\delta^2)^2=\delta\). Conversely Frobenius covariance iterated
r times gives \(W_a^{q^2}=W_{-a}=\delta/W_a\). Therefore
\[
 V(x_a)=\eta+\frac{W_a}{W_a+\delta^2}
 \tag{83.5}
\]
is fixed by the q-squared power map whenever its denominator is
nonzero, so lies in K. The value \(W_a=\delta^2\) gives infinity.
Substitution proves both functional identities in (83.4).

This is a bijection onto all canonical norm/Frobenius phase data,
not an additional ansatz. Indeed \(\operatorname{ord}_{q+1}(2)=2r\):
no smaller positive power is one modulo q+1, using
\(2^r=-1\) for exponents between r and 2r. Section 71 therefore
puts every canonical full phase solution in E.

## 83.2 Trace-zero coordinates and every point at infinity

Write \(\tau(x)=\operatorname{Tr}_{F/\mathbb F_2}(x)\), and let
\[
 T=\{y\in F:\tau(y)=0\}.
\]
The map \(x\mapsto x^2+x\) identifies the pairs \(\{x,x+1\}\)
with T. Since \(\tau(x+1)=\tau(x)+1\), all functions in (83.4)
are uniquely of the form
\[
 \boxed{\displaystyle
 V(x)=\tau(x)+U(x^2+x),\qquad
 U:T\longrightarrow\mathbb P^1(K),\quad U(y^2)=U(y)^4.}
 \tag{83.6}
\]
The formula includes infinity. To see uniqueness, subtract tau
from V; the result is constant on the two-element fibers. The
remaining Frobenius law is exactly the displayed law on U.

Let the squaring orbits on T have lengths \(d_1,\ldots,d_s\).
Each \(d_i\mid r\), and \(\sum_i d_i=q/2\). An orbit of length
d permits an arbitrary initial value in
\(\mathbb P^1(\mathbb F_{4^d})\); subsequent values are its fourth
powers. Hence the set of all canonical norm/Frobenius assignments
has the explicit product description
\[
 \boxed{\displaystyle
 \prod_{i=1}^s\mathbb P^1(\mathbb F_{4^{d_i}}),\qquad
 N_r=\prod_{i=1}^s(4^{d_i}+1).}
 \tag{83.7}
\]
Its finite Cayley chart is an affine binary space of dimension q,
with exactly \(2^q\) points. This count concerns the ambient
norm/Frobenius equations, not Q or C.

For r=3 the orbit lengths are 1,3, giving \(N_3=5\cdot65=325\).
For r=5 they are 1,5,5,5, giving
\[
 N_5=5\cdot1025^3=5,384,453,125.
 \tag{83.8}
\]
If r is an odd prime, the only squaring-fixed element of T is zero;
every other orbit has length r. Consequently the uniform ambient
count is \(5(4^r+1)^{(2^{r-1}-1)/r}\). Its positivity alone says
nothing about HI existence.

The finite-chart exporter uses binary linear algebra on the
functional equations in (83.4). Algebraic degree at most r-1
already describes the whole finite chart: V minus any affine
particular solution descends to the vector space F/\(\mathbb F_2\)
of dimension r-1. Every function on that space has a squarefree
polynomial expression of degree at most r-1.

For the boundary, infinity must occupy whole orbits under
\(x\mapsto x+1\) and \(x\mapsto x^2\), of sizes \(2d_i\).
For each nonempty union of these orbits, the boundary enumerator
restricts the full finite-chart basis to the complement and removes
dependent directions. This loses no finite values on the remaining
orbits, by (83.7). The restricted binary dimension is
\(q-\sum_{i\text{ infinite}}2d_i\). Thus all boundary charts are
disjoint and exhaustive.

`hi_char2_cayley_geometry.m` checks (83.1)--(83.6), both finite
and infinite choices, and all conic additions at r=1,3,5,7,9.
Every exact check passes. Its larger orders 129 and 513 are checks
of the coordinate identities only; they are not HI certificates.

## 83.3 All order-33 phase points and independent cubic verification

The finite chart at order 33 has binary dimension 32. Gray-code
enumeration checks every one of its \(2^{32}\) assignments using
exact finite-field tables and all 28 quadratic representatives.
The 15 boundary charts contribute another 1,089,485,829 assignments.
The completed results are:

| Search at order 33 | Assignments | First Q | Full Q |
|---|---:|---:|---:|
| Finite Cayley chart | 4,294,967,296 | 4,205,046 | 80 |
| All boundary charts | 1,089,485,829 | 1,060,796 | 20 |
| Total | 5,384,453,125 | 5,265,842 | 100 |

The 80 finite-chart points form four free orbits under
\((\mathbb Z_{33})^\times\). The 20 boundary points form one
additional free orbit; in every one, infinity occurs exactly at
labels 11 and 22. The enumeration is closed under every scalar
reindexing. Each of the five orbits splits into two Frobenius
orbits of length 10 over \(\mathbb F_4\).

One representative of every scalar orbit is converted to the
standard row-certificate format and independently checked by
`hi_finite_field_certificate.py`. This verifier reconstructs B
from its row, without using the search's Cayley table or quadratic
orbit reduction. For each of the five representatives it verifies
field irreducibility, the normalization and row reflection,
all \(33^2=1089\) quadratic equations, all
\(33^4=1,185,921\) cubic equations, and nonzero global dimension.
Every check passes. Reindexing supplies the same conclusions at
all 100 points.

The saved field polynomial is
\[
 t^{20}+t^{10}+t^9+t^7+t^6+t^5+t^4+t+1.
\]
Its binary encoding is 1050355; the encoded dimension parameter
is 476308. The five JSON certificates are identified by finite
chart masks 64989013, 251496637, 414317049, 1996608439, and boundary
chart 8 with mask 191761516. Their filenames begin
`hi_finite_field_certificates/hi_finite_field_33_char2_cayley`.
These masks identify points in the exported binary basis; they
are not theoretical parameters for an infinite family.

For example, the first complete certificate can be verified without
Magma or rerunning the search:

```sh
python hi_finite_field_certificate.py --verify hi_finite_field_certificates/hi_finite_field_33_char2_cayley_64989013.json
```

We have therefore proved the following finite assertions:

1. There are exactly 100 canonical full phase solutions at order
   33 over an algebraic closure of characteristic two, for the
   fixed choice of delta. Their coordinate algebra is
   \((\mathbb F_{2^{20}})^{10}\) over \(\mathbb F_4\).
2. Before character normalization, the full phase scheme has
   3300 geometric points, with algebra
   \((\mathbb F_{2^{20}})^{330}\).
3. At order 33, Q together with Frobenius covariance implies
   every cubic in the phase parametrization. The implication
   holds as an ideal equality inside the finite etale
   norm/Frobenius algebra. Full Q alone was not classified here.
4. The algebraic reconstruction and categorical lifting argument
   of Section 58 gives a complex HI fusion category at order 33.
   This argument does not establish a unitary structure.

As an independent small-order check, the same finite/boundary
method exhausts all 325 ambient assignments at order 9, finding
24 first-Q points and 12 full-Q points in two orbits of six.
Six lie in the finite chart and six in the boundary. Both orbits
again pass the complete independent cubic verifier.

The arithmetic count from Section 73 gives the correct new value:
\(1093=33^2+4\) is fundamental, its ordinary real-quadratic
class number is 5, and the unit index is one. Thus
\[
 R(33)=\varphi(33)h(1093)=20\cdot5=100.
\]
`hi_char2_ray_count33_results.txt` records the independently
certified PARI class group (`bnfcertify`), unit index, and ray degree.
This agreement extends the finite evidence for the arithmetic count;
an identification of the two constructions remains unproved.

## 83.4 Restrictions on short formulas and the remaining task

The affine-linear version of (83.4) has
\(V(x)=\gamma+L(x)\), where \(\gamma\in\mathbb F_4\),
L is binary linear, \(L(x^2)=L(x)^4\), and \(L(1)=1\).
There are exactly \(4^r\) such functions. One can enumerate them
without privileging a normal basis: if \(\theta^{2^i}\) is a
normal basis of F, choose \(v\in K\) with
\(\operatorname{Tr}_{K/\mathbb F_4}(v)=1\) and prescribe
\(L(\theta^{2^i})=v^{4^i}\). The linear search has 4,64,1024
candidates at n=3,9,33, respectively. Full-Q counts are 2,0,0.

The full algebraic-degree-at-most-two chart has binary dimension
8 at order 9 and 22 at order 33. It contains all six finite-chart
order-9 solutions, but none of the 4,194,304 order-33 candidates
satisfies full Q. The latter search has 4188 first-Q points.
Among the 80 actual finite-chart order-33 points, 70 have algebraic
degree four and ten have degree three. All ten degree-three
points belong to the orbit represented by mask 414317049.

A further exact interpolation test allows arbitrary binary linear
maps \(L_i:F\to K\) with \(L_i(x^2)=L_i(x)^4\), and asks for
\[
 V(x)=\gamma+L_0(x)+L_1(h(x^2+x)),\qquad\gamma\in\mathbb F_4.
 \tag{83.9}
\]
At order 33 none of the 80 finite-chart solutions has this form
for \(h(y)=1/(y+1)\), or for any monomial \(h(y)=y^j\),
\(1\le j\le31\). These tests allow every semilinear map, not
only a selected coefficient or normal basis. The reciprocal
denominator never vanishes because \(\tau(1)=1\).
At order 9 the reciprocal and several monomial versions contain
all six finite-chart solutions, illustrating why that smaller
case alone does not validate an extrapolation.
Section 83.6 strengthens this to an obstruction for arbitrary
Frobenius-compatible h at order 33, including all boundary solutions.

The uniform task in this coordinate system is now explicit:
choose values in the projective-line product (83.7) for unbounded
odd r so that the additive HI equations hold. The parametrization,
positive ambient counts, and finite completion at order 33 do not
provide such choices. **Infinitude remains unproved.**

## 83.5 Field-trace extension preserves the normalizations but fails Q

The conic coordinates admit a natural extension to larger fields.
Let q=\(2^r\), with r odd, and let s be another positive odd
integer. Starting from V in (83.4), define
\[
 \widetilde V(x)=V\!\left(
   \operatorname{Tr}_{\mathbb F_{q^s}/\mathbb F_q}(x)\right),
 \qquad x\in\mathbb F_{q^s}.
 \tag{83.10}
\]
Embed its values from \(\mathbb F_{q^2}\) into
\(\mathbb F_{q^{2s}}\), and retain the value infinity where needed.
Since s is odd, the trace of 1 is 1, and trace commutes with
squaring. Consequently
\[
 \widetilde V(x+1)=\widetilde V(x)+1,\qquad
 \widetilde V(x^2)=\widetilde V(x)^4.
\]
The Cayley construction therefore produces normalized,
Frobenius-covariant phases at order \(q^s+1\). They have exactly
the phase values of the original function, embedded into the
larger ambient field. This is a proved extension of the ambient
normalization equations; it is not an extension theorem for HI.

More explicitly, (83.1) and the field trace define a label map
\(\pi:\mathbb Z_{q^s+1}\to\mathbb Z_{q+1}\), with
\(\pi(0)=0\), no other zero values, and
\[
 \pi(-a)=-\pi(a),\qquad \pi(2a)=2\pi(a).
\]
Every nonzero target label has exactly \(q^{s-1}\) preimages.
The extended phases are \(\widetilde W_a=W_{\pi(a)}\).
In particular, if s>1 then characteristic two gives the uniform
identity
\[
 \sum_{a\in\mathbb Z_{q^s+1}}\widetilde W_a=1.
 \tag{83.11}
\]
This label map is not assumed to be additive, so this construction
is not a cyclic quotient inflation.

The first additive check rejects the proposed extension on every
available input in two complete tests:

| Source order | Extension degree s | Target order | Certified source points | First-Q survivors |
|---|---:|---:|---:|---:|
| 9 | 3 | 513 | 12 | 0 |
| 33 | 3 | 32769 | 100 | 0 |

`hi_char2_cayley_trace.py` generates the exact Magma calculation.
For every input it verifies the field embedding, trace fibers,
both label symmetries, every inverse norm, Frobenius covariance,
and (83.11), before evaluating the first quadratic. All first-Q
residuals are nonzero, recorded in the original finite-field
binary encoding in `hi_char2_cayley_trace_results.txt`.
Thus this trace rule cannot supply an induction from either of
these complete source families along degree-three extensions.
No nonexistence assertion about the target orders follows.

## 83.6 An arbitrary single nonlinear feature still fails at order 33

There is a structural test for (83.9) that does not enumerate h.
It applies at r=3 and r=5. Put
\[
 F=\mathbb F_{2^r},\quad K=\mathbb F_{4^r},\quad
 T=\ker\operatorname{Tr}_{F/\mathbb F_2},\quad
 H=\ker\operatorname{Tr}_{K/\mathbb F_4}.
\]
Write \(\sigma(x)=x^2\), \(\varphi(v)=v^4\), and
\[
 S=\mathbb F_2[t]/(1+t+\cdots+t^{r-1}).
 \tag{83.12}
\]
For these two r the displayed polynomial is irreducible, so S is
\(\mathbb F_4\) or \(\mathbb F_{16}\), respectively. Let t act
by sigma on T and by varphi on H. The normal-basis decomposition
shows that T is a line over S and H is a plane over S. These are
**endomorphism-field actions**: in particular, at r=5 the field
\(S=\mathbb F_{16}\) is not a subfield of \(K=\mathbb F_{2^{10}}\).

Choose a nonzero generator theta of the S-module T and define
\(s(x)\in S\) by \(x=s(x)\theta\). Since r is odd, the
projection onto H is
\[
 \pi(v)=v+\operatorname{Tr}_{K/\mathbb F_4}(v).
\]
For a normalized V, finite except possibly at x=0,1, form
\[
 c(x)=\operatorname{Tr}_{K/\mathbb F_4}(V(x)),\qquad
 Z(x)=s(x)^{-1}\pi(V(x)),\qquad x\in T\setminus\{0\}.
 \tag{83.13}
\]
Include c(0) when V(0) is finite. The inverse in Z is an S-module
scalar. Both c and Z are constant on the squaring orbits in T.

**Single-feature criterion.** Such a V has the form (83.9) for some
arbitrary function \(h:T\to F\) with \(h(y^2)=h(y)^2\), arbitrary
binary linear intertwiners \(L_i(x^2)=L_i(x)^4\), and
\(\gamma\in\mathbb F_4\), if and only if

1. the values c(x) take at most two distinct values;
2. all Z(x) lie in one affine S-line in the S-plane H.

For the boundary version, set h(0) and V(0),V(1) to infinity and
apply the formula at all other inputs. The same criterion holds.

**Proof.** The translation identity forces \(L_0(1)=1\).
For \(x\in T\), intertwining gives
\[
 \operatorname{Tr}_{K/\mathbb F_4}(L_0(x))=0,\qquad
 c(x)=\gamma+L_1(1)\operatorname{Tr}_{F/\mathbb F_2}(h(x^2+x)).
\]
This proves the first condition. The restrictions of the projected
linear maps to T are S-linear. Hence, for some A,B in H,
\[
 \pi(V(x))=s(x)A+s\!\left(h(x^2+x)+
       \operatorname{Tr}_{F/\mathbb F_2}(h(x^2+x))\right)B.
\]
Division by s(x) proves the affine-line condition.

Conversely, write \(Z(x)=A+\lambda(x)B\) on such a line, and
write \(c(x)=\gamma+b(x)c\), with \(b(x)\in\mathbb F_2\).
Choose \(\gamma=V(0)\) in the finite chart; on the boundary choose
either trace value. If only one trace value occurs, c can be any
nonzero element of \(\mathbb F_4\). Both b and lambda can be
chosen constant on the squaring orbits. On \(F=\mathbb F_2\oplus T\),
define
\[
 L_0(\epsilon+s\theta)=\epsilon+sA,\qquad
 L_1(\epsilon+s\theta)=\epsilon c+sB.
\]
The map \(x\mapsto x^2+x\) is a bijection of T, so prescribe
\[
 h(x^2+x)=b(x)+s(x)\lambda(x)\theta\quad(x\ne0).
\]
Set h(0)=0 in the finite chart and h(0)=infinity on the boundary.
These formulas commute with the required Frobenius actions and
reconstruct V on T. Translation by 1 reconstructs it on the rest
of F. This proves sufficiency as well. ∎

The complete order-9 and order-33 lists have no poles outside
\(\{0,1\}\), so this criterion applies to every saved point.
Its exact results are:

| Order | Chart | Number of trace values | Affine-line condition | Points |
|---:|---|---:|---|---:|
| 9 | finite | 2 | holds | 6 |
| 9 | boundary | 1 | holds | 6 |
| 33 | finite | 3 | fails | 50 |
| 33 | finite | 2 | fails | 20 |
| 33 | finite | 3 | holds | 10 |
| 33 | boundary | 3 | fails | 20 |

Thus **none of the 100 order-33 solutions admits a single nonlinear
feature of this form, for any Frobenius-compatible h**. All 12
order-9 points do, and the verifier explicitly reconstructs each.
This excludes a much larger family than the reciprocal and power
tests in Section 83.4. It does not exclude constructions with more
features or assert nonexistence at any order.

`hi_char2_cayley_semilinear_rank.py` verifies the module actions,
checks the affine-line condition both by scalar orbits and by
determinants over S, and reconstructs every accepted function at
every field input. It also reconstructs synthetic positive examples
at both orders, including ten at order 33. The complete pointwise
certificate is `hi_char2_cayley_semilinear_rank_certificates.json`.

## 83.7 Why the successful two-feature fits give no HI constraint

Before the preceding criterion was found, the single-feature search
was enlarged to every distinct invertible restriction
\[
 M(y)=\sum_{i=0}^{r-1}\epsilon_i y^{2^i},\qquad
 \epsilon_i\in\mathbb F_2,
\]
on T. There are three such restrictions at r=3 and fifteen at r=5.
The exact tests include every power h, the reciprocal 1/(y+1),
and the boundary reciprocal 1/y. At order 33 they give 495 feature
spaces, with 20 distinct row spaces, and no fits. Section 83.6 now
explains this without restricting the choice of h or M.

Adding a second nonlinear term changes the outcome:
\[
 V(x)=\gamma+L_0(x)+L_1(h_1(M(x^2+x)))
                    +L_2(h_2(M(x^2+x))).
 \tag{83.14}
\]
At r=5, choose two distinct functions from
\[
 \frac1{y+1},\quad y^3,\quad y^5,\quad y^7,\quad
 y^{11},\quad y^{15},\quad y^{31}.
 \tag{83.15}
\]
The omitted nonzero powers are either in the same doubling orbit
as a listed power, which can be absorbed into the output intertwiner,
or are already contained in the linear term. With the fifteen M,
this gives 315 spaces, of which 23 are distinct. Their union fits
all 80 finite-chart solutions. **It also fits every one of the
\(2^{32}\) finite norm/Frobenius functions, including every failure
of Q in that chart.**

Here is a small exact certificate of this full coverage. Seven
distinct largest linear spaces have dimension 32 before imposing
the two binary translation constraints. Each contains the common
24-dimensional space of homogeneous variations U with U(x+1)=U(x),
U(0)=0, and relative trace zero on every nonzero squaring orbit in T.
The remaining data are four
elements \(c_0,c_1,c_2,c_3\in\mathbb F_4\): the value at zero
and the relative traces on the three nonzero orbits. The seven
largest spaces, on this quotient, are exactly the seven planes
\[
 \sum_{i=1}^3 e_i(c_i+c_0)=0,
 \qquad 0\ne(e_1,e_2,e_3)\in\mathbb F_2^3.
 \tag{83.16}
\]
Every triple of elements of \(\mathbb F_4\) has a nontrivial
binary linear relation, since \(\dim_{\mathbb F_2}\mathbb F_4=2\).
Thus these seven planes cover all trace patterns, proving coverage
of the entire affine chart. Of the 256 trace patterns, 168 lie in
one plane, 84 lie in three planes, and four lie in all seven.

`hi_char2_cayley_two_feature_coverage.py` checks the common fiber,
identifies each of the seven binary normals, checks all 256 trace
patterns, and compares their full affine span with the independent
32-dimensional Cayley export. This proves coverage without
enumerating \(2^{32}\) functions. The measured peak memory is under
20 MiB. The fitting scripts and results are listed below.

Consequently the successful two-feature interpolation at order 33
provides no evidence that those coefficients satisfy Q at a larger
order. A construction must select the coefficients and prove their
additive identities. That step, and infinitude, remain unresolved.

---

# 84. Small quadratic error does not make the Alltop approximation close to HI

The Alltop construction of Section 41 has an additional asymptotic
feature. Changing its exceptional entry to the HI amplitude makes
the quadratic operator error tend to zero as the prime order grows.
Nevertheless, a necessary cubic operator polynomial stays a definite
distance from zero. Thus this particular approximation cannot be
completed by a perturbation tending to zero in operator norm.
The result does not rule out other large-order approximations or
entrywise corrections whose operator norms remain substantial.

## 84.1 An explicit nearby contraction and a vanishing Q error

Let p be a prime at least 5, let \(\zeta=e^{2\pi i/p}\), and
choose \(c\not\equiv0\pmod p\). Here we use the positive
dimension embedding
\[
 d=\frac{p+\sqrt{p^2+4}}2,\qquad t=d^{-1},\qquad
 \alpha=\frac{\sqrt d}{d-1},\qquad e=\frac1{d-1}.
\]
Take the inverse-normalized phases
\[
 W_0=-1,\qquad W_a=-\sqrt d\,\zeta^{ca^3}\quad(a\ne0),
\]
and form A by the usual phase formulas. In particular,
\[
 A_{g,h}=-\alpha\zeta^{3cgh(g-h)}
 \quad\text{if }gh(g-h)\ne0,
\]
while all nonorigin exceptional entries are -e and
\(A_{0,0}=1-e\). Define the transfer operator with the verified
index convention
\[
 R_{(a,b),(c',f)}=\mathbf1_{b=c'}A_{b,a+f}.
\]
Define a comparison matrix by
\[
 \overline A_{g,h}=-p^{-1/2}\zeta^{3cgh(g-h)}\quad(g\ne0),
 \qquad \overline A_{0,h}=\mathbf1_{h=0}-e,
 \tag{84.1}
\]
and let \(\overline R\) be its transfer operator.

For a fixed nonzero g, the row in (84.1) is a quadratic chirp.
Its discrete Fourier transform has modulus one at every frequency,
by the elementary nondegenerate quadratic Gauss-sum identity.
Indeed, expanding the squared modulus and summing over the
difference of two indices leaves only difference zero, since the
quadratic coefficient is nonzero and p is odd.
The zero row has Fourier eigenvalues -t at frequency zero and 1
elsewhere, since \(pe=1+t\). As the transfer operator is a
permutation of these reverse-circulant blocks, it follows that
\[
 \|\overline R\|_{\rm op}=1,\qquad
 I-\overline R^*\overline R\text{ is positive of rank one},
 \qquad
 p^2-k\le\|\overline R^k\|_{\rm HS}^2\le p^2.
 \tag{84.2}
\]
The last bounds follow by telescoping the defect of the kth power:
it is a positive contraction of rank at most k.

Each nonzero row differs from (84.1) by a change in the chirp
coefficient and by corrections at its two exceptional entries.
Therefore
\[
 \boxed{\displaystyle
 \|R-\overline R\|_{\rm op}\le\varepsilon_p:=
 \sqrt{\frac{d+1}{d-1}}-1+\frac2{\sqrt d+1}
 =O(p^{-1/2}).}
 \tag{84.3}
\]
Indeed \(\alpha\sqrt p=\sqrt{(d+1)/(d-1)}\) and
\(\alpha-e=1/(\sqrt d+1)\); each exceptional correction is
a multiple of a permutation matrix in the corresponding block.
The zero block is identical in R and \(\overline R\).

Both quadratic operator identities in (50.2) consequently have
error at most \(2\varepsilon_p+\varepsilon_p^2\) for R.
The rank-one exceptional projections are exactly those in (50.2).
Thus this is an approximation to Q even in operator norm, not just
an array with small individual residual entries.

## 84.2 An exact fifth trace from a torus character sum

Now restrict to \(p\equiv2\pmod3\). For five cyclic variables,
expanding the phase in the trace gives
\[
 \sum_{i\bmod5}x_i(x_{i-1}+x_{i+1})
                  (x_i-x_{i-1}-x_{i+1})
 =-2\sum_{i\bmod5}x_{i-1}x_ix_{i+1}.
 \tag{84.4}
\]
On \((\mathbb F_p^\times)^5\), the monomial map
\[
 y_i=x_{i-1}x_ix_{i+1}
\]
is bijective. Its integer exponent matrix is the circulant
matrix with diagonal and two neighboring diagonals equal to one;
its determinant is 3. This determinant is invertible modulo p-1
under the stated congruence assumption. Hence, for every
\(\kappa\in\mathbb F_p^\times\),
\[
 \boxed{\displaystyle
 \sum_{x_i\ne0}\zeta^{\kappa\sum_i x_{i-1}x_ix_{i+1}}
 =\prod_{i=1}^5\sum_{y_i\ne0}\zeta^{\kappa y_i}=-1.}
 \tag{84.5}
\]
In the transfer trace, \(\kappa=-6c\ne0\).

For completeness, all terms with zero indices can also be summed
exactly. Put \(m=p-1\), \(u=1-em\), and \(v=1-e\).
The following table gives the contribution per subset of zero
indices; its multiplicity is listed separately.

| Zero-index pattern in the five-cycle | Multiplicity | Contribution per subset |
|---|---:|---:|
| No zeros | 1 | \(p^{-5/2}\) |
| One zero | 5 | \(m^2(m-e)/p^2\) |
| Two adjacent zeros | 5 | \(e^2m^2/p^{3/2}\) |
| Two nonadjacent zeros | 5 | \(-mu^2/p^{3/2}\) |
| Three zeros, remaining indices adjacent | 5 | \(e^2vm^2/p\) |
| Three zeros, remaining indices nonadjacent | 5 | \(e^2mu/p\) |
| Four zeros | 5 | \(-e^2v^2m/p^{1/2}\) |
| Five zeros | 1 | \(v^5\) |

Here each nonzero-index factor has coefficient \(-p^{-1/2}\).
At a zero index i the factor is
\(\mathbf1_{x_{i-1}+x_{i+1}=0}-e\). For example, with only
\(x_0=0\), write the remaining variables as a,b,c,f. The phase
is \(\kappa bc(a+f)\). The delta term has \(m^3\) summands
and zero phase. The unrestricted nonzero sum of the phase is
\(m^2\), since summing separately over a and f gives
\((-1)^2\) for every b,c. This proves the one-zero row of the
table. With two adjacent zeros the remaining phase is a nonzero
multiple of a product of three nonzero variables, whose character
sum is \(-m^2\). In the other rows the surviving phase is zero,
and the displayed delta factors count the indicated nonzero pairs.
These observations verify all the entries.

Summing the table gives the exact formula
\[
\begin{aligned}
 \operatorname{Tr}\overline R^5={}&p^{-5/2}
 +\frac{5m^2(m-e)}{p^2}
 +\frac{5e^2m^2-5mu^2}{p^{3/2}}\\
 &+\frac{5e^2vm^2+5e^2mu}{p}
 -\frac{5e^2v^2m}{\sqrt p}+v^5
 =5p-14+O(p^{-1}).
 \tag{84.6}
\end{aligned}
\]
In particular \(p^{-2}\operatorname{Tr}\overline R^5\to0\).
This is an exact character-sum calculation followed by an elementary
asymptotic expansion; it is not inferred from a numerical trace.

## 84.3 A nonvanishing cubic error and an operator-distance lower bound

Every physical HI transfer operator satisfies the necessary
polynomial identity of Section 50,
\[
 F_t(R):=(R^5-I)(R^3+tR+tI)=0.
\]
For the Alltop phases at the HI amplitude, however,
\[
 \boxed{\displaystyle
 \lim_{\substack{p\to\infty\\p\equiv2\ (3)}}
 \frac{\|F_t(R)\|_{\rm HS}^2}{p^2}=2.}
 \tag{84.7}
\]
To prove this, first use (84.2) and (84.6). If
\(E_3=I-(\overline R^3)^*\overline R^3\), then
\(E_3\ge0\), \(\operatorname{rank}E_3\le3\), and
\(\|E_3\|\le1\). Therefore
\[
 \operatorname{Tr}((\overline R^3)^*\overline R^8)
 =\operatorname{Tr}\overline R^5
   -\operatorname{Tr}(E_3\overline R^5),
 \qquad |\operatorname{Tr}(E_3\overline R^5)|\le3.
\]
It follows that
\(p^{-2}\|\overline R^8-\overline R^3\|_{\rm HS}^2\to2\).
On the other hand, (84.3), t tending to zero, and the usual
telescoping bound for differences of powers give
\[
 \|F_t(R)-(\overline R^8-\overline R^3)\|_{\rm op}\to0.
\]
Normalized Hilbert--Schmidt norm is bounded by operator norm, so
this proves (84.7).

There is also a quantitative consequence for possible corrections.
For any physical HI operator \(R_*\), Q gives \(\|R_*\|\le1\)
and C gives \(F_t(R_*)=0\). Since \(\|R\|\le1+\varepsilon_p\),
telescoping each term of
\(F_t(X)=X^8-X^3+t(X^6+X^5-X-I)\) yields
\[
 \|F_t(R)\|_{\rm op}
 \le\left(11+o(1)\right)\|R-R_*\|_{\rm op}.
\]
Combining this with (84.7) proves
\[
 \boxed{\displaystyle
 \liminf_{\substack{p\to\infty\\p\equiv2\ (3)}}
 \inf_{R_*\text{ physical HI at }p}
 \|R-R_*\|_{\rm op}\ge\frac{\sqrt2}{11}.}
 \tag{84.8}
\]
An empty infimum is interpreted as infinity. No HI nonexistence
claim is used to prove this lower bound.

`hi_alltop_operator_limit.py` checks (84.4), the determinant 3,
and exact integer character counts at primes 5,11,17,23. It checks
the transfer indexing, polynomial evaluation, and (84.6) against
direct dense matrices at 5 and 11. Larger FFT calculations through
509 measure the operator Q defect and sample the cubic polynomial
on normalized random vectors. For example, at 509 the measured Q
operator defect is about 0.1812, while the sampled normalized squared
Hilbert--Schmidt defect is 1.9807. The large-matrix quantities are
explicitly numerical estimates; the uniform conclusions are proved
above independently of those samples. The FFT implementation uses
arrays of size O(p^2), without storing a dense p-squared-square matrix.

The asymptotic quadratic approximation is therefore insufficient
for this proposed perturbative route. A construction must also
control the cubic operator defect, or use a substantially different
argument. **Infinitude remains unproved.**

---

# 85. A quantitative criterion for correcting approximate pentagons

Section 84 shows why an approximation must control the full operator
defect. This section supplies a sufficient correction criterion once
such control and a linear certificate are available. All constants
below are independent of the fusion rank. **The required linear
certificate and approximate associators have not been constructed for
unbounded HI orders. This section does not establish infinitude.**

## 85.1 Unitary data before imposing the pentagon

Fix a finite semisimple C*-category, a binary *-tensor bifunctor with
the desired fusion multiplicities, and a strict unit. Associativity
of the fusion ring makes the two triple-product functors isomorphic.
Choose arbitrary natural unitary maps
\[
 F_{a,b,c}:((a\otimes b)\otimes c)\longrightarrow
 a\otimes(b\otimes c),
\]
equal to the identity when an input is the unit. At this stage no
pentagon equation is assumed. On composite inputs these maps extend
by direct sums and the fixed fusion-space inclusions.

Use the maximum operator norm over simple-input, simple-output
matrix blocks. Tensoring an operator with an identity and extending
it to direct sums are contractions in this norm. A tangent vector
\(u\in X\) is a normalized natural skew-adjoint endomorphism of the
left-associated triple product, and the unitary update is
\(F\mapsto F\exp(u)\). Let \(\operatorname{dist}\) be the corresponding
maximum operator-norm length metric on this product of unitary groups.

For each quadruple, let \(P(F)\) be the holonomy of the usual pentagon,
starting at \((((ab)c)d)\), following the path of three associators,
and returning along the inverse of the path of two associators.
Thus \(P(F)\) is a product of five unitary factors. Define
\[
 r(F)=\frac{P(F)-P(F)^*}{2}\in Y,\qquad
 q(F)=\|P(F)-I\|,\qquad e(F)=\|r(F)\|.
 \tag{85.1}
\]
Here \(Y\) is the real space of normalized skew-adjoint quadruple
cochains. If \(q(F)<1\), spectral calculus gives
\[
 q(F)\le\frac2{\sqrt3}e(F),\qquad
 r(F)=0\ \Longrightarrow\ P(F)=I.
 \tag{85.2}
\]
Indeed, for a unitary eigenvalue \(e^{i\theta}\), the hypothesis
implies \(|\theta|<\pi/3\), and
\(|e^{i\theta}-1|/|\sin\theta|=1/|\cos(\theta/2)|\).
The condition on \(q\) is essential: the skew part alone would also
vanish at \(P=-I\).

Write
\[
 J_Fu=\left.\frac{d}{ds}r(F\exp(su))\right|_{s=0}.
\]
The product rule for five unitary factors gives
\[
 \begin{split}
 \|P(F)-P(G)\|&\le5\operatorname{dist}(F,G),\\
 \|J_F-J_G\|&\le25\operatorname{dist}(F,G),\\
 \|r(F\exp(u))-r(F)-J_Fu\|&\le\frac{25}{2}\|u\|^2.
 \end{split} \tag{85.3}
\]
For the second derivative there are 25 ordered choices of the two
differentiated factors, including coincident choices. Each term is
bounded by the product of the tangent norms. The same count bounds
the variation of the right-trivialized derivative \(J_F\). Taking a
skew part is contractive, so it does not enlarge these bounds.

## 85.2 An exact boundary relation and a quadratic compatibility bound

The five-object associahedron has 14 binary parenthesizations,
21 edges, six pentagonal faces, and three square faces. These counts
and the following relation are checked directly from binary trees
by `hi_pentagon_stability.py`; no pentagon relation is used in the
free-word check. The squares commute already by bifunctoriality and
naturality, even for the present arbitrary unitary \(F\).

Shelling the boundary gives an ordered product of conjugates of all
nine oriented face loops which freely reduces to the empty word.
Deleting the three identity square loops gives
\[
 U_1U_2\cdots U_6=I,
 \tag{85.4}
\]
where each \(U_i\) is a unitarily transported pentagon holonomy or
its inverse. All six pentagons occur exactly once. The saved
certificate records every edge, oriented face, and transport path,
so (85.4) is checkable in a free group, independently of matrix
arithmetic or categorical existence.

For completeness, the certificate uses the following six faces.
An interval denotes a fixed parenthesized block; its endpoints here
are positions among \(a,b,c,d,e\). The sign compares its orientation
with the standard three-edge-then-inverse-two-edge pentagon.

| Fixed block | Face ID | Sign | Transport length |
|---|---:|---:|---:|
| \((ab)\) | 0 | -1 | 2 |
| \((bc)\) | 1 | +1 | 6 |
| \((cd)\) | 2 | -1 | 2 |
| \((de)\) | 3 | +1 | 7 |
| \((abcd)\) | 7 | -1 | 7 |
| \((bcde)\) | 8 | +1 | 4 |

The pentagonal product order is \(8,1,7,3,2,0\), and all transports
are based at \(((ab)(c(de)))\). Their lengths sum to 28. Each path
edge applies one associator, possibly on composite objects.

For any quadruple cochain \(y\), apply the six corresponding
substitutions or exterior tensorings, transport to this common
five-object parenthesization, and sum with the displayed signs.
This defines a real-linear map \(B_F:Y\to Z\), where \(Z\) consists
of skew-adjoint five-object cochains. In particular,
\[
 B_Fr(F)=\sum_{i=1}^6\frac{U_i-U_i^*}{2},\qquad
 \|B_F\|\le6.
 \tag{85.5}
\]
If \(E_i=U_i-I\) and \(V_i=U_1\cdots U_i\), then (85.4) gives
\[
 0=\sum_{i=1}^6V_{i-1}E_i,\qquad
 \left\|\sum_{i=1}^6E_i\right\|
 \le\sum_{i=1}^6(i-1)q(F)^2=15q(F)^2.
\]
Here \(\|V_{i-1}-I\|\le(i-1)q(F)\) follows by telescoping products
of unitaries. Taking skew parts and using (85.2) proves the uniform
compatibility estimate
\[
 \boxed{\|B_Fr(F)\|\le20e(F)^2\quad(q(F)<1).}
 \tag{85.6}
\]
It is valid before imposing coherence. It does not assert that the
off-solution tangent maps form a complex.

For a transport containing \(m\) associators, changing \(F\) by
distance \(s\) changes its conjugation operator by at most \(2ms\).
The six fixed cochain substitutions have norm at most one.
The sum of path lengths in the exact certificate therefore gives
\[
 \boxed{\|B_F-B_G\|\le56\operatorname{dist}(F,G).}
 \tag{85.7}
\]

## 85.3 A correction test requiring only data at the trial point

Choose a trial \(F_0\) and real-linear maps
\[
 h:Y\to X,\qquad k:Z\to Y,
\]
with certified operator bounds \(\|h\|\le H\), \(\|k\|\le K\).
They must preserve the indicated skew-adjoint and unit-normalized
spaces. Define the single-point linear defect
\[
 \theta_0=\|I_Y-J_{F_0}h-kB_{F_0}\|.
 \tag{85.8}
\]
This is an induced operator norm, not a maximum matrix-entry error.
No exact solution is required to state or check this condition.

**Correction theorem.** Put \(q_0=q(F_0)\), \(e_0=e(F_0)\).
If some \(R>0\) satisfies
\[
 \begin{split}
 &q_0+5R<1,\\
 &\theta=\theta_0+(25H+56K)R,\qquad
   \beta=20K+\frac{25}{2}H^2,\\
 &\eta=\theta+\beta e_0<1,\qquad
   \frac{He_0}{1-\eta}<R,
 \end{split} \tag{85.9}
\]
then the iteration
\[
 F_{j+1}=F_j\exp\bigl(-h r(F_j)\bigr)
 \tag{85.10}
\]
converges to unitary, unit-normalized associators satisfying every
pentagon. Moreover
\[
 e(F_j)\le\eta^j e_0,\qquad
 \operatorname{dist}(F_\infty,F_0)\le\frac{He_0}{1-\eta}.
 \tag{85.11}
\]

To prove this, keep the same maps \(h,k\) throughout the iteration.
On the radius-\(R\) ball, (85.3) and (85.7) imply
\(\|I-J_Fh-kB_F\|\le\theta\), and (85.3) ensures \(q(F)<1\).
Writing \(u=-hr(F)\), the Taylor remainder and (85.6) give
\[
 \begin{split}
 e(F\exp(u))
 &\le\|(I-J_Fh-kB_F)r(F)\|
       +\|kB_Fr(F)\|+\frac{25}{2}\|u\|^2\\
 &\le\theta e(F)+\beta e(F)^2.
 \end{split}
\]
Induction gives the geometric error bound. The sum of update path
lengths is at most \(He_0/(1-\eta)<R\), keeping every step and its
interpolating path in the ball. The iterates are Cauchy, their limit
has zero skew residual, and (85.2) makes its pentagon holonomy the
identity. This proves the theorem without assuming nonemptiness of
the exact solution space.

One convenient set of sufficient constants is
\[
 \boxed{H,K\le1,\quad\theta_0\le\tfrac14,\quad
 q_0\le\tfrac12,\quad e_0\le\tfrac1{1000}.}
 \tag{85.12}
\]
Taking \(R=1/200\) gives \(\theta\le131/200\),
\(\beta\le65/2\), \(\eta\le11/16\), and displacement at most
\(2/625<1/200\). These rational inequalities are also checked
exactly in the script. No claim is made that present HI candidates
satisfy (85.12).

The theorem produces a coherent unitary monoidal structure with
the prescribed fusion multiplicities. To conclude fusion-category
existence, rigidity must also be ensured. One sufficient open
condition is nonvanishing of the unit-channel coefficients
\((F^{a,a^*,a}_a)_{1,1}\) for every simple \(a\), with their lower
bounds larger than the displacement in (85.11). The usual duality
construction for coherent unitary fusion data then applies; see
[Kitaev, Appendix E.2](https://arxiv.org/html/cond-mat/0506438).
This condition is not silently included in the numerical pentagon bounds.

## 85.4 Relation to categorical rigidity and the outstanding HI step

The norm-one maps needed in (85.12) have a concrete definition even
before coherence. Assume the based fusion rules give a dual label
\(a^*\) with a one-dimensional unit channel in \(a^*\otimes a\).
Use their positive Frobenius--Perron dimensions \(d_a\), and choose
an isometry \(i_a:1\to a^*\otimes a\). Put
\[
 R_a=\sqrt{d_a}\,i_a,\qquad
 V_{a,T}=F_{a^*,a,T}(R_a\otimes I_T).
\]
Strict unitality identifies the source of \(V_{a,T}\) with \(T\).
For every unitary trial \(F\), without any snake or pentagon
identity,
\[
 V_{a,T}^*V_{a,T}=d_aI_T,\qquad
 \mathcal T_{a,T}(L)=V_{a,T}^*(I_{a^*}\otimes L)V_{a,T}
 \tag{85.13}
\]
is a completely positive map on \(\operatorname{End}(a\otimes T)\)
with \(\mathcal T_{a,T}(I)=d_aI\) and norm \(d_a\).

For an m-cochain \(c\), take \(T\) to be the chosen product of its
last m-1 inputs. Fix a reassociation path giving a unitary
\(S:a\otimes T\to T_m(a,X_1,\ldots,X_{m-1})\), where \(T_m\)
is the cochain's specified parenthesization. Define
\[
 (\chi_{m,F}c)_{X_1,\ldots,X_{m-1}}
 =\frac1D\sum_a d_a\,
       \mathcal T_{a,T}\bigl(S^*c_{a,X_1,\ldots,X_{m-1}}S\bigr),
 \qquad D=\sum_a d_a^2.
 \tag{85.14}
\]
The value depends on the fixed paths away from coherence, but this
does not affect the following conclusions. Each summand preserves
adjoints, and the dimension weights make the whole map unital and
completely positive. Therefore \(\|\chi_{m,F}\|\le1\) for every
unitary trial \(F\). If \(c\) is unit-normalized, so is its image:
a unit among the remaining inputs makes each component of \(c\)
zero. All these assertions hold before proving rigidity.

Let \(N_Y\) discard the quadruple components with a unit input;
it is a norm-one projection. We may consequently take the specific
single-point maps
\[
 \boxed{h=\chi_{4,F_0},\qquad k=N_Y\chi_{5,F_0},\qquad H,K\le1,}
 \tag{85.15}
\]
where \(\chi_{5,F_0}\) starts from the five-object bracketing used
in (85.5). The map \(k\) is defined on all of \(Z\), since away
from coherence no normalization property of \(B_F\) was assumed.
Freeze the maps (85.15) during the correction iteration, as required
in the proof above. Thus finding abstract bounded linear maps is
not an additional construction problem: (85.13)--(85.15) give
candidates from the trial associators themselves. Their **homotopy
defect** in (85.8) still needs a bound.

At an existing unitary fusion category, the tangent complex has a
contracting homotopy given by dimension-weighted partial traces;
see [Bartlett, Section 6](https://arxiv.org/html/1502.02882#S6).
At that coherent point (85.14) is this categorical averaging map.
After the unitary identifications of the chosen parenthesizations,
the homotopy equation in degree four gives maps of the form \(h,k\)
in (85.8) with \(H,K\le1\) and \(\theta_0=0\).

That exact-category statement is not a bound at an arbitrary trial
point. The new criterion separates the issue: the explicit maps
(85.15) need a certified bound on (85.8), as well as a small
pentagon residual. A uniform estimate on this off-solution homotopy
defect has not been established here. In particular,
neither the handleslide identity nor \(d^2=0\) is assumed away from
coherence. The directly proved replacement used above is (85.6).

There is one scale issue when applying the theorem to HI categories.
Their noninvertible unit-channel entries have magnitude \(1/d\),
which tends to zero with the order. A fixed error threshold alone
does not guarantee the open rigidity condition at unbounded n.
For example, if the trial unit-channel magnitudes are at least
\(1/d\), the strengthened hypotheses
\[
 \theta_0\le\frac14,\quad q_0\le\frac12,\quad
 e_0\le\min\left\{\frac1{1000},\frac1{4d}\right\}
 \tag{85.16}
\]
with the maps (85.15) suffice for a unitary HI categorification.
Indeed, the proof of (85.12) bounds the actual displacement by
\((16/5)e_0\le4/(5d)<1/d\), so every required coefficient remains
nonzero. This is a sufficient order-dependent accuracy target,
not a lower bound on all possible correction methods.

For an infinitude proof by this route, it would suffice to construct
unitary trial associators and their linear certificates satisfying
(85.9), with the rigidity condition, at unbounded odd HI orders.
This would avoid having to evaluate every pentagon exactly in the
initial formula. Section 84 excludes one proposed vanishing-operator
approximation; the real negative-dimension double-sine candidate is
not directly an input to this unitary theorem. Neither supplies
the missing family of certificates.

The reproducible script verifies the free-word boundary relation,
the six canonical face transports and total length 28, and the
rational correction constants. Independent small noncommuting
unitary matrices with exactly imposed square relations check the
quadratic norm bounds and the five-factor derivative bound. Those
matrix regressions are numerical checks of the proved estimates,
not HI existence certificates. The calculation uses negligible
memory relative to the user's half-system-memory threshold.
**Infinitude remains unproved.**

---

# 86. A quantitative handleslide before coherence

The main nonformal step in the contracting homotopy of Section 85
is a dimension-weighted partial-trace identity, often drawn as a
handleslide. This section proves an error bound for that identity
without assuming the pentagon or an existing category. It applies
to the multiplicity-free HI fusion rules. It also gives exact
finite combinatorial certificates for comparing reassociation paths.
These results do not construct an unbounded family of associators.
**Infinitude remains unproved.**

## 86.1 Two unital completely positive maps

Use the unitary trial data of Section 85 and suppose the based
fusion rules are multiplicity-free. Write \(d_a\) for their positive
Frobenius--Perron dimensions and \(D=\sum_a d_a^2\).
Choose isometries
\[
 i_{ab}^z:z\to a\otimes b\quad(N_{ab}^z=1),\qquad
 R_a=\sqrt{d_a}\,i_{a^*a}^1.
\]
Let \(\mathcal T_{a,T}\) be the partial-trace map (85.13).
For an arbitrary object \(T\), take a family
\(c=(c_z)_z\), \(c_z\in\operatorname{End}(z\otimes T)\),
with norm \(\|c\|=\max_z\|c_z\|\). Define
\[
 C_{ab}(c)=\sum_{z:N_{ab}^z=1}
 (i_{ab}^z\otimes I_T)c_z(i_{ab}^{z*}\otimes I_T).
\]
For a simple \(b\), the two handle maps are
\[
 \begin{split}
 L_{b,T}(c)
 &=\frac1D\sum_a d_a\,
 \mathcal T_{a,b\otimes T}
       \bigl(F_{a,b,T}C_{ab}(c)F_{a,b,T}^*\bigr),\\
 R_{b,T}(c)
 &=I_b\otimes\left(\frac1D\sum_zd_z\mathcal T_{z,T}(c_z)\right).
 \end{split} \tag{86.1}
\]
Both maps are unital and completely positive before coherence:
the extensions \(C_{ab}\) are unital *-homomorphisms, each partial
trace sends the identity to \(d_aI\), and the total weights are
\(D^{-1}\sum_a d_a^2=1\). The norm bound below is in completely
bounded norm, so it also controls matrix amplifications and
arbitrary multiplicity spaces inside \(T\).

Let \(q\) be the maximum pentagon operator defect on simple
quadruples, equivalently the maximum difference of the two unitary
paths around a pentagon. Naturality and direct sums give the same
bound when any input is a composite object, including \(T\).

## 86.2 Reducing each map using one pentagon

The actual Kraus maps for \(L\) can be written as
\[
 K^L_{az}=(I_{a^*}\otimes(i_{ab}^{z*}\otimes I_T))
       (I_{a^*}\otimes F_{a,b,T}^*)V_{a,b\otimes T},
 \tag{86.2}
\]
where \(V\) is (85.13). Set
\[
 \begin{split}
 j_{azb}&=(I_{a^*}\otimes i_{ab}^{z*})
         F_{a^*,a,b}(R_a\otimes I_b):b\to a^*\otimes z,\\
 \widetilde K^L_{az}&=F_{a^*,z,T}(j_{azb}\otimes I_T).
 \end{split} \tag{86.3}
\]
The pentagon on \((a^*,a,b,T)\), applied to the cup \(R_a\),
compares (86.2) and (86.3). Indeed, the relation being approximated is
\[
 (I_{a^*}\otimes F_{a,b,T}^*)F_{a^*,a,b\otimes T}
 =F_{a^*,a\otimes b,T}(F_{a^*,a,b}\otimes I_T)
       F_{a^*\otimes a,b,T}^*.
\]
The difference of these two paths has norm at most \(q\).
Naturality moves the last associator across \(R_a\), where strict
unitality removes it. Naturality also moves the projection onto
\(z\) across the first associator. Orthogonality of those projections
then gives the operator inequality
\[
 \sum_z(K^L_{az}-\widetilde K^L_{az})^*
        (K^L_{az}-\widetilde K^L_{az})\le d_aq^2I.
 \tag{86.4}
\]
This controls the complete family, without summing separate scalar
norm bounds over the labels \(z\).

For the other side choose
\(\ell_{bz^*}^{a^*}:a^*\to b\otimes z^*\). Frobenius reciprocity
of the based fusion rules identifies its allowed labels with
\(N_{ab}^z=1\). Define
\[
 \begin{split}
 K^R_{az}&=((\ell_{bz^*}^{a^*})^*\otimes I_{z\otimes T})
       F_{b,z^*,z\otimes T}^*(I_b\otimes V_{z,T}),\\
 s_{azb}&=((\ell_{bz^*}^{a^*})^*\otimes I_z)
       F_{b,z^*,z}^*(I_b\otimes R_z):b\to a^*\otimes z,\\
 \widetilde K^R_{az}&=F_{a^*,z,T}(s_{azb}\otimes I_T).
 \end{split} \tag{86.5}
\]
The actual Kraus expression for \(R\) follows by inserting the resolution of the
identity on \(b\otimes z^*\). The pentagon on \((b,z^*,z,T)\)
and naturality give
\[
 \sum_a(K^R_{az}-\widetilde K^R_{az})^*
        (K^R_{az}-\widetilde K^R_{az})\le d_zq^2I.
 \tag{86.6}
\]

Stack the left Kraus maps with weights \(\sqrt{d_a/D}\), and the
right ones with weights \(\sqrt{d_z/D}\). Each actual and reduced
stack is an isometry. Equations (86.4) and (86.6) bound the norm
difference of the corresponding stacks by \(q\). For isometries
\(U,V\) in the same representation,
\[
 \|U^*\pi(c)U-V^*\pi(c)V\|\le2\|U-V\|\,\|c\|.
\]
This inequality holds at every matrix amplification. Consequently,
if \(\widetilde L,\widetilde R\) use the reduced Kraus maps,
\[
 \boxed{\|L-\widetilde L\|_{\rm cb}\le2q,\qquad
        \|R-\widetilde R\|_{\rm cb}\le2q.}
 \tag{86.7}
\]
No snake identity, exact pentagon, or dimension-dependent factor
was used in these estimates.

## 86.3 A scalar balance condition and the uniform handle bound

Because \(\operatorname{Hom}(b,a^*\otimes z)\) is one-dimensional,
the two maps \(j_{azb}\) and \(s_{azb}\) are scalar multiples of the
same isometry. Let matrix rows index the right intermediate channel
and columns the left intermediate channel. Their squared magnitudes are
\[
 \|j_{azb}\|^2=d_a\left|[F^{a^*,a,b}_b]_{z,1}\right|^2,
 \qquad
 \|s_{azb}\|^2=d_z\left|[F^{b,z^*,z}_b]_{1,a^*}\right|^2.
\]
Thus the two reduced channels use the same unital completely
positive compression maps, with possibly different scalar weights.
Define
\[
 \mu_b=\frac1D\sum_{a,z:N_{ab}^z=1}
 \left|d_a^2\left|[F^{a^*,a,b}_b]_{z,1}\right|^2
       -d_z^2\left|[F^{b,z^*,z}_b]_{1,a^*}\right|^2\right|.
 \tag{86.8}
\]
Each set of nonnegative weights sums to one, so \(0\le\mu_b\le2\).
The triangle inequality applied to those common compression maps
gives \(\|\widetilde L-\widetilde R\|_{\rm cb}\le\mu_b\).
Together with (86.7), this proves
\[
 \boxed{\|L_{b,T}-R_{b,T}\|_{\rm cb}\le4q+\mu_b.}
 \tag{86.9}
\]
The bound is independent of the number of simples, their dimensions,
and the object \(T\).

In particular, the standard unit-channel magnitudes
\[
 \left|[F^{a^*,a,b}_b]_{z,1}\right|^2=\frac{d_z}{d_ad_b},
 \qquad
 \left|[F^{b,z^*,z}_b]_{1,a^*}\right|^2=\frac{d_a}{d_bd_z}
 \tag{86.10}
\]
make both weights equal to \(d_ad_z/(Dd_b)\), hence \(\mu_b=0\).
No phase matching is necessary. For HI these prescribed magnitudes
are precisely \(1\), \(1/d\), and \(1/\sqrt d\), according to
the input and intermediate dimensions. They concern the rows or
columns with a unit intermediate channel, whose values are already
fixed in the usual unitary normalization. A trial construction
retaining those magnitudes therefore satisfies the \(4q\) bound
regardless of its remaining associator entries.

`hi_unitary_handle_bound.py` implements the binary tensor functor,
associators on arbitrary direct sums, and all four handle channels
for the Fibonacci fusion rule. It deliberately varies unitary
associators without imposing the pentagon. The balanced trials
change phases while retaining (86.10); the unbalanced trials vary
the unit-channel magnitudes as well. Tests include objects with
several copies of both simple labels. Every channel remains unital,
and the two \(2q\) comparisons, the \(\mu_b\) comparison, and the
combined bound pass. At a balanced trial with \(q\approx0.14256\),
for example, the sampled handle defect is approximately 0.01414.
These are numerical regressions of the uniform proof, not estimates
of completely bounded norms and not new HI existence certificates.

## 86.4 Exact certificates for the remaining reassociation estimates

For \(m=4,5,6,7\) tensor factors, `hi_associahedron_path_bound.py`
constructs the complete rotation graph of binary trees and its
square and pentagonal two-faces. It chooses a spanning tree and
assigns cost zero to its edges. It then repeatedly uses a two-face
with just one edge whose cost is not yet known, assigning
\[
 \text{cost(new edge)}=
 \begin{cases}0&\text{square},\\1&\text{pentagon}\end{cases}
 +\sum_{\text{other edges in the face}}\text{cost(edge)}.
 \tag{86.11}
\]
In each of these four finite graphs every edge is eventually
assigned a cost at most one. The exact results are:

| Tensor factors | Vertices | Edges | Two-faces | Non-tree eliminations | Maximum cost |
|---:|---:|---:|---:|---:|---:|
| 4 | 5 | 5 | 1 | 1 | 1 |
| 5 | 14 | 21 | 9 | 8 | 1 |
| 6 | 42 | 84 | 56 | 43 | 1 |
| 7 | 132 | 330 | 300 | 199 | 1 |

The saved JSON certificates include every edge, oriented face,
spanning-tree edge, and elimination step. Their replay checks
the full rotation graph, verifies each face using its common
parenthesized intervals, checks that the tree spans, and then
checks every integer cost equation. No numerical matrix computation
or HI solution enters these certificates.

They have the following uniform operator consequence. Transport
along the spanning tree to identify all vertex Hilbert spaces.
The tree edges become identities. A square has zero holonomy
defect; a pentagon has defect at most \(q\). Solving its unitary
product for one edge and telescoping the remaining factors proves
inductively that every gauged edge has defect at most its cost
times \(q\), hence at most \(q\). Therefore two reassociation paths
\(p_1,p_2\) with the same endpoints satisfy
\[
 \boxed{\|U(p_1)-U(p_2)\|\le
          (\operatorname{length}(p_1)+\operatorname{length}(p_2))q,
          \quad m\le7.}
 \tag{86.12}
\]
For fewer than four factors the comparison is exact. The parameter
\(m\) here counts tensor factors, not the order of an HI group.
The conclusion is valid for arbitrary object labels and arbitrary
fusion rank at each of these fixed values of \(m\).

The maps in the Section-85 homotopy test involve only a fixed number
of object positions. Equations (86.9) and (86.12) supply bounds for
the handle comparison and reassociation comparisons, respectively.
Section 87 completes the full estimate using right-associated
cochains, where the middle cancellations become exact and the
remaining transport costs can be counted. An unbounded HI family
with sufficiently small full pentagon defect is still needed.
**Infinitude remains unproved.**

---

# 87. Small pentagon error now suffices under unit-channel balance

The separate linear certificate in Section 85 can be removed for
multiplicity-free unitary trial data. Using right-associated tensor
products makes the middle coface cancellations exact. The two
remaining comparisons are controlled by Section 86 and one additional
pentagon. The resulting iteration has explicit constants independent
of fusion rank.

In particular, a unitary trial for the cyclic HI rules, with standard
unit-channel magnitudes and full pentagon error
\[
 q\le\min\{1/130,\,1/(4d)\},
 \tag{87.1}
\]
implies a unitary HI category of that order. This is an unconditional
sufficient criterion, with a constructive proof below. **No such
family of trials has been constructed at unbounded orders. Infinitude
is still unproved.**

## 87.1 Right-associated cochains

For this section write
\[
 T_m(X_1,\ldots,X_m)=X_1\otimes
       (X_2\otimes(\cdots\otimes X_m)),
\]
and use cochains in \(\operatorname{End}(T_m)\), with maximum block
operator norm. This changes the parenthesization convention of
Section 85. A tangent vector is now a skew-adjoint **output**
endomorphism of \(F\), so its unitary update is \(\exp(u)F\).

Define cofaces \(f_i^m:C^m\to C^{m+1}\) as follows:

- \(f_0^mc=I_{X_1}\otimes c_{X_2,\ldots,X_{m+1}}\).
- For \(1\le i\le m\), evaluate \(c\) with inputs \(X_i,X_{i+1}\)
  merged, and conjugate to the fully right-associated product. If
  \(i<m\), this uses the single associator
  \(F_{X_i,X_{i+1},T_{m-i}(X_{i+2},\ldots,X_{m+1})}\), tensored
  with the preceding identities. For \(i=m\) no associator is needed.
- \(f_{m+1}^mc\) is \(c\otimes I_{X_{m+1}}\), conjugated by the
  successive right reassociations which append the last object.

Put \(\partial_m=\sum_{i=0}^{m+1}(-1)^if_i^m\). These maps are
defined before coherence; no assertion that \(\partial^2=0\) is made.
The signed sums preserve unit normalization already from strict
unitality. Each individual coface is a contraction.

Because the first tensor factor is separated in \(T_m\), the
averaging map requires no preliminary reassociation:
\[
 (\chi_mc)_{X_1,\ldots,X_{m-1}}
 =\frac1D\sum_a d_a\,
       \mathcal T_{a,T_{m-1}(X_1,\ldots,X_{m-1})}
       (c_{a,X_1,\ldots,X_{m-1}}).
 \tag{87.2}
\]
It has norm at most one, preserves adjoints, and preserves unit
normalization, just as in (85.14).

The partial trace is natural under every map of the object being
traced past. More precisely, for a unitary \(U:T\to T'\),
\[
 \mathcal T_{a,T'}((I_a\otimes U)c(I_a\otimes U^*))
       =U\mathcal T_{a,T}(c)U^*.
 \tag{87.3}
\]
This follows directly from naturality of \(F\) in the compression
formula (85.13), without the pentagon. Consequently
\[
 \chi_{m+1}f_0^m=I,\qquad
 \chi_{m+1}f_i^m=f_{i-1}^{m-1}\chi_m\quad(2\le i\le m)
 \tag{87.4}
\]
hold **exactly** at arbitrary unitary trials.

For \(i=1\), the difference is precisely the handle comparison
(86.1), applied with \(T\) the product of the remaining objects.
Writing \(\mu=\max_b\mu_b\) from (86.8),
\[
 \|\chi_{m+1}f_1^m-f_0^{m-1}\chi_m\|\le4q+\mu.
 \tag{87.5}
\]

Only the exterior right coface is left. For arbitrary objects \(T,Y\)
and \(c\in\operatorname{End}(a\otimes T)\), the required comparison
before averaging is
\[
 \mathcal T_{a,T\otimes Y}
       (F_{a,T,Y}(c\otimes I_Y)F_{a,T,Y}^*)
 \quad\hbox{versus}\quad
       \mathcal T_{a,T}(c)\otimes I_Y.
\]
Its first compression map is
\((I_{a^*}\otimes F_{a,T,Y}^*)V_{a,T\otimes Y}\).
The pentagon on \((a^*,a,T,Y)\), followed by naturality at the cup,
puts this within \(\sqrt{d_a}q\) of
\(F_{a^*,a\otimes T,Y}(V_{a,T}\otimes I_Y)\).
Both compression maps have norm \(\sqrt{d_a}\).
Naturality moves \(c\) through the latter associator, giving the
second expression. Their difference is therefore at most
\(2d_aq\|c\|\). Averaging with weights \(d_a/D\), and using (87.3)
for the other right reassociations, proves
\[
 \|\chi_{m+1}f_{m+1}^m-f_m^{m-1}\chi_m\|\le2q.
 \tag{87.6}
\]

In degree four, the three middle cancellations are (87.4), the
left boundary is (87.5), and the right boundary is (87.6). Hence
\[
 \boxed{\|I-\partial_3\chi_4-\chi_5\partial_4\|
       \le6q+\mu.}
 \tag{87.7}
\]
This is the desired uniform off-solution homotopy estimate in the
right-associated convention.

## 87.2 Derivative and compatibility estimates in the same convention

Let \(A\) and \(B\) be respectively the three-edge and two-edge
unitary paths from \((((ab)c)d)\) to \(a(b(cd))\). Take the
pentagon holonomy based at the right-associated object:
\[
 P=AB^*,\qquad r=(P-P^*)/2,\qquad
 q=\|P-I\|,\quad e=\|r\|.
 \tag{87.8}
\]
These norms agree with the previous convention, since the two
holonomies are unitarily conjugate. Under the update \(\exp(u)F\),
direct differentiation gives
\[
 dP=Z_+(u)P-PZ_-(u),\qquad
 Z_+=f_0^3+f_2^3+f_4^3,\quad Z_-=f_1^3+f_3^3.
\]
Taking skew parts and comparing with \(\partial_3u=Z_+(u)-Z_-(u)\)
proves
\[
 \boxed{\|J_F-\partial_3\|\le5q,\qquad
 J_Fu=\left.\frac{d}{ds}r(\exp(su)F)\right|_{s=0}.}
 \tag{87.9}
\]
The five-factor Taylor remainder is still at most
\((25/2)\|u\|^2\), as in (85.3).

The degree-four compatibility bound must use the same cofaces.
Transport the six-pentagon boundary certificate of Section 85 to
the right-associated five-object base. Let \(\widehat B_F\) be its
signed sum of transported quadruple cochains, now right-associated.
The same telescoping proof gives
\[
 \|\widehat B_Fr\|\le15q^2.
\]
The transports defining \(\widehat B_F\) and those defining
\(\partial_4\) have the same endpoints for each face. The cost
certificates in Section 86 give the following exact comparison:

| Fixed block | Face ID | Cost of the transport-comparison loop |
|---|---:|---:|
| \((ab)\) | 0 | 0 |
| \((bc)\) | 1 | 1 |
| \((cd)\) | 2 | 0 |
| \((de)\) | 3 | 2 |
| \((abcd)\) | 7 | 2 |
| \((bcde)\) | 8 | 0 |

Here the cost is the sum of the gauged-edge costs of (86.11) along
the reduced comparison loop; the total is 5. Comparing conjugations
multiplies the transport norm bound by at most two. Therefore
\[
 \|\widehat B_F-\partial_4\|\le10q,\qquad
 \boxed{\|\partial_4r\|\le15q^2+10qe.}
 \tag{87.10}
\]
`hi_right_pentagon_correction.py` checks all six loop comparisons
as exact free words. It also replays the spanning-tree cost
certificate. In the edge numbering of Section 85, the standard
right-coface transports for faces \(0,1,2,3,7,8\) are respectively
\((3),(2),(1),(),(1,4,9),()\). Their endpoints and orientations
are checked against the right-based pentagon on each face.

## 87.3 A uniform correction iteration

At the current trial recompute \(\chi_4\) by (87.2) and set
\[
 \boxed{F_{j+1}=\exp(-\chi_{4,F_j}r(F_j))F_j.}
 \tag{87.11}
\]
Every update remains unitary and unit-normalized, and its path
length is at most \(e(F_j)\). Combining (87.7), (87.9), (87.10),
and the Taylor remainder gives, whenever \(q(F)<1\),
\[
 \begin{split}
 e(F_{\rm new})
 &\le\mu(F)e+21qe+15q^2+\frac{25}{2}e^2\\
 &\le\boxed{\mu(F)e+57e^2}.
 \end{split} \tag{87.12}
\]
For the last inequality use \(q^2\le(4/3)e^2\) from (85.2), and
\(q\le(7/6)e\), since \(2/\sqrt3<7/6\). The resulting coefficient
is exactly \(15(4/3)+21(7/6)+25/2=57\).

The correction need not preserve exact unit-channel balance, but
its drift has a uniform bound:
\[
 \boxed{|\mu(F)-\mu(G)|\le4\operatorname{dist}(F,G).}
 \tag{87.13}
\]
To see this, regard the two sets of weights in (86.8) as probability
distributions on pairs \((a,z)\). For fixed \(a\), the first is the
squared modulus distribution of a unit column of \(F\), with weight
\(d_a^2/D\); for fixed \(z\), the second comes from a unit row, with
weight \(d_z^2/D\). For unit vectors \(v,w\),
\[
 \sum_i\bigl||v_i|^2-|w_i|^2\bigr|\le2\|v-w\|_2.
\]
Thus each distribution changes by at most twice the associator
distance. Their difference changes by at most four times that
distance, including after the maximum over \(b\).

**Uniform correction theorem.** If a multiplicity-free unitary
trial satisfies
\[
 \boxed{\mu_0+65e_0\le\frac12,\qquad q_0+10e_0<1,}
 \tag{87.14}
\]
then (87.11) converges to exact unitary, unit-normalized associators
with the same fusion multiplicities. Its error and displacement obey
\[
 e(F_j)\le2^{-j}e_0,\qquad
 \operatorname{dist}(F_\infty,F_0)\le2e_0.
 \tag{87.15}
\]

Indeed, as long as the total displacement is at most \(2e_0\),
pentagon Lipschitz continuity gives \(q(F_j)\le q_0+10e_0<1\),
while (87.13) gives \(\mu(F_j)\le\mu_0+8e_0\). Equation (87.12)
therefore halves each residual, since \(8+57=65\). The summed
update lengths are bounded by \(\sum_j2^{-j}e_0=2e_0\), closing
the induction. Completeness of the finite product of unitary
groups gives a limit. Its skew residual vanishes, and its pentagon
holonomies stay within distance less than one of the identity;
therefore those holonomies are the identity. No exact solution
was assumed in this proof.

For balanced trial data, \(\mu_0=0\) and \(q_0\le1/130\) are
sufficient: \(e_0\le q_0\), so both inequalities in (87.14) hold.
To obtain a fusion category, each required unit-channel coefficient
must also survive. A lower bound strictly greater than \(2e_0\)
suffices, by (87.15) and the duality criterion in Section 85.

For the HI rules, standard unit-channel magnitudes give \(\mu_0=0\)
and every duality coefficient has magnitude at least \(1/d\).
If (87.1) holds, then
\[
 2e_0\le2q_0\le\frac1{2d}<\frac1d,
\]
so all those coefficients remain nonzero. This proves the claimed
HI existence criterion. In particular, an unbounded odd-order
family of balanced unitary trial associators with
\(q_n=o(1/n)\) would establish infinitude. The theorem requires
the full maximum operator defect, not entrywise errors or sampled
pentagon tests.

The rigidity condition has not been replaced by a general automatic
rigidity assertion. The recent theorem of
[Etingof--Penneys](https://doi.org/10.1017/fmp.2025.10020), Theorem 1.1,
assumes braiding; their Question 3.1 concerns extending automatic
rigidity to finite semisimple weakly rigid categories without that
assumption. The HI fusion ring is noncommutative for odd n greater
than one, so that braided theorem does not apply directly here.

## 87.4 Verification and the remaining construction

The script verifies the integer transport costs and rational
constants exactly. It independently implements right-associated
cofaces on normalized Fibonacci cochains and tests (87.7), (87.9),
and (87.10) at deliberately incoherent unitary trials. The exact
middle cancellations and the separate handle and boundary estimates
are checked individually as well. The derivative
is also compared to a direct perturbation of the associator
matrices. At a balanced trial, the iteration reduces the measured
pentagon norm from approximately \(1.5072\times10^{-3}\) to
\(2.3171\times10^{-8}\), then to floating-point precision, while
the accumulated update length stays below \(5.099\times10^{-4}\).
The finite example checks formulas and convergence behavior;
it does not supply a new HI order or certify an infinite family.

The linear-estimate gap left by Sections 85--86 is now resolved in
this right-associated formulation. The remaining issue is the
construction of unitary HI trial associators meeting (87.1) for
unbounded n. Neither the Alltop approximation of Section 84 nor
the negative-dimension double-sine candidate has been shown to
meet these hypotheses. **Infinitude remains unproved.**

---

# 88. An exact reduced associator and a uniform obstruction to extending it

The correction theorem suggests first constructing associators after
omitting the invertible channels in a product of two noninvertibles.
That reduced problem has an elementary solution for every n. However,
the missing channels impose pentagons which stay far from satisfied
under the most direct unitary extension. The obstruction is independent
of the augmented blocks and survives arbitrary choices of phases.

## 88.1 Exact associators for the reduced rules

Keep the HI rules involving an invertible object, and replace only
the last fusion rule by
\[
 \rho_a\rho_b=\bigoplus_{c\in\mathbb Z_n}\rho_c.
 \tag{88.1}
\]
These are associative multiplicities with positive dimension function
\(d_{\alpha_a}=1\), \(d_{\rho_a}=n\). Their semisimple category
of graded vector spaces has the following unitary associator. Every
block with fewer than three noninvertible inputs is the scalar 1 on
its unique admissible channel. For three noninvertible inputs and
output \(\rho_o\), send the left intermediate label x to
\[
 \boxed{F^{\rho_a,\rho_b,\rho_c}_{\rho_o}:\quad
           x\longmapsto b+o-x.}
 \tag{88.2}
\]
All labels are taken modulo n. Each block is a permutation matrix,
and the unit \(\alpha_0\) is strict.

For four noninvertible inputs, let x label the first product and y
the first triple product. Along the three-edge pentagon path the
successive new labels are
\[
 u=b+y-x,\qquad v=u+o-y=b+o-x,\qquad
 w=c+v-u=c+o-y.
\]
Along the two-edge path they are
\[
 s=c+o-y,\qquad t=b+o-x.
\]
Thus the final pairs \((w,v)\) and \((s,t)\) agree. If an input
is invertible, substitute its forced intermediate label using
\(\alpha_g\rho_a=\rho_{g+a}\) and
\(\rho_a\alpha_g=\rho_{a-g}\); the same two final labels agree.
The script below verifies all 16 input-type patterns symbolically
over the integers, with every free fusion label left as a variable.
Consequently the verification applies to every cyclic order.

This is a finite semisimple unitary monoidal category, but it is
not rigid: no product involving a noninvertible simple has a unit
summand. It therefore does not establish an HI existence result.

There is also a useful uniqueness statement. Suppose the permutation
in a reduced three-noninvertible block is affine,
\[
 f(a,b,c,o,x)=Aa+Bb+Cc+Do+Ex+K,
 \qquad E\in(\mathbb Z/n\mathbb Z)^\times.
 \tag{88.3}
\]
Write the two pentagon final labels as
\[
\begin{split}
 u&=f(a,b,c,y,x),&v&=f(a,u,d,o,y),&w&=f(b,c,d,v,u),\\
 s&=f(x,c,d,o,y),&t&=f(a,b,s,o,x).
\end{split}
\]
Coefficient comparison in \(v-t=w-s=0\) gives \(CD=0\)
and \(BCD+CE=0\). Hence \(CE=0\), so C=0. Further coefficients
then give, in order,
\[
 E(B-1)=0,\quad AB=0,\quad D+E=0,\quad
 D^2-D=0,\quad (B-C)K=0.
\]
Canceling the unit E yields
\[
 (A,B,C,D,E,K)=(0,1,0,1,-1,0).
 \tag{88.4}
\]
This proof works over composite cyclic orders as well as prime
orders; it does not divide by a possibly nonunit coefficient.
Thus (88.2) is the unique invertible affine permutation formula.
Allowing scalar phases on its entries does not change the necessary
permutation identities.

**In fact, the affine assumption can be removed at every odd n.**
Suppose each reduced associator is monomial: a permutation matrix
with unit-modulus entries. Let \(f(a,b,c,o,x)\) be its right
intermediate label on a left channel x. The four pentagons with
exactly one invertible input force
\[
\begin{split}
 f(a+g,b,c,o+g,x+g)&=f(a,b,c,o,x),\\
 f(a,b+g,c,o,x)&=g+f(a-g,b,c,o,x),\\
 f(a,b,c+g,o,x)&=f(a,b-g,c,o,x-g),\\
 f(a,b,c-g,o,x)&=f(a,b,c,o+g,x)-g.
\end{split}
 \tag{88.4a}
\]
Their one-dimensional phases do not affect these support equations.
Set \(\varphi(o,x)=f(0,0,0,o,x)\). The first three identities give
\[
 f(a,b,c,o,x)
 =b-c+\varphi(o-a+b-c,\,x-a+b-2c).
\]
The last identity then gives
\(\varphi(k,x+2g)=\varphi(k,x)-2g\). Since n is odd,
multiplication by 2 is surjective. Hence for some function
\(h:\mathbb Z_n\to\mathbb Z_n\),
\[
 f(a,b,c,o,x)=a+c-x+h(o-a+b-c).
 \tag{88.4b}
\]

Now take all four inputs to be \(\rho_0\). Equality of the
first final labels in the pentagon, with \(z=o-x\), requires
\[
 \boxed{h\bigl(h(z+h(y))-y\bigr)=h(z)+h(y)-y}
 \qquad (y,z\in\mathbb Z_n).
 \tag{88.4c}
\]
This finite functional equation already forces h to be the identity.
To prove it, let H be the image of h. As z varies, (88.4c) gives
\[
 h(H-y)=H+h(y)-y\ \subseteq H.
\]
The translated set on the right has cardinality \(|H|\), so it
equals H. Thus H is invariant under translation by \(h(y)-y\)
for every y. Since \(h(y)\in H\), translating backwards shows
\(y\in H\). Consequently H is the whole group and h is bijective.
Choose \(y_0\) with \(h(y_0)=0\). Equation (88.4c) reduces to
\[
 h(h(z)-y_0)=h(z)-y_0.
\]
Surjectivity now proves \(h(u)=u\) for every u. This image-set
argument works for any finite abelian group; the odd-order assumption
was needed earlier to obtain (88.4b).

Substituting h into (88.4b) gives (88.2). Therefore every monomial
solution of the reduced odd cyclic rules has the same permutation
support. Nonlinear choices of the intermediate-label permutations
do not yield additional reduced constructions.

## 88.2 Explicit balanced unitary HI trials

Restore the full HI fusion multiplicities and set
\[
 d=\frac{n+\sqrt{n^2+4}}2,\qquad t=1/d,\qquad s=1/\sqrt d.
\]
Set every one-dimensional associator block to 1. For three
noninvertible inputs and output \(\rho_o\), define
\[
 (P_{b+o})_{y,x}=\mathbf1_{y=b+o-x}.
\]
If \(o\ne a-b+c\), use the n-by-n block \(P_{b+o}\).
If \(o=a-b+c\), there is an extra invertible channel on both
sides. Order it first and use
\[
 \boxed{\begin{pmatrix}
 t&s\mathbf1^T\\
 s\mathbf1&P_{b+o}-\dfrac{1+t}{n}\mathbf1\mathbf1^T
 \end{pmatrix}.}
 \tag{88.5}
\]
Here \(\mathbf1\) is the length-n all-ones vector.

This matrix is unitary. On the orthogonal complement of
\(\mathbf1\), it is the orthogonal permutation \(P_{b+o}\).
On the span of the extra channel and \(\mathbf1/\sqrt n\), it is
\[
 \begin{pmatrix}t&\sqrt n\,s\\\sqrt n\,s&-t\end{pmatrix},
 \qquad t^2+ns^2=1.
\]
All other blocks are unitary as well. The prescribed unit-channel
magnitudes are exactly \(1\), \(1/d\), and \(1/\sqrt d\),
so the imbalance in (86.8) vanishes. At n=1 this construction is
the standard Fibonacci associator.

Thus unitarity and balance can both be satisfied uniformly by an
explicit formula. The following pentagon prevents applying
Section 87 at any odd n greater than one.

## 88.3 A pentagon which augmented blocks and phases cannot repair

Take four inputs \(\rho_0\) and output \(\alpha_k\), k nonzero.
Every left fusion path has intermediate labels
\((\rho_x,\rho_k)\), x arbitrary. Every right fusion path has
labels \((\rho_z,\rho_{-k})\), z arbitrary. The three-edge
path uses (88.2) twice, with intermediate label \(k-x\), so
\[
 L:e_x\longmapsto e_{x-2k}.
\]
The two-edge path uses only one-dimensional blocks and gives
\[
 S:e_x\longmapsto e_{x-k}.
 \tag{88.6}
\]
Neither path uses an augmented block: the two n-by-n blocks have
outputs \(\rho_k\) and \(\rho_{-k}\), both nonexceptional.
Consequently any change to (88.5) leaves (88.6) unchanged.

If k has odd order r, the relative permutation \(S^*L\) is a
union of r-cycles. Its spectrum consists of r-th roots of unity,
and therefore
\[
 \boxed{\|L-S\|=2\cos\!\left(\frac{\pi}{2r}\right).}
 \tag{88.7}
\]
In particular, choose a generator k to obtain
\[
 q\ge2\cos\!\left(\frac{\pi}{2n}\right)\longrightarrow2.
 \tag{88.8}
\]
This is a full block operator norm, not a sampled entrywise error.

Even arbitrary phases on the one-dimensional blocks and the
nonzero entries of the nonexceptional permutation blocks cannot
lower (88.7). The relative operator becomes a weighted r-cycle.
If the product of its weights is \(e^{i\theta}\), its r
eigenvalues are the equally spaced roots of \(z^r=e^{i\theta}\).
At least one lies within angular distance \(\pi/r\) of -1,
so its distance from 1 is at least \(2\cos(\pi/(2r))\).
This argument needs only unitarity and the retained permutation
supports. The augmented blocks can be arbitrary unitary matrices.

More generally, if \(\eta\) is the maximum block operator
distance from any such trial to any exact unitary HI associator
in the same fusion bases, telescoping the five unitary factors
around this pentagon gives
\[
 \eta\ge\frac25\cos\!\left(\frac{\pi}{2n}\right).
 \tag{88.9}
\]
Thus a perturbation whose operator norm tends to zero cannot repair
this family. The error is already forced by invertible-output
pentagons, even though the reduced rules satisfy all their own
pentagons exactly. This restricts the proposed construction and
does not assert nonexistence of HI categories.

## 88.4 Verification and consequence for the construction problem

`hi_reduced_affine_associator.py` checks all reduced pentagon type
patterns symbolically, replays the affine uniqueness deduction
without field assumptions, and derives all four mixed support
covariances independently from fusion paths. It also exhausts
all \(3^3+5^5+7^7=826695\) finite maps at orders 3, 5, and 7,
confirming that (88.4c) has only the identity solution. The image-set
proof above supplies the uniform statement. An independent fusion-path implementation
checks unitarity of every order-3 block, every scalar balance
summand there, and all Fibonacci pentagons at order 1. At
\(n=3,5,7,9,11,15,23\), it checks the exact 0/1 path permutations
in (88.6) for every nonzero k, their operator norms, and the
phase-independent lower bound numerically. It also computes a
noninvertible-output pentagon to exercise the augmented matrices.
These numerical checks are regressions of the formulas, not
existence certificates. The saved run used approximately 100 MiB
peak resident memory.

Every monomial reduced construction therefore has the same obstruction
to supplying the balanced small-error trials required by Section 87,
even after changing its scalar phases and augmented blocks. A
successful trial must change its nonexceptional blocks substantially
in operator norm, or start from a different construction. **Infinitude
remains unproved.**

---

# 89. Correcting nonunitary trials with algebraic partial traces

The double-sine construction uses the dimension character
\(\delta_{\alpha_g}=1\), \(\delta_{\rho_g}=-1/d\). Its associators,
if reconstructed, need not be unitary in the fixed fusion bases.
Consequently Section 87 cannot be applied to that construction as
stated. This section removes that restriction, with a polynomial
loss in a bound for the associators and their inverses.

The result is a sufficient existence criterion for each order,
without a separate linear certificate and without assuming a nearby
exact category. It does not yet establish that the analytic candidate
satisfies this criterion for unbounded orders.

## 89.1 Conventions, algebraic trace, and scalar balance

Fix a multiplicity-free based fusion ring, its binary tensor functor
on finite-dimensional semisimple complex vector spaces, and orthonormal
fusion bases. Let F be a natural, invertible, strictly unit-normalized
trial associator. Ordinary operator norms refer to these fixed bases;
F is not assumed to preserve them. Fix nonzero numbers
\(\delta_a=\delta_{a^*}\), with
\[
 D=\sum_a\delta_a^2\ne0,\qquad
 S=\frac{\sum_a|\delta_a|^2}{|D|}\ge1.
 \tag{89.1}
\]
A dimension character is the intended choice, but the estimates below
only use the stated conditions on these weights.

Use right-associated cochains and the output update \(F\mapsto e^uF\),
as in Section 87, now with arbitrary complex u. Every conjugation is
\(c\mapsto FcF^{-1}\). In particular,
\[
 P=LS^{-1}_{\mathrm{short}},\qquad r=P-I,\qquad
 q=\max\|P-I\|,\qquad q_-=\max\|P^{-1}-I\|.
 \tag{89.2}
\]
Here L and \(S_{\mathrm{short}}\) are the long and short pentagon paths;
the subscript distinguishes the latter from the weight constant S.
Both maxima run over simple inputs and output blocks. Naturality
extends these bounds to arbitrary direct-sum inputs. If q<1 then
\(q_-\le q/(1-q)\). Unlike the unitary case, changing the base of
the pentagon can change its norm, so (89.2) is used throughout.

Let \(i_a:1\to a^*\otimes a\) be the fixed unit-channel inclusion.
The algebraic partial trace is
\[
 \mathcal T_{a,T}(c)=\delta_a(i_a^*\otimes I_T)
 F_{a^*,a,T}^{-1}(I_{a^*}\otimes c)F_{a^*,a,T}
 (i_a\otimes I_T).
 \tag{89.3}
\]
The star here is only the fixed fusion-basis projection. It is not
an inverse or a categorical adjoint of F. Equivalently choose
\(r_a^2=\delta_a\), and use cup \(r_ai_a\) and cap \(r_ai_a^*\).
For negative \(\delta_a\), this cap is not the adjoint of the cup.
These are auxiliary maps before coherence, with no snake identity
assumed.

If \(\|F\|,\|F^{-1}\|\le M\), with M at least one, then
\[
 \mathcal T_{a,T}(I)=\delta_a I_T,\quad
 \|\mathcal T_{a,T}\|_{\mathrm{cb}}\le|\delta_a|M^2,\quad
 \chi_m=D^{-1}\sum_a\delta_a\mathcal T_a,
 \|\chi_m\|_{\mathrm{cb}}\le SM^2.
 \tag{89.4}
\]
The trace is natural under arbitrary invertible maps of T, directly
by naturality of F. Thus the exact middle cancellations (87.4)
still hold with inverses, including \(\chi_{m+1}f_0^m=I\).
The signed differentials and the averaging map preserve unit
normalization.

Replace the squared magnitudes in (86.8) by algebraic products of
matrix coefficients and inverse coefficients:
\[
 \begin{split}
 \mu_b=\frac1{|D|}\sum_{a,z:N_{ab}^z=1}\big|&
 \delta_a^2[F^{a^*,a,b}_b]_{z,1}
                 [(F^{a^*,a,b}_b)^{-1}]_{1,z}\\
 &-\delta_z^2[F^{b,z^*,z}_b]_{1,a^*}
                 [(F^{b,z^*,z}_b)^{-1}]_{a^*,1}\big|,
 \qquad \mu=\max_b\mu_b.
 \end{split}
 \tag{89.5}
\]
For example, the algebraic analogues of standard unit-channel
normalization are
\[
 [F^{a^*,a,b}_b]_{z,1}[(F^{a^*,a,b}_b)^{-1}]_{1,z}
       =\frac{\delta_z}{\delta_a\delta_b},\qquad
 [F^{b,z^*,z}_b]_{1,a^*}[(F^{b,z^*,z}_b)^{-1}]_{a^*,1}
       =\frac{\delta_a}{\delta_b\delta_z}.
 \tag{89.6}
\]
They imply \(\mu=0\) even when the dimensions are negative or complex.
These products are unchanged by left and right diagonal rescalings
of each F block. No assertion that an arbitrary HI trial already
satisfies (89.6) is made.

## 89.2 Off-pentagon handle and homotopy bounds

Define the actual and reduced handle channels as in Section 86,
using (89.3) and inverses. There are now independent plus and minus
compression maps, instead of a map and its adjoint. For clarity,
the left reduced maps use
\[
 \begin{split}
 j^+_{azb}&=(I_{a^*}\otimes\iota_z^*)
       F_{a^*,a,b}(r_ai_a\otimes I_b),\\
 j^-_{azb}&=(r_ai_a^*\otimes I_b)
       F_{a^*,a,b}^{-1}(I_{a^*}\otimes\iota_z),
 \end{split}
 \tag{89.7}
\]
and the right reduced maps use
\[
 \begin{split}
 s^+_{azb}&=(\ell_{a^*}^*\otimes I_z)
       F_{b,z^*,z}^{-1}(I_b\otimes r_zi_z),\\
 s^-_{azb}&=(I_b\otimes r_zi_z^*)
       F_{b,z^*,z}(\ell_{a^*}\otimes I_z).
 \end{split}
 \tag{89.8}
\]
Here \(\iota_z:z\to a\otimes b\) and
\(\ell_{a^*}:a^*\to b\otimes z^*\) are the fixed inclusions.
The reduced plus maps are \(F_{a^*,z,T}(j^+\otimes I_T)\)
and \(F_{a^*,z,T}(s^+\otimes I_T)\); the minus maps have the
reverse factors with \(F^{-1}\).

For each a, stacking over z is an orthogonal direct-sum operation
on the fixed fusion bases. The actual and reduced plus stacks,
weighted by \(\sqrt{|\delta_a|/|D|}\), have norm at most
\(\sqrt S M^2\), as do their minus stacks. The corresponding
right stacks have the same bound, with z carrying the weight.
The phases of \(\delta_a/D\) may be placed on one of the two stacks
without changing these estimates.

The forward pentagon compares the actual and reduced plus stacks
with error at most \(\sqrt S M^2q\); its inverse compares the
minus stacks with error at most \(\sqrt S M^2q_-\). One can see
the two estimates directly before applying the cup: the paths have
the form
\[
 A=(I\otimes F^{-1})F_1,\qquad
 B=(I\otimes F^{-1})PF_1.
\]
Hence \(\|A-B\|\le M^2q\), and
\(\|A^{-1}-B^{-1}\|\le M^2q_-\). Naturality at the cup gives
the reduced paths (89.7)--(89.8). The tensor representations of a
cochain have the same norm as the cochain. Expanding
\(U^-cU^+-V^-cV^+\) in two differences now gives
\[
 \|L-\widetilde L\|_{\mathrm{cb}},\quad
 \|R-\widetilde R\|_{\mathrm{cb}}
       \le SM^4(q+q_-).
 \tag{89.9}
\]

The channel \(\operatorname{Hom}(b,a^*\otimes z)\) is
one-dimensional. Products of its plus and minus coefficients are
the two algebraic products in (89.5), each with one factor of
\(\delta_a\) or \(\delta_z\) supplied by the cup and cap. The
remaining common compression has norm at most \(M^2\). Therefore
\[
 \|\widetilde L-\widetilde R\|_{\mathrm{cb}}\le M^2\mu_b,
 \qquad
 \boxed{\|L-R\|_{\mathrm{cb}}
       \le2SM^4(q+q_-)+M^2\mu_b.}
 \tag{89.10}
\]

For the exterior right coface, the same plus/minus comparison on
\((a^*,a,T,Y)\) gives \(SM^4(q+q_-)\) before appending the
remaining tail. Its \(m-2\) associators add a conjugation norm
factor at most \(M^{2(m-2)}\). Thus
\[
 \|\chi_{m+1}f_{m+1}^m-f_m^{m-1}\chi_m\|
       \le SM^{2m}(q+q_-).
 \tag{89.11}
\]
Combining this with the exact middle cancellations and (89.10),
in degree four,
\[
 \|I-\partial_3\chi_4-\chi_5\partial_4\|
 \le S(2M^4+M^8)(q+q_-)+M^2\mu
 \le9SM^8q+M^2\mu\quad(q\le1/2).
 \tag{89.12}
\]
Neither positivity nor a categorical duality structure was used.

## 89.3 A polynomial compatibility bound in the general linear group

The right-based pentagon derivative is still
\(Ju=Z_+(u)P-PZ_-(u)\), as in (87.9), now without taking skew
parts. The five coface norms sum to at most
\(2+2M^2+M^4\le5M^4\), so
\[
 \|J-\partial_3\|\le5M^4q.
 \tag{89.13}
\]
The five-factor product rule gives a Taylor remainder at most
\((25/2)M^5\|u\|^2\), provided the exponential update path stays
where F and its inverse have norm at most M.

A direct use of the long boundary transports would give unnecessarily
large powers of M. Instead gauge the exact five-object rotation
graph of Section 86 along its saved spanning tree. Its root is the
fully right-associated vertex, and every tree path has length at
most three. The exact elimination certificate has the following
stronger property:

- A pentagonal elimination has all its other gauged edges equal
  to the identity. The new edge, in either orientation, is a
  conjugate of a canonical right-based pentagon or its inverse.
- A square either sets an edge to the identity or copies, possibly
  with inversion, just one earlier nonidentity gauged edge.

In the first case the conjugation can use the tree path to the
canonical right base of that face, of length at most three. Since
all other gauged edges in that face are identities, cyclically
moving its start vertex introduces no further factor. Consequently
every nonidentity gauged edge E satisfies
\[
 \|E-I\|,\ \|E^{-1}-I\|\le2M^6q=:t
 \qquad(q\le1/2).
 \tag{89.14}
\]

The six old transports in the right-based boundary certificate
have respectively zero, zero, two, two, one, and zero nonidentity
gauged edges. The six standard coface transports have none and
length at most three. These assertions, and the free-word boundary
identity itself, are replayed exactly in the new script.

Suppose now \(q\le1/(16M^6)\), so \(t\le1/8\). Each old
transport T and its inverse have norm at most
\(M^3(1+t)^2\). In particular,
\(\|\operatorname{Ad}(T)\|\le2M^6=:a\).
Write the six transported face holonomies as
\(U_i=\operatorname{Ad}(T_i)(P_i^{\epsilon_i})\), with three
negative signs. Their product is exactly the identity: the three
square factors in the nine-face free-word certificate are already
identities by naturality. We have
\(e:=\max_i\|U_i-I\|\le(4/3)aq\le1/6\).

Expanding the product, and using
\(\sum_{k=2}^6\binom6k e^k\le15e^2(1+e)^4\), bounds its
linear term. For each negative face, replacing its inverse
residual by minus its forward residual adds at most
\(aq^2/(1-q)\). Thus, for the signed boundary operator \(\widehat B\),
\[
 \|\widehat Br\|
 \le\bigl(15(4/3)^6+4\bigr)a^2q^2
 <90a^2q^2=360M^{12}q^2.
 \tag{89.15}
\]

To compare an old transport with its standard coface transport,
their loop has k nonidentity gauged edges, where k is zero, one,
or two. Its holonomy R and inverse obey
\(\|R^{\pm1}-I\|\le kt(1+t)\) and
\(\|R^{\pm1}\|\le(1+t)^2\). The difference of their
conjugation operators, including the standard transport, is at
most \(4ktM^6\). The sum of these six k values is five. Hence
\[
 \|\widehat B-\partial_4\|\le40M^{12}q,
 \qquad
 \boxed{\|\partial_4r\|\le400M^{12}q^2
        \quad\text{if }q\le1/(16M^6).}
 \tag{89.16}
\]
This proof uses only fixed five-object combinatorics and norm bounds;
the number of simple labels does not appear.

## 89.4 Explicit convergence and rigidity criterion

Combining (89.12)--(89.13), and \(\|\chi\|\le SM^2\), gives
\[
 \|I-J\chi_4-\chi_5\partial_4\|
       \le M^2\mu+14SM^8q.
\]
For \(u=-\chi_4r\), equation (89.16) and the Taylor bound imply
\[
 \begin{split}
 q_{\mathrm{new}}
 &\le M^2\mu q+
  \left(14SM^8+400SM^{14}+\frac{25}{2}S^2M^9\right)q^2\\
 &\le\boxed{M^2\mu q+427S^2M^{14}q^2}.
 \end{split}
 \tag{89.17}
\]

The scalar imbalance also has a rank-independent drift bound. Along
\(\dot F=uF\), a column of F and a row of \(F^{-1}\) each have
norm at most M and derivative norm at most \(M\|u\|\).
Cauchy--Schwarz bounds the sum of derivatives of their paired
products by \(2M^2\|u\|\). Sum first over z for the first term
of (89.5), and first over a for the second term. The weights give
\[
 |\mu(F_1)-\mu(F_0)|\le4SM^2\operatorname{length}(F_s).
 \tag{89.18}
\]
The length is \(\int\|u_s\|\,ds\), and all matrices along the
path must satisfy the bound M.

**Theorem.** Let F_0 be an invertible unit-normalized trial on the
fixed multiplicity-free fusion ring. Put
\[
 M_0=\max\{1,\|F_0\|,\|F_0^{-1}\|\},\qquad M=2M_0.
\]
If its residual and scalar imbalance satisfy
\[
 \boxed{M^2\mu_0+435S^2M^{14}q_0\le\tfrac12,}
 \tag{89.19}
\]
then the explicit iteration
\[
 F_{j+1}=\exp(-\chi_{4,F_j}(P(F_j)-I))F_j
 \tag{89.20}
\]
converges to exact invertible, unit-normalized associators, with
\[
 q_j\le2^{-j}q_0,\qquad
 \operatorname{length}(F_j)\le2SM^2q_0.
 \tag{89.21}
\]
If, additionally,
\[
 \lambda_0:=\min_a|[F_0^{a,a^*,a}_a]_{1,1}|
                >2SM^3q_0,
 \tag{89.22}
\]
the limit is a fusion category with the prescribed ring.

**Proof.** Condition (89.19) implies
\(q_0\le1/(870S^2M^{14})\le1/(16M^6)\) and
\(2SM^2q_0\le1/(435SM^{12})<\log2\). Every update segment
whose accumulated length is at most this bound keeps F and its
inverse bounded by \(M_0e^{\mathrm{length}}<M\).
Assume inductively that earlier residuals halve. Their total length,
including the next segment, is less than \(2SM^2q_0\).
By (89.18),
\(\mu_j\le\mu_0+8S^2M^4q_0\). Equation (89.17) gives
\[
 q_{j+1}\le
 \left[M^2\mu_0+(8S^2M^6+427S^2M^{14})q_0\right]q_j
 \le\tfrac12q_j.
\]
This closes the induction and proves (89.21). The finite total
length makes both the matrices and their inverses Cauchy, so the
limit is invertible and its pentagons hold exactly. Each unit
coefficient changes by at most M times the length; (89.22) makes
all of them nonzero at the limit. Nonzero unit-channel coefficients
give left and right rigidity by Definition 2.5 and Proposition 3.2
of [Fuchs--Grøsfjeld, *Tetrahedral symmetry of 6j-symbols in fusion
categories*](https://www.diva-portal.org/smash/get/diva2:1682055/FULLTEXT01.pdf).
No pivotal or unitary structure is assumed in that rigidity result.
This proves the theorem.

In particular, algebraically balanced trials satisfy the simple
sufficient inequality
\[
 \boxed{q_0\le\frac1{870S^2(2M_0)^{14}}.}
 \tag{89.23}
\]
For the HI ghost dimensions,
\(D=n(1+d^{-2})>0\) and S=1. If a ghost trial also has the
standard unit coefficients \([F^{a,a^*,a}_a]_{1,1}=1/\delta_a\),
their minimum magnitude is one, so (89.23) automatically implies
the rigidity margin (89.22). This gives a nonunitary HI existence
criterion requiring only algebraic balance, invertibility, and a
sufficiently small full right-based pentagon residual.

## 89.5 Checks and the remaining uniform construction problem

`hi_nonunitary_pentagon_correction.py` replays the free-word boundary
and the spanning-tree elimination certificate, recovers all six
right-based pentagons with their signs, and checks the integer and
rational estimates used in (89.14)--(89.19). Independent general
linear matrices on the edges, with only the squares imposed, test
the boundary and transport formulas in dimensions 2, 3, and 7.

It also implements actual inverses, algebraic cups and caps, handle
channels, cofaces, derivatives, and updates for the Fibonacci ring.
Tests use both dimension roots, including the nonunitary Yang--Lee
matrix
\[
 F=\begin{pmatrix}t^2&t\\t&-t^2\end{pmatrix},\qquad
 t=1/\sqrt\delta,\quad\delta=(1-\sqrt5)/2.
\]
Balanced and unbalanced perturbations exercise the two handle
comparisons, the scalar comparison, exact middle cancellations,
the exterior comparison, the derivative, and the imbalance drift.
These are floating-point regressions of the proofs, not completely
bounded norm certificates. A balanced Yang--Lee perturbation has
successive full pentagon errors approximately
\[
 7.38\cdot10^{-2},\quad1.31\cdot10^{-3},\quad
 1.03\cdot10^{-6},\quad5.85\cdot10^{-13},\quad1.82\cdot10^{-14}.
\]
That numerical iteration begins outside the conservative theorem
threshold and is not presented as a certified instance of (89.19).
The saved complete run uses approximately 60 MiB of resident memory.

Section 80.7 encloses Q and C residuals of phase-derived core
matrices. Section 90 supplies full trial associators, their inverse
and operator bounds, and exact algebraic balance, and certifies
the correction criterion at three finite orders. Infinitude still
requires the sufficient bounds for an unbounded set of orders.
Refining an approximation alone does not prove that the exact
analytic residual is small. The theorem removes the unitarity
obstacle to this route; it does not supply the missing unbounded
family. **Infinitude remains unproved.**

---

# 90. From certified core residuals to full HI existence certificates

The remaining finite-order inputs to Section 89 can all be read
from the core matrix. The reconstruction formula of Section 2
holds as a definition before coherence, and its pentagon error
has a particularly simple entrywise description. This supplies
a uniform sufficient inequality for the analytic candidate, and
the interval calculations now verify it at orders 3, 7, and 11.

The finite conclusions establish categories near the analytic
trials. They do not assert that the analytic trials themselves
satisfy the pentagon exactly or that their special-function values
are algebraic.

## 90.1 Transparent trials and all their pentagon residuals

Let \(\delta^2=n\delta+1\), \(t=1/\delta\), and choose
\(s^2=t\). Suppose the core A satisfies only
\[
 A_{g,h}=A_{-h,g-h},\qquad
 A_{g,0}=A_{0,g}=A_{g,g}=-\frac1{\delta-1}\ (g\ne0),\quad
 A_{0,0}=1-\frac1{\delta-1}.
 \tag{90.1}
\]
Define each admissible F coefficient with an invertible external
input or output to be one. For three noninvertible inputs and a
noninvertible output, use t when both intermediate channels are
invertible, s when exactly one is invertible, and
\[
 [F^{\rho_a,\rho_b,\rho_c}_{\rho_o}]_{\rho_y,\rho_x}
       =A_{o+b-a-c,\,x+y-a-c}
 \tag{90.2}
\]
otherwise. Rows index right channels, as in Section 89. These
form natural, unit-normalized trial maps; invertibility will follow
from the quantitative condition below.

For a pentagon on \((\rho_a,\rho_b,\rho_c,\rho_e)\), write its
left basis as \((x,y)\), where x is the first pair's channel and
y the first triple's channel. Write its right basis as \((z,w)\),
where z is the last pair's channel and w the last triple's channel.
The long-minus-short entry is
\[
 \begin{split}
 E_{(z,w),(x,y)}={}&
 \sum_u [F^{\rho_b,\rho_c,\rho_e}_w]_{z,u}
         [F^{\rho_a,u,\rho_e}_{o}]_{w,y}
         [F^{\rho_a,\rho_b,\rho_c}_y]_{u,x}\\
 &-[F^{\rho_a,\rho_b,z}_{o}]_{w,x}
         [F^{x,\rho_c,\rho_e}_{o}]_{z,y},
 \end{split}
 \tag{90.3}
\]
where inadmissible factors vanish. Here o denotes the output object;
its cyclic label is also written o when its type is specified.

When the output and all four displayed channels are noninvertible,
put
\[
 g=y+b-a-c,\quad h=w+c-b-e,\quad
 k=x-o+e-c,\quad l=z-o+a-b.
 \tag{90.4}
\]
Changing the noninvertible summation label to
\(m=o+u-a-e\), the three long-path factors become
\(A_{m,g+h}A_{g,m+k}A_{h,m+l}\). The two short-path
factors become \(A_{g+l,k}A_{h+k,l}\), using the order-three
symmetry. The possible invertible u contributes
\(t\mathbf1_{g=h=0}\). Consequently
\[
 \boxed{E_{(z,w),(x,y)}=C(g,h,k,l)}
 \tag{90.5}
\]
for the residual C defined in Section 52.

All the other noninvertible-output entries are as follows. In this
table alpha means an invertible channel and rho a noninvertible
channel. The labels in (90.4) are used only when their channels
are noninvertible.

| Left channels \((x,y)\) | Right \((z,w)=(\alpha,\rho)\) | Right \((\rho,\alpha)\) | Right \((\rho,\rho)\) |
|---|---:|---:|---:|
| \((\alpha,\rho)\) | 0 | 0 | \(sQ(-l,h)\) |
| \((\rho,\alpha)\) | 0 | 0 | 0 |
| \((\rho,\rho)\) | \(sQ(-k,g)\) | 0 | \(C(g,h,k,l)\) |

For example, x invertible forces \(g=0\). The noninvertible-u
part of the long path is
\(s[Q(-l,h)+\mathbf1_{l=0}-t\mathbf1_{h=0}]\).
Its invertible-u part is \(st\mathbf1_{h=0}\), and the short
path is \(s\mathbf1_{l=0}\), giving the table entry. The
z-invertible case has the corresponding k formula. If y is
invertible then k=0 and m=0; if w is invertible then l=0 and
m=0. Substitution gives equality of the two paths. When both x
and z are invertible, the cancellation is
\(t\sum_m A_{m,0}+t^2=0\). These calculations cover all nine
type pairs.

For invertible output \(\alpha_o\), y and w are necessarily
noninvertible, with labels \(y=o+e\), \(w=a-o\). If x and z
are noninvertible, the same substitution gives
\[
 \boxed{E_{(z,w),(x,y)}=Q(z-x+o,\ o+e+b-a-c).}
 \tag{90.6}
\]
The other entries are zero. The cases with one of x,z invertible
use \(\sum_m A_{m,0}=-t\); with both invertible they use
\(nt+t^2=1\). Both identities follow from (90.1) and
\(\delta^2=n\delta+1\).

Finally, if an external input is invertible, each nontrivial path
coefficient has at most one all-noninvertible F factor. The
transparent translations in (90.2) identify its two indices on
the two paths; the admissible t and s coefficients match as well.
Thus every such pentagon already holds. This proves the entrywise
description at all odd orders without assuming Q or C.

## 90.2 Bounds for inverses, balance, and the full operator error

For the rest of the section use the ghost root \(\delta=-1/d\),
where \(d=(n+\sqrt{n^2+4})/2\). Up to independent row and
column permutations, all nontrivial trial matrices are the
n by n anti-circulant blocks
\[
 (K_g)_{ij}=A_{g,i+j}\quad(g\ne0)
\]
and the single augmented block
\[
 F_0=\begin{pmatrix}
 t&s\mathbf1^T\\s\mathbf1&P-\dfrac1{\delta-1}J
 \end{pmatrix},\qquad P_{ij}=\mathbf1_{i+j=0}.
 \tag{90.7}
\]
The latter satisfies \(F_0^2=I\) exactly, independently of every
nonexceptional entry of A. On the constant subspace it is
\(\left(\begin{smallmatrix}-d&i\sqrt{nd}\\i\sqrt{nd}&d\end{smallmatrix}\right)\),
up to the sign chosen for s; on the orthogonal complement it is
the permutation P. Therefore
\[
 \|F_0\|=\|F_0^{-1}\|=d+\sqrt{nd}<2d.
 \tag{90.8}
\]

For g nonzero define
\((G_g)_{ij}=A_{-g,i+j-g}\). The order-three symmetry gives,
entry by entry,
\[
 (K_gG_g-I)_{ij}=Q(j-i,g).
 \tag{90.9}
\]
Let \(\epsilon_Q\ge\max|Q|\) and \(\epsilon_C\ge\max|C|\).
If \(n\epsilon_Q<1\), the Neumann series makes every \(K_g\)
invertible and bounds its inverse by
\(\|G_g\|/(1-n\epsilon_Q)\).

The norm of an anti-circulant is the largest magnitude of the
discrete Fourier coefficients of its defining row. In particular,
with \(\zeta=e^{2\pi i/n}\), set
\[
 R=\max_{g\ne0,k}\left|\sum_h A_{g,h}\zeta^{kh}\right|,
 \qquad
 M_0=\max\left\{2d,\frac{R}{1-n\epsilon_Q}\right\}.
 \tag{90.10}
\]
This bounds all full trial associators and their actual inverses.
An upper bound on R suffices; the coarser row-sum bound
\(R\le\max_{g\ne0}\sum_h|A_{g,h}|\) is also available.
The Fourier assertion follows by writing an anti-circulant as a
circulant times a permutation and applying the unitary discrete
Fourier transform.

Only the augmented block and scalar-one blocks occur in the unit
products (89.5). Since the augmented inverse is exactly itself,
their products are \(t^2\), \(s^2=t\), or one. They satisfy
(89.6) for every admissible type combination. Thus the algebraic
imbalance is **exactly zero**, even when Q and C are nonzero.
The unit coefficients themselves are \(1/\delta_a\), so their
minimum magnitude is one. No nonunitary rigidity hypothesis is
left to check separately once the small-error bound holds.

The all-noninvertible fourfold tensor product has block dimension
\(n^2+2\) at each noninvertible output and at most \(n+1\) at
an invertible output. A square matrix of size m and maximum entry
magnitude epsilon has norm at most \(m\,\mathrm{epsilon}\).
The entrywise formulas therefore give
\[
 \|L-S_{\mathrm{short}}\|
       \le(n^2+2)\max\{\epsilon_C,\sqrt d\,\epsilon_Q\}.
\]
The short inverse has norm at most \(M_0^2\), so the required
right-based pentagon error obeys
\[
 \boxed{q\le\overline q:=(n^2+2)M_0^2
               \max\{\epsilon_C,\sqrt d\,\epsilon_Q\}.}
 \tag{90.11}
\]

**Corollary.** A ghost core satisfying (90.1) gives complex HI
existence at that order whenever \(n\epsilon_Q<1\) and
\[
 \boxed{870(2M_0)^{14}(n^2+2)M_0^2
             \max\{\epsilon_C,\sqrt d\,\epsilon_Q\}\le1.}
 \tag{90.12}
\]
Indeed, (90.11), exact balance, S=1, and the unit-coefficient
margin supply every hypothesis of Section 89. The correction
may leave the transparent form; this does not change its fusion ring.

## 90.3 Complete interval certificates at three known orders

`hi_transparent_residual_bound.py` checks the generic index changes
over the integers and the scalar cancellations as exact rational
identities. It then builds complete five-edge pentagons on arbitrary
order-three symmetric cores with nonzero Q and C. At order 3 and
the negative dimension root, all 7,776 combinations of four inputs
and output are checked, covering 46,494 entries. Further trials at
the positive order-3 root and negative roots at 5 and 7 exercise
all internal type combinations. The largest discrepancy from the
predicted residual formula is about \(1.5\times10^{-14}\), while
the Q and C residuals being matched are of order one or larger.
The inverse formula and the Fourier norm formula are checked
independently as well. These floating-point checks support the
uniform algebraic derivation above.

The FLINT/Arb program now computes certified Fourier bounds in
(90.10) and reports the full sufficient inequality, in addition
to its core residual enclosures. It accepts a sufficiently small
residual whether or not its interval contains zero; zero containment
is reported separately and is not used as an existence argument.
The following run uses 256-bit arithmetic and nine extrapolation
levels, with uniform logarithmic remainder less than
\(6.44\times10^{-39}\):

```sh
cc -O2 -std=c11 -Wall -Wextra -Werror -DLEVELS=9 \
  hi_shintani_boundary_series.c -o /tmp/hi_shintani_correction_certificate \
  $(pkg-config --cflags --libs flint)
/tmp/hi_shintani_correction_certificate
```

The full bounds are saved in `hi_shintani_correction_results.txt`.
The displayed bounds below are rounded upward, except for the
thresholds, which are rounded downward.

| n | Certified \(M_0\) bound | Full \(\overline q\) bound | Sufficient threshold \(1/[870(2M_0)^{14}]\) | Upper bound for threshold ratio |
|---:|---:|---:|---:|---:|
| 3 | 6.605552 | \(3.125\times10^{-35}\) | \(2.329\times10^{-19}\) | \(1.342\times10^{-16}\) |
| 7 | 14.280110 | \(2.052\times10^{-32}\) | \(4.784\times10^{-24}\) | \(4.289\times10^{-9}\) |
| 11 | 34.334691 | \(9.671\times10^{-30}\) | \(2.217\times10^{-29}\) | 0.43617 |

Every threshold ratio is strictly below one. The corresponding
upper bounds for changes of the unit coefficients are below
\(1.441\times10^{-31}\), \(9.560\times10^{-28}\), and
\(6.263\times10^{-24}\), respectively. The run finishes in about
three seconds with approximately 13 MiB peak resident memory.
A separate Python calculation parses the outward printed bounds
and rechecks the correction and rigidity inequalities with exact
rational arithmetic, using even the coarser
\(\sqrt d<n+1\). Its complete log is included in
`hi_transparent_residual_bound_results.txt`.
The nine new half-sample balls are also checked numerically against
independent double-sine integrals at 50 decimal digits, with the
complete comparison saved in `hi_shintani_correction_checks_results.txt`.

These are rigorous existence certificates by analytic approximation
and correction at three **known** finite orders. They use no exact
Stark-unit relation or fitted algebraic HI seed, and do not infer
an exact zero from an interval containing zero. The finite input
could alternatively be chosen from rational midpoint samples within
the internal Arb half-sample intervals, with the other half defined
by exact reflection; the same estimates apply.

For infinitude, (90.12) is now a concrete sufficient target involving
only the explicitly constructed core, finite Fourier sums, and
Q/C residuals. Exact analytic cancellation would suffice, but it
is stronger than necessary. For example, if \(M_0(n)\le K n^b\)
on an unbounded set, bounds
\[
 \max\{\epsilon_C,\sqrt d\,\epsilon_Q\}
                  =o(n^{-16b-2})
\]
would suffice on that set. Section 91 shows that these particular
analytic ghost trials have exponential growth even after changing
fusion bases; Section 92 gives the corresponding explicit error
target. No uniform verification of a sufficient additive bound
at unbounded orders has been proved. **Infinitude remains unproved.**

---

# 91. Uniform ghost growth and a gauge-invariant obstruction to reducing it

The polynomial-growth example at the end of Section 90 does not
describe these ghost trials. Their largest generic entries grow
exponentially, and no change of trivalent fusion bases removes
that growth. The growth can be determined from a uniform elementary
estimate on the double sine.

## 91.1 A bounded-error real dilogarithm approximation

Write
\[
 f(x)=-\int_0^x\log(2\sin\pi t)\,dt
 =\frac1{2\pi}\sum_{k\ge1}\frac{\sin(2\pi kx)}{k^2}
 \quad(0\le x\le1).
 \tag{91.1}
\]
In particular, \(f(0)=f(1)=0\), \(f(1-x)=-f(x)\), and
\(|f(x)|\le\pi/12\). Use the positive-period double sine with
the normalization of Section 76.

**Lemma.** For d positive, \(0<x<1\), and
\(z=dx+1/2\),
\[
 \log\operatorname{Sin}_2(z;d,1)=d f(x)+E_d(x),
\]
where E has the sign of \(1/2-x\) and
\[
 \boxed{|E_d(x)|\le
  \min\left\{\tfrac12\log2,\frac{\pi|\cot\pi x|}{24d}\right\}.}
 \tag{91.2}
\]
At x=1/2 the remainder is exactly zero.

**Proof.** Put \(c=1-2x\) and rescale the integral (51.8) by
\(u=dt\). Its leading part is
\[
 I(x)=\int_0^\infty
 \left[c-\frac{\sinh(cu/2)}{\sinh(u/2)}\right]\frac{du}{u^2}.
\]
Differentiating twice on compact subintervals of (0,1) gives
\[
 I''(x)=-\int_0^\infty\frac{\sinh((1-2x)u/2)}{\sinh(u/2)}\,du
       =-\pi\cot\pi x=f''(x).
\]
For the middle equality, expand the ratio as
\((e^{-xu}-e^{-(1-x)u})/(1-e^{-u})\) and use the partial
fraction expansion of cotangent. Dominated convergence at both
endpoints gives \(I(0)=I(1)=0\), so I=f. The remaining term is
\[
 E_d(x)=d\int_0^\infty
 \frac{\sinh((1-2x)u/2)}{\sinh(u/2)}
 \left[1-\frac{u/(2d)}{\sinh(u/(2d))}\right]\frac{du}{u^2}.
 \tag{91.3}
\]
Its sign is as asserted. For \(v\ge0\),
\(0\le1-v/\sinh v\le\min\{1,v^2/6\}\).
The quadratic inequality follows, for \(v^2<6\), by comparing
the coefficients of \(\sinh(v)/v\) with those of
\((1-v^2/6)^{-1}\); for larger v it is immediate. This bounds
(91.3) by \(\pi|\cot\pi x|/(24d)\).

For the other bound, the absolute value of the hyperbolic ratio
in (91.3) is at most one. The resulting integral is its value at
x=0. The double-sine reflection and d-shift identities give
\(\operatorname{Sin}_2(1/2;d,1)=\sqrt2\), so that value is
\((\log2)/2\). All these integrals converge absolutely. This
proves the lemma.

For the HI periods let \(d=(n+\sqrt{n^2+4})/2\), and write
\[
 L_n(a)=\log F_n(a)
       =\log\operatorname{Sin}_2(1+ad/(d+1);d,1).
\]
For real \(0\le a\le n\), put \(\theta=a/n\). The x appearing
in (91.2) is exactly
\[
 x=\theta+\frac{1/2-\theta}{d}.
 \tag{91.4}
\]
It lies between \(1/(2d)\) and \(1-1/(2d)\). Since
\(\pi|\cot\pi x|\le1/\min(x,1-x)\), equation (91.2)
even gives \(|E_d(x)|\le1/12\) throughout this interval.
For integer \(1\le a<n\), \(|f'|\le\log n\) between x and
theta. Using \(d-n=1/d\) gives the uniform estimate
\[
 \boxed{|L_n(a)-nf(a/n)|\le B_n:=
       \tfrac12\log n+\frac{\pi}{12d}+\frac1{12}.}
 \tag{91.5}
\]
For instance, the derivative bound follows from
\(2\sin\pi t\ge4/n\) when \(1/n\le t\le1-1/n\),
and \(2\sin\pi t\le2\).

## 91.2 The largest generic entry is determined by a balanced triple

Reflection gives \(L_n(n-a)=-L_n(a)\), and
\(L_n(0)=\tfrac12\log d\). Direct differentiation of (51.8)
shows that \(L_n''(a)<0\) for \(0<a<n/2\), and
\(L_n''(a)>0\) for \(n/2<a<n\). Also
\(L_n'(n-a)=L_n'(a)\).

If \(0<b<a\) and \(a+b<n\), these facts imply
\(L_n'(a)<L_n'(b)\): when a exceeds n/2, compare n-a
with b. It follows by transferring weight from the larger
coordinate to the smaller that
\[
 H_n(a,b,c)=L_n(a)+L_n(b)+L_n(c),\qquad a+b+c=n,
\]
is strictly increased by balancing unequal positive coordinates.
On the boundary it is constantly \((\log d)/2\). Hence
\[
 \tfrac12\log d\le H_n(a,b,c)\le3L_n(n/3),
 \tag{91.6}
\]
and its maximum on positive integer triples is attained precisely
at permutations of
\[
 (a_*,b_*,c_*)=
  (\lfloor n/3\rfloor,\lfloor(n+1)/3\rfloor,\lfloor(n+2)/3\rfloor).
\]

For \(0<g<h<n\), the generic core formula has magnitude
\[
 |A_{g,h}|=
 \frac{\exp H_n(g,h-g,n-h)}{\sqrt d(1+1/d)}.
 \tag{91.7}
\]
When \(0<h<g<n\), its magnitude is the same prefactor times
\(\exp[-H_n(h,g-h,n-g)]\). By (91.6) these reverse entries
are at most \(1/(d+1)\), whereas all the entries in (91.7)
are at least the axis value \(d/(d+1)\). Thus the maximum
over **generic** positions is exactly
\[
 \boxed{\Gamma_n=
 \frac{F_n(a_*)F_n(b_*)F_n(c_*)}{\sqrt d(1+1/d)}.}
 \tag{91.8}
\]
This maximum excludes the exceptional origin entry, which can be
larger at small orders.

Define the positive constant
\[
 \kappa=3f(1/3)
       =\frac3{2\pi}\sum_{k\ge1}\frac{\sin(2\pi k/3)}{k^2}
       =0.32306594721945051409\ldots.
 \tag{91.9}
\]
The function \(f(x)+f(y)+f(1-x-y)\) on the positive triangle
is strictly concave, vanishes on the boundary, and has maximum
kappa at the equilateral point. For concavity, its negative
Hessian has positive diagonal entries because
\(\cot\alpha+\cot\gamma=\sin\beta/(\sin\alpha\sin\gamma)>0\),
and positive determinant because
\(\cot\alpha\cot\beta+\cot\beta\cot\gamma+
\cot\gamma\cot\alpha=1\) when \(\alpha+\beta+\gamma=\pi\).

Combining this with (91.5), and bounding the second derivatives
by 5 on the interval containing the balanced integer triple, gives
the completely explicit bounds
\[
 \begin{split}
 \kappa n-3B_n-\frac5{3n}-\tfrac12\log d-\log(1+1/d)
 &\le\log\Gamma_n\\
 &\le\kappa n+3B_n-\tfrac12\log d-\log(1+1/d).
 \end{split}
 \tag{91.10}
\]
Here the balanced coordinates lie in [1/5,1/2] and their squared
distances from 1/3 sum to at most \(2/(3n^2)\); use
\(\pi\cot(\pi/5)<5\) for the Taylor bound.

One also obtains the sharper asymptotic
\[
 \boxed{\Gamma_n=3^{-1/4}n^{-1/2}e^{\kappa n}(1+O(1/n)).}
 \tag{91.11}
\]
Indeed, uniformly near theta=1/3, (91.2)--(91.4) give
\(L_n(a)=nf(\theta)+(1/2-\theta)f'(\theta)+O(1/n)\).
The balanced displacements sum to zero, and
\(f'(1/3)=-(\log3)/2\). Their total constant term is therefore
\(-\tfrac14\log3\), proving (91.11).

A convenient bound with no asymptotic constant is
\[
 \boxed{\Gamma_n\le2n^{-1/2}e^{\kappa n}\quad(n\ge3).}
 \tag{91.12}
\]
Use (91.6) and \(x=1/3+1/(6d)\) in (91.2). Since f decreases
there, \(3L_n(n/3)\le d\kappa+1/4\). Finally
\(\kappa\le\pi/4\), \(d-n=1/d\), and
\(1/4+\pi/12<\log2\) give (91.12).

## 91.3 Every fusion-basis gauge retains an exponentially large entry

For a fixed generic position (g,h), consider all coefficients
(90.2) indexed by a,b,c,x, with
\[
 o=g-b+a+c,\qquad y=h-x+a+c.
\]
They are all equal to \(A_{g,h}\). A change of noninvertible
trivalent bases by nonzero scalars \(v_{a,b}^x\) changes each
coefficient by
\[
 \frac{v_{a,b}^x v_{x,c}^o}{v_{b,c}^y v_{a,y}^o}.
\]
As a,b,c,x vary, each of the four indexed vertex multisets consists
of every noninvertible trivalent vertex exactly n times. All gauge
factors cancel in the product. Thus
\[
 \boxed{\prod_{a,b,c,x}
  [F'^{\rho_a,\rho_b,\rho_c}_{\rho_{g-b+a+c}}]
        _{\rho_{h-x+a+c},\rho_x}=A_{g,h}^{\,n^4}.}
 \tag{91.13}
\]
At least one entry in every gauge consequently has magnitude at
least \(\Gamma_n\). Multiplicity-free fusion-basis changes are
precisely such scalar changes; permutations of simple labels only
permute these bounds. This rules out reducing all these ghost
associator norms to polynomial growth by a fusion-basis gauge.

For the original transparent basis, the Fourier quantity R in
(90.10) satisfies
\[
 \Gamma_n\le R\le n\Gamma_n.
 \tag{91.14}
\]
The upper bound follows from the entry bounds above; the lower
bound follows from Fourier inversion. Hence the maximum norm of
the direct trial associators has exponential rate exactly kappa.
When \(n\epsilon_Q\le1/2\), the inverse bound in Section 90
has the same rate, and more explicitly
\[
 \boxed{M_0\le4\sqrt n\,e^{\kappa n}.}
 \tag{91.15}
\]
To include the augmented block, note that \(\kappa>1/4\) and
\(\log n\le n/2\), so \(e^{\kappa n}\ge\sqrt n\).
The inequality \(\kappa>1/4\) already follows from the first
positive term in
\(\kappa=\frac{3\sqrt3}{4\pi}\sum_{j\ge0}
[(3j+1)^{-2}-(3j+2)^{-2}]\).

`hi_ghost_growth.py` checks the gauge multisets exactly for all
core positions at 3, 5, and 7. Independent double-sine integrals
test the bounded remainder and growth formulas through order 1001;
only a few samples are needed at the larger orders. For example,
\(\Gamma_n\sqrt n e^{-\kappa n}\) is approximately 0.73419
at 31, 0.75147 at 101, and 0.75898 at 1001, approaching
\(3^{-1/4}\approx0.75984\). These checks do not verify Q or C
at those larger orders. Peak resident memory was about 58 MiB.

The conclusion concerns conditioning of this construction, not
nonexistence of HI categories. The small-error correction route
needs exponentially accurate additive identities in these bases.
The next section improves the sufficient error exponent by using
the fixed unit-channel blocks more carefully.

---

# 92. Uniformly bounded ghost traces and a stronger infinitude target

The bound \(\|\chi\|\le SM^2\) in Section 89 charges the trace
for the largest generic associator. At transparent HI trials the
trace only uses the fixed unit-channel rows and columns. Its
normalized norm remains bounded independently of n, despite the
growth in Section 91.

## 92.1 Both normalized cup stacks have bounded norm

Include the four kinds of auxiliary maps
\[
 \begin{array}{ll}
 V^L_{a,T}=F_{a^*,a,T}(r_ai_a\otimes I),&
 W^L_{a,T}=(r_ai_a^*\otimes I)F_{a^*,a,T}^{-1},\\
 V^R_{a,T}=F_{T,a^*,a}^{-1}(I\otimes r_ai_a),&
 W^R_{a,T}=(I\otimes r_ai_a^*)F_{T,a^*,a},
 \end{array}
 \tag{92.1}
\]
where \(r_a^2=\delta_a\). Let H bound the squared norms of all
four stacks, with a stacked using weight
\(\sqrt{|\delta_a|/D}\). Equivalently, bound the norms of the
weighted sums of their Euclidean Gram matrices. The definition
uses no categorical adjoint. It implies \(\|\chi_m\|\le H\)
at every degree.

At the initial transparent ghost trial, for invertible a every
map in (92.1) has squared norm one. For noninvertible a its
squared norm is \(1/d\) if T is invertible, and d+n if T is
noninvertible. The latter is the squared norm of
\(\sqrt\delta(t,s,\ldots,s)\), using \(F_0^{-1}=F_0\).
For a simple T the resulting weighted Gram is a scalar. Since
\(D=n(1+d^{-2})\), these scalars are one and
\[
 \boxed{H_0=\frac{3-d^{-2}}{1+d^{-2}}<3,}
 \tag{92.2}
\]
respectively. Naturality gives the same bound on arbitrary direct
sums. This proves the bound for all four stacks, including the
right cup maps needed for the reduced right handle.

Along a path of length ell on which F and its inverse have norm
at most M, each of the four stacks changes in norm by at most
\(M\,\mathrm{ell}\). Indeed, \(\|F-F_0\|\) and
\(\|F^{-1}-F_0^{-1}\|\) are at most that quantity, and the
squared cup weights sum to
\(\sum_a|\delta_a|^2/D=1\). Consequently throughout the path
\[
 H\le(\sqrt{H_0}+M\,\mathrm{ell})^2.
 \tag{92.3}
\]
The correction is not required to retain the transparent form.

## 92.2 Improved off-pentagon estimates and convergence

Using (92.1) in the proof of (89.9), the actual and reduced
handle stacks have norm at most \(\sqrt H M\), and their
differences are at most \(\sqrt H Mq\) and
\(\sqrt H Mq_-\). This follows from the same pentagon
comparison, keeping \(F_{a^*,a,T}(r_ai_a\otimes I)\) as a
single cup map instead of estimating its two factors separately.
The reduced right stacks use the right maps in (92.1).
Thus
\[
 \|L-\widetilde L\|,\ \|R-\widetilde R\|
        \le HM^2(q+q_-),\qquad
 \|L-R\|\le2HM^2(q+q_-)+M^2\mu.
 \tag{92.4}
\]
The exterior right coface similarly has bound
\(HM^{2m-2}(q+q_-)\). The exact middle cancellations are
unchanged, giving
\[
 \|I-\partial_3\chi_4-\chi_5\partial_4\|
 \le H(2M^2+M^6)(q+q_-)+M^2\mu
 \le9HM^6q+M^2\mu\quad(q\le1/2).
 \tag{92.5}
\]
Use the derivative estimate \(5M^4q\), the compatibility
estimate \(400M^{12}q^2\), and the five-factor Taylor bound
already proved in Section 89. The update \(u=-\chi_4r\) now
has norm at most Hq, and
\[
 q_{\mathrm{new}}\le M^2\mu q+
  \left(14HM^6+400HM^{12}+\tfrac{25}{2}H^2M^5\right)q^2.
 \tag{92.6}
\]
If \(H\le4\), its quadratic coefficient is at most
\(1856M^{12}\).

**Theorem.** Let a transparent ghost trial satisfy the conditions
of Section 90, with F and its inverse bounded by \(M_0\), and
put \(M=2M_0\). It suffices that
\[
 \boxed{q_0\le\frac1{3776M^{12}}.}
 \tag{92.7}
\]
Then the same iteration (89.20) converges to a complex HI category,
with \(q_j\le2^{-j}q_0\) and total length at most \(8q_0\).

**Proof.** Assume the earlier residuals halve and use H at most
four for the steps already taken. Including the next segment,
the length is less than \(8q_0<\log2\), so F and its inverse
remain bounded by M. Equation (92.3) keeps H below four because
\[
 8Mq_0\le\frac1{472M^{11}}\le\frac1{472},\qquad
 \sqrt3+\frac1{472}<2.
\]
This also justifies the initial use of H at most four, by the
usual first-exit argument along each segment. The initial
imbalance is zero, and (89.18) gives
\(\mu_j\le32M^2q_0\). Equation (92.6) now yields
\[
 q_{j+1}\le(32M^4+1856M^{12})q_0q_j
          \le1888M^{12}q_0q_j\le\tfrac12q_j.
\]
The compatibility smallness condition \(q\le1/(16M^6)\)
also follows from (92.7). The induction, convergence, and
invertibility follow as in Section 89. The unit coefficients
change by at most \(8Mq_0<1\), preserving their nonzero
initial magnitudes. Thus rigidity is preserved as well.

The core form of this improved sufficient inequality is
\[
 \boxed{3776(2M_0)^{12}(n^2+2)M_0^2
        \max\{\epsilon_C,\sqrt d\,\epsilon_Q\}\le1.}
 \tag{92.8}
\]
It permits errors larger than (90.12) by the factor
\(870(2M_0)^2/3776\). A rational replay of the previous
certified bounds gives threshold ratios below
\(3.335\times10^{-18}\), \(2.282\times10^{-11}\), and
\(0.000401459\) at 3, 7, and 11, respectively. No new
special-function evaluations are needed for this improvement.

`hi_ghost_trace_bound.py` checks the exact normalization and
constant calculations, and tests all four cup stacks and the
improved handle and exterior estimates on incoherent Fibonacci
and Yang--Lee trials. It also checks the drift estimate and
replays (92.7) on the printed interval bounds with rational
arithmetic. The saved run used about 96 MiB of resident memory.

## 92.3 An explicit sufficient error rate depending only on n

Let \(\eta_n=\max\{\epsilon_C,\sqrt d\,\epsilon_Q\}\) for
the analytic ghost core. Combining (91.15) with (92.8) gives
the following uniform implication:
\[
 \boxed{\eta_n\le
 \frac{e^{-14\kappa n}}{3776\,2^{40}\,n^7(n^2+2)}
 \quad\Longrightarrow\quad
 \text{complex cyclic HI existence at order n}.}
 \tag{92.9}
\]
Indeed, this bound already implies \(n\epsilon_Q<1/2\).
Then \(M_0\le4\sqrt n e^{\kappa n}\), and substitution
in (92.8) gives exactly the denominator in (92.9).
All statements leading to this implication are uniform in odd n.

Thus proving \(\eta_n=o(n^{-9}e^{-14\kappa n})\) on an
unbounded set would establish the requested infinitude. The
exponential rate is \(14\kappa\approx4.5229232611\).
One may also formulate a cubic-only target, since the exact
identity (52.2) allows the choice
\(\epsilon_Q=(1+1/d)\epsilon_C\); multiplying a cubic
bound by \(\sqrt d+1/\sqrt d\) then bounds eta.

The double-sine asymptotics in Section 91 control individual
entries. They do not control cancellation among the terms of Q
or C to this accuracy. The asymptotic checks through 1001 also
do not measure those residuals. A proof of (92.9), or of another
sufficient additive estimate, at unbounded orders is still
missing. **Infinitude remains unproved.**

---

# 93. An exact finite Fourier transform proves every quadratic identity

This section resolves the quadratic part of the analytic construction
at every odd order. It also proves the previously conjectural
identification with the algebraic maximizer in Section 53. The key is
to keep the noninteger poles in the finite-sum contour and match them
with the residues in a continued hyperbolic beta integral.

## 93.1 The Fourier evaluation

Let n be odd and at least 3, and use
\[
 d=\frac{n+\sqrt{n^2+4}}2,\quad \delta=-d^{-1},\quad
 A=d+1,\quad B=1+d^{-1},\quad
 \Omega=A+B=AB,\quad A-B=n.
\]
Here A and B are periods. Write the core matrices as
\(\mathsf A,\mathsf B\), where
\(\mathsf B=(\delta-1)\mathsf A\), to distinguish them
from these periods. Set
\[
 S(u)=\operatorname{Sin}_2(u;A,B),\qquad
 \gamma(u)=S(u)^{-1},\qquad F(z)=S(B+z).
\]
The phase formula is the one proved in Sections 75--77:
\[
 W_0=-1,\qquad
 W_a=-(-1)^{a(a+n)/2}\frac{F(a)}{\sqrt d}\quad(0<a<n).
\]
In particular \(F(0)=\sqrt d\), \(F(n-z)=F(z)^{-1}\),
and \(F(-a)=(-1)^{a+1}/F(a)\) at the nonzero integer samples.

For \(0<h<n\), define
\[
 \widehat{\mathsf B}_h(k)=
 \sum_{a=0}^{n-1}\mathsf B_{a,h}e^{-2\pi i ka/n},
 \qquad
 \omega_{h,k}\equiv\frac{2\pi k}{n}+\pi(h-1)\pmod{2\pi},
 \quad -\pi\le\omega_{h,k}\le\pi.
\]
The two endpoint choices, when present, give the same formula since
h is then even.

**Theorem.** Every one of these Fourier coefficients has the exact
evaluation
\[
 \boxed{
 \widehat{\mathsf B}_h(k)=-B e^{-ih\omega_{h,k}/2}
 \gamma\!\left(\frac{\Omega+h}{2}
                 -\frac{\Omega\omega_{h,k}}{2\pi}\right)
 \gamma\!\left(\frac{\Omega+h}{2}
                 +\frac{\Omega\omega_{h,k}}{2\pi}\right).
 }\tag{93.1}
\]
This is an evaluation of a finite sum, not a quadrature approximation.

## 93.2 The contour and the cancellation of every extra pole

Put \(\alpha=1/A\), \(\beta=1/B\); thus \(\alpha+\beta=1\).
Fix h and k and abbreviate \(\theta=2\pi k/n\),
\(\omega=\omega_{h,k}\). Define
\[
 R_h(z)=\frac{F(z)}{F(z-h)},\qquad
 K_h(z)=\frac{\pi e^{-i\omega z}}{\sin\pi z}R_h(z).
\]
The integer interpolation, including its exceptional value at zero,
gives for \(0\le a<n\)
\[
 \mathsf B_{a,h}+B\mathbf1_{a=h}
 =\frac{(-1)^{h(a+1)}}{\sqrt d F(h)}R_h(a).
 \tag{93.2}
\]
Consequently the residues of K at integers recover the Fourier sum
with precisely this one diagonal correction.

The sine shifts imply
\[
 \frac{R_h(z+n)}{R_h(z)}
 =\frac{\sin(\pi\alpha z)\sin(\pi\beta(z-h))}
        {\sin(\pi\beta z)\sin(\pi\alpha(z-h))}.
\]
The multiplier from the cosecant and exponential under the same
n-shift is \((-1)^h\). The elementary identity
\[
 (-1)^h\sin(\pi\alpha z)\sin(\pi\beta(z-h))
 -\sin(\pi\beta z)\sin(\pi\alpha(z-h))
 =\sin(\pi\alpha h)\sin\pi z
\]
therefore gives the meromorphic identity
\[
 \boxed{K_h(z+n)-K_h(z)
 =-4\pi\sin(\pi h/A)e^{-i\omega z}
       \gamma(-z)\gamma(z-h).}\tag{93.3}
\]
Here one uses
\(F(z)/(2\sin(\pi z/B))=-\gamma(-z)\) and
\(1/(2\sin(\pi(z-h)/A)F(z-h))=\gamma(z-h)\).

Let \(L=\lfloor h/B\rfloor\), and choose
\[
 \sigma=-\varepsilon,\qquad
 0<\varepsilon<\min\{1,(L+1)B-h\}.
\]
In the strip \(\sigma<\Re z<\sigma+n\), K has the integer
poles \(0,\ldots,n-1\) and exactly the additional poles
\[
 p_\ell=h-\ell B,\qquad 1\le\ell\le L.
\]
There are no numerator poles: the first pole of F is at
\(A>n\). All denominator zeros in this strip are the ones
just listed. Irrationality of B prevents coincidences.
Furthermore \(K_h(z+n)\) is regular at each \(p_\ell\).

The standard double-sine asymptotic, uniformly across this finite
strip, gives
\[
 |R_h(x+it)|=O(e^{-\pi h|t|/\Omega}).
\]
Thus both horizontal sides of the residue rectangle tend to zero:
\(|\omega|\le\pi<\pi(1+h/\Omega)\). This includes all
Fourier modes, even the endpoint mode when h is even.

Write
\[
 r_\ell=\operatorname*{Res}_{z=p_\ell}
     e^{-i\omega z}\gamma(-z)\gamma(z-h),
 \qquad p_0=h,
\]
and let \(I_\sigma\) be the integral of this gamma product along
\(\sigma+i\mathbb R\), with measure \(dz/i\). From (93.3),
the additional K residues are exactly
\(4\pi\sin(\pi h/A)r_\ell\). The rectangle therefore gives
\[
 \sum_{a=0}^{n-1}\operatorname*{Res}_{z=a}K_h(z)
 =-2\sin(\pi h/A) I_\sigma
  -4\pi\sin(\pi h/A)\sum_{\ell=1}^L r_\ell.
 \tag{93.4}
\]

The hyperbolic beta identity needed here is the two-gamma Fourier
integral, equation (2.17) of
[Belousov--Sarkissian--Spiridonov, *Complex binomial theorem and pentagon identities*](https://arxiv.org/html/2412.07562v2).
Specializing its parameters to \(f=-h\), the other shift equal to
zero, and its exponential parameter to
\((\Omega+h-\Omega\omega/\pi)/2\), gives
\[
 I_{\rm sep}=\sqrt\Omega\,e^{-ih\omega/2}\gamma(-h)
 \gamma\!\left(\frac{\Omega+h}{2}
                 -\frac{\Omega\omega}{2\pi}\right)
 \gamma\!\left(\frac{\Omega+h}{2}
                 +\frac{\Omega\omega}{2\pi}\right).
 \tag{93.5}
\]
The separating contour here means meromorphic continuation of the
usual separating contour. It is not the undeformed vertical line
when h is positive. First take \(|\omega|<\pi\), continue in h,
and then include the endpoints by continuity in the convergent
positive-h regime. Exactly the left-pole sequence
\(p_0,\ldots,p_L\) has crossed the line, so its correction is
\[
 I_{\rm sep}=I_\sigma+2\pi\sum_{\ell=0}^L r_\ell.
 \tag{93.6}
\]
No left and right poles coincide at the final integer h: such a
coincidence would express a positive integer less than A as a
nonnegative combination of A and B.

Substitution in (93.4) cancels every term with \(\ell\ge1\).
Only \(r_0\) remains. Since
\(\operatorname{Res}_{u=0}\gamma(u)=\sqrt\Omega/(2\pi)\),
\[
 r_0=\frac{\sqrt\Omega}{2\pi}e^{-i\omega h}\gamma(-h).
\]
Finally,
\[
 2\sin(\pi h/A)\gamma(-h)=(-1)^hF(h),\qquad
 \frac{\sqrt\Omega}{\sqrt d}=B.
\]
Multiplying the integer residue sum by
\((-1)^h/(\sqrt d F(h))\) gives the right side of (93.1)
plus \(B e^{-i\omega h}\). Because
\(e^{-i\omega h}=e^{-i\theta h}\), this last term cancels
exactly the diagonal correction in (93.2). This proves (93.1).

## 93.3 Reflection proves every quadratic column

The evaluated coefficients satisfy
\[
 \boxed{
 \widehat{\mathsf B}_h(k)
 \widehat{\mathsf B}_{n-h}(-k)
 =B^2e^{-2\pi i kh/n}.}\tag{93.7}
\]
Here is an explicit check of the phases and gamma shifts. It suffices
to take h odd and \(0\le k\le(n-1)/2\), since replacing h by
\(n-h\) and conjugating covers all cases. Write
\(\lambda=\Omega k/n\). Use \(\omega_h=2\pi k/n\)
and \(\omega_{n-h,-k}=\pi-2\pi k/n\). The first gamma
pair has arguments
\(x_\pm=(\Omega+h)/2\pm\lambda\); the other pair has
arguments
\[
 y_1=\Omega+(n-h)/2-\lambda,\qquad
 y_2=(n-h)/2+\lambda.
\]
Thus \(x_++y_1=\Omega+A\), \(x_-+y_2=A\).
Reflection and the A/B shifts reduce their product to
\[
 \frac{\sin\bigl(\pi[(h-n)/(2B)+Ak/n]\bigr)}
      {\sin\bigl(\pi[(\Omega+h)/(2A)-Bk/n]\bigr)}
 =(-1)^{(h-n)/2+k}.
\]
The two sine arguments, divided by pi, sum to
\((h-n+2)/2+k\). The denominator's argument lies strictly
between 0 and 1. The exponential prefactors in (93.1) then give
exactly (93.7).

Order-three symmetry gives
\(\mathsf B_{h,a}=\mathsf B_{a-h,n-h}\). Therefore the
Fourier transform, in g, of
\(\sum_a\mathsf B_{g+a,h}\mathsf B_{h,a}\)
is the left side of (93.7) multiplied by
\(e^{2\pi i kh/n}\). Fourier inversion proves
\[
 \sum_a\mathsf A_{g+a,h}\mathsf A_{h,a}
 =\mathbf1_{g=0}\qquad(h\ne0).
\]
The zero column follows directly from the fixed axes and
\(\delta^2=n\delta+1\). Consequently
\[
 \boxed{Q(g,h)=0\quad\text{for all }g,h\in\mathbb Z_n,
                 \text{ at every odd }n\ge3.}\tag{93.8}
\]

## 93.4 Identification with the convex center and algebraicity

Set \(u_a=\mathsf B_{a,1}\). Its coordinate signs and reflection
are exactly (53.2). For h=1, both gamma arguments in (93.1) lie
strictly between 0 and \(\Omega\), where gamma is positive.
Centering the Fourier transform as in Section 53 gives
\(\lambda_k=-(-1)^k\) times a strictly positive number.
Thus u is in the prescribed chamber \(\mathcal P_n\).

The proved quadratic column says that its circulant inverse has
the weighted reciprocal coefficients (53.7). These are precisely
the critical equations (53.6). Strict concavity from Section 53
therefore identifies u with its unique maximizer.
Reconstruction (53.8) identifies every analytic \(W_a\) with
the real algebraic phase: an odd-order real character gauge is
trivial. In particular,
\[
 \boxed{W_a\text{ and }F(a)\text{ are algebraic for every
 integer sample and every odd order}.}\tag{93.9}
\]
This proves algebraicity of these particular samples. It does not
identify their number fields with the conjectured ray fields or
prove the remaining Stark reciprocity assertions.

The independent script `hi_shintani_fourier.py` checks the finite
Fourier formula, the off-real shift identity, the extra-residue
cancellation, every quadratic, and both sets of chamber signs.
Its computations are numerical checks of the proof, not the proof
of uniformity. The saved 40-digit run covers orders 3, 5, 7, 9,
and 11, including a composite order and all modes in every column.
Its largest Q error is below \(8.5\times10^{-39}\), and its
largest scalar H error is below \(8.3\times10^{-40}\). It
completed in 67.9 seconds with peak RSS 26.01 MiB.
Cubic identities are not asserted by this section.

# 94. Canonical characteristic-two quadratic solutions at every odd order

The zero Fourier mode yields an additional convolution identity.
Together with algebraicity, it ensures that reduction modulo 2
is possible without losing any phase to a zero or a pole.

## 94.1 The exact convolution identity

For \(h\ne0\), let \(r\in\{1,\ldots,n-1\}\) satisfy
\(2r=h\pmod n\). Formula (93.1) at k=0 simplifies to
\[
 \sum_a\mathsf B_{a,h}=-\frac{B}{F(r)^2}.
 \tag{94.1}
\]
If h is odd, \(r=(n+h)/2\) and the two gamma arguments
are \(B+r\). If h is even, \(r=h/2\) and the arguments
are r and \(\Omega+r\). In the latter case
\[
 \gamma(r)\gamma(\Omega+r)
 =\frac{\gamma(r)}{\gamma(-r)}
 =\frac{(-1)^r}{F(r)^2};
\]
the phase in (93.1) cancels this sign.

For nonzero h the entire column, including its two special entries,
is \(\mathsf B_{a,h}=W_aW_{h-a}/W_h\).
Since \(F(r)^2=dW_r^2\), (94.1) becomes
\[
 \boxed{
 \sum_{a\in\mathbb Z_n}W_aW_{2r-a}
 =-\delta(\delta-1)\frac{W_{2r}}{W_r^2}
 \quad(r\in\mathbb Z_n).}\tag{94.2}
\]
The r=0 case also holds: its two sides are respectively
\(1+(n-1)\delta\) and \(\delta(\delta-1)\), equal by
the dimension equation. The script accompanying Section 93
independently checks both (94.1) and (94.2).

## 94.2 All phases are units above 2

**Theorem.** In any number field containing these analytic phases,
every \(W_a\) has valuation zero at every prime above 2.

**Proof.** Fix such a valuation v. The dimension equation shows
that delta is a unit. Its reduction satisfies
\(\bar\delta^2+\bar\delta+1=0\), so \(\delta-1\) is
also a unit. Put \(m=\min_a v(W_a)\). If m were negative,
choose r with \(v(W_r)=m\). Pair the summands in (94.2) by
\(a\leftrightarrow2r-a\). Because n is odd, the only
fixed summand is \(W_r^2\); all other pairs have a factor 2.
Their valuations are at least \(v(2)+2m>2m\). Hence the
left side has valuation exactly 2m, and the right side has
valuation \(v(W_{2r})-2m\). This forces
\(v(W_{2r})=4m<m\), a contradiction. Thus all valuations
are nonnegative. The norm equations
\(W_aW_{-a}=\delta\) for nonzero a, and \(W_0=-1\),
then make all of them zero. ∎

It follows as well that the double-sine samples \(F(a)\) are
units above 2. No conjecture about their fields is used here.

## 94.3 Uniform nonemptiness of the canonical Q scheme

Reduce at any prime above 2. All phase denominators and
\(\delta-1\) remain nonzero, so every equation (Q) remains
valid. In characteristic two, the paired convolution on the left
of (94.2) is just \(\overline W_r^2\), while
\(-\bar\delta(\bar\delta-1)=1\). Consequently
\[
 \boxed{\overline W_{2r}=\overline W_r^{\,4}
          \quad\text{for every }r.}\tag{94.3}
\]
Thus the canonical characteristic-two phase scheme defined by
the inverse norms, all Q, and Frobenius covariance is nonempty
at every odd order. If \(M=\operatorname{ord}_n(2)\), all
these phases lie in \(\mathbb F_{4^M}\): iterate (94.3).
This supplies the uniform nonemptiness that was missing from
the finite-field Q construction.

The cubic quotient of this finite scheme is a further condition.
Its nonemptiness is not a consequence of the argument above.
For example, at \(n=3^k\) the field-degree theorem of Section 65
now applies to a nonempty canonical Q scheme at every k, but it
does not prove positivity of the *full cubic* component count
\(b_k\) in Section 71.

One sufficient remaining lemma would be the uniform implication
\[
 \text{inverse norms + Q + }W_{2a}=W_a^4
 \quad\Longrightarrow\quad C
 \qquad\text{in characteristic two}.
 \tag{94.4}
\]
The finite checks of this implication do not prove it at unbounded
orders. If it is proved, Sections 58 and 94 immediately give
complex HI categories at every odd order. Alternatively, one
can prove C for the analytic candidate directly, or establish
the sufficient cubic error bound from Section 92; Q is now
exact and its error term can be set to zero. **The cubic step
and the requested infinitude remain unproved.**

## 94.4 The scalar H condition and the prime-order row field

The same convolution proves the scalar relation (55.1), without
assuming any cubic identity. Put \(t=\delta-1\),
\(s=\sum_a W_a\), and define
\[
 b_a=\frac{W_a^2}{W_{2a}}.
\]
For nonzero a, \(b_a=\mathsf B_{a,2a}\) and
\(b_ab_{-a}=\delta\). At zero, \(b_0=-1\), whereas
\(\mathsf B_{0,0}=\delta-2=b_0+t\). Summing (94.2),
using that doubling permutes the indices, gives
\[
 s^2=-\delta t\sum_a\frac1{b_a}.
\]
Retaining the zero correction in this reciprocal sum yields
\[
 \sum_a\frac1{b_a}
 =\frac{\sum_a\mathsf B_{a,2a}-2t}{\delta}.
\]
Therefore
\[
 \boxed{s^2+t\sum_a\mathsf B_{a,2a}-2t^2=0,}
 \qquad
 \boxed{S(W)^2+T(\mathsf A)=2.}\tag{94.5}
\]
This is exactly the scalar H condition of Section 55. Its validity
at the canonical center is now a theorem at every odd order.
The independent numerical verifier also checks (94.5).

In particular, Proposition 55.2 now gives an unconditional consequence
for the analytic candidate at every odd prime p: all phases lie in
their row field
\[
 \mathbb Q(\delta)(W_1,\ldots,W_{p-1})
 =\mathbb Q(\delta)(R_2,\ldots,R_{p-1}).
 \tag{94.6}
\]
Neither abelianity nor the conjectural ray conductor follows from
this equality. The individual values of S and T in the proposed
period-40 formula (55.5) are also still unproved.

There are now two algebraic completion statements whose hypotheses
are supplied uniformly: characteristic-two completion (94.4), or
the characteristic-zero implication from one quadratic column and
H to C discussed in Sections 55 and 57. Their finite certificates
do not prove either implication uniformly. **Infinitude still
requires a cubic completion argument.**

---

# 95. The convolution lift is unramified and realizes arithmetic Frobenius

The exact convolution identity has a further arithmetic consequence:
the phase field and its normal closure are unramified above 2, and
the fourth-power residue action lifts to literal doubling of the
characteristic-zero phase labels. This does not require a conjectural
identification of the phase field with a class field.

## 95.1 A strict contraction for the convolution equations

Put \(K=\mathbb Q(\delta)\), \(\lambda=\delta(\delta-1)\).
At the prime above 2, K has residue field \(\mathbb F_4\)
and is unramified over \(\mathbb Q_2\), because
\(X^2-nX-1\) reduces to the separable irreducible polynomial
\(X^2+X+1\). In particular lambda is a unit and reduces to 1.

Consider the n quartic equations in n variables
\[
 \mathscr H_r(X)=X_r^2\sum_a X_aX_{2r-a}
                   +\lambda X_{2r}=0,
 \qquad r\in\mathbb Z_n.
 \tag{95.1}
\]
Do not confuse these n convolution equations with the single scalar
H of Section 55. No norm, origin, Q, or C equation is included in
(95.1). Its reduction and Jacobian are especially simple:
\[
 \overline{\mathscr H}_r=X_r^4+X_{2r},\qquad
 \frac{\partial\overline{\mathscr H}_r}{\partial X_b}
 =\mathbf1_{b=2r}.
 \tag{95.2}
\]
Thus the Jacobian is a permutation matrix. On a doubling orbit of
length ell, the residue solutions are parametrized by
\(X^{4^\ell}=X\). There are exactly \(4^n\) geometric residue
tuples for (95.1), many of which fail the phase norms or Q.

There is an explicit lift, requiring no matrix inverse. In a complete
unramified integer ring whose residue field contains the tuple, define
\[
 (\mathcal T X)_{2r}
 =-\lambda^{-1}X_r^2\sum_a X_aX_{2r-a}.
 \tag{95.3}
\]
Start at any integral representatives of a residue solution of
(95.2), and iterate T. It preserves that residue tuple. If
\(X-Y\in2^s\mathcal O^n\), with \(s\ge1\), then
\[
 \mathcal T X-\mathcal T Y\in2^{s+1}\mathcal O^n.
 \tag{95.4}
\]
Indeed, for cyclic convolution,
\((Y+e)*(Y+e)-Y*Y=2Y*e+e*e\); coordinate squares have
the same estimate. Substituting both estimates in (95.3) proves
(95.4). Therefore the iteration converges to the unique solution
of (95.1) with those residues, gaining at least one binary digit
per step. This also directly realizes the simple-root lift in
(95.2).

The unramified ring with a specified finite residue extension exists
uniquely in this complete setting; this is the finite-etale
residue-field correspondence for henselian local rings.
[Stacks Project, Lemma 04GK](https://stacks.math.columbia.edu/tag/04GK).

Uniqueness also holds against an integral solution in a ramified
extension with the same residues. Normalize v by \(v(2)=1\),
and let \(s=\min_a v(X_a-Y_a)>0\). The same computation gives
\[
 \min_a v((\mathcal T X)_a-(\mathcal T Y)_a)
 \ge\min\{s+1,2s\}>s.
 \tag{95.5}
\]
Two distinct fixed points with the same residue would contradict
this strict improvement. This ramified comparison is needed in
the application to number fields; uniqueness only inside the
chosen unramified ring would not suffice.

## 95.2 Unramifiedness and the exact Frobenius action

Let \(E=K(W_0,\ldots,W_{n-1})\) be the analytic phase field
proved algebraic in Section 93. Fix any prime of E above 2.
Section 94 makes all phases integral units there. Their residues
satisfy (95.2), and (94.2) says the phases themselves satisfy
(95.1). The unramified lift from Section 95.1 and the ramified
uniqueness comparison (95.5) therefore identify the completed
phases with that unramified lift. Hence
\[
 \boxed{E/K\text{ is unramified at every prime above }2.}
 \tag{95.6}
\]

Let phi be arithmetic Frobenius over \(K_2\), so that its
residue action is \(x\mapsto x^4\). The two tuples
\[
 (\varphi(W_a))_a,\qquad (W_{2a})_a
\]
both solve (95.1). For the first, phi fixes delta and lambda;
for the second, reindex the convolution by the automorphism
\(a\mapsto2a\) of \(\mathbb Z_n\). They have the same
residues by (94.3), so uniqueness proves the exact identity
\[
 \boxed{\varphi(W_a)=W_{2a}\quad\text{in characteristic zero}.}
 \tag{95.7}
\]
Since all the right sides belong to E, this local Frobenius
restricts to an automorphism sigma of the global field E over K.
Its formula is independent of the chosen prime above 2, and its
order divides \(M=\operatorname{ord}_n(2)\).

There is a stronger normal-closure statement. Let L be the normal
closure of E over K. It is unramified above 2 as well: equivalently,
one can place all the conjugate tuples in unramified local extensions
and take their compositum. Unramifiedness is preserved in the normal
closure and composita.
[Stacks Project, Lemma 0EXR](https://stacks.math.columbia.edu/tag/0EXR).
For any chosen prime of L above 2, its arithmetic Frobenius satisfies
\[
 \varphi(\tau(W_a))=\tau(W_{2a})
 \qquad(\tau\in\operatorname{Gal}(L/K)),
 \tag{95.8}
\]
by precisely the same uniqueness argument applied to each conjugate
tuple. These conjugates generate L, so phi commutes with every
element of \(\operatorname{Gal}(L/K)\). Thus
\[
 \boxed{\operatorname{Frob}_{(2)}\text{ is a central element
 of }\operatorname{Gal}(L/K),\text{ of order dividing }M.}
 \tag{95.9}
\]
Here the Frobenius convention is explicitly the fourth-power
arithmetic convention. Centrality also makes its conjugacy class
a single element. It does not make the whole Galois group abelian.

For \(n=3^k\), Section 65 forces a canonical Q phase to have
residue degree \(M=2n/3\) over \(\mathbb F_4\). Consequently
sigma has exactly that order on E. If \(F=E^{\langle\sigma\rangle}\),
then \(E/F\) is cyclic of degree \(2n/3\), and the prime above
2 splits completely in \(F/K\). This supplies the predicted
doubling action and its full local degree on an unbounded family;
it does not identify F with the proposed class-field factor or
supply the missing cubic equations.

## 95.3 Exact lifting checks and the limit of the argument

`hi_convolution_hensel.py` performs exact arithmetic in
\((\mathbb Z/2^{24})[z]/f(z)\), using the irreducible residue
polynomials from the saved certificates. It independently verifies
irreducibility, lifts delta, iterates (95.3), and constructs arithmetic
Frobenius by lifting \(z^4\) to a root of f. It then checks
(95.7) and every norm, Q, and C equation.

For the known order-3 certificate and both order-9 certificates,
the contraction gains one binary digit at every step, and all
these equations vanish modulo \(2^{24}\). This is an exact
finite-precision calculation, not a proof that the lifted C
residuals vanish to every precision for arbitrary seeds.
The saved run, including the negative control, completed in
3.25 seconds with peak RSS 15.46 MiB.

The negative control has \(\overline W_0=1\) and
\(\overline W_a=\bar\delta^2\) for all nonzero a at order 3.
It satisfies the residue inverse norms and Frobenius covariance,
but fails Q. Its convolution iteration also converges and obeys
(95.7). Nevertheless, its lifted origin defect has valuation 2,
its norm defect has valuation 1, and its Q and C defects have
valuation 0. Thus the convolution lift alone cannot be used to
infer the other equations. This control does not refute (94.4),
whose full-Q hypothesis it fails.

What remains is a cubic completion theorem for the canonical
Q solutions supplied by Section 94. The exact Frobenius action,
unramifiedness, and finite-precision checks above do not replace
that theorem. **HI infinitude remains unproved.**

---

# 96. Diagonal completion fails without the phase hypothesis at infinitely many orders

The diagonal equivalence (71.2) holds for matrices, independently of
phase factorization. It cannot be extended to all cubics at that
level, even after imposing the generic transpose inverse products.
The following counterfamily proves this uniformly. It does not
refute the phase-specific completion conjecture (94.4).

## 96.1 An explicit matrix over the four-element field

Let p be a prime congruent to 7 modulo 8, and let chi be its
quadratic character, extended by \(\chi(0)=0\). Work over
\(\mathbb F_4\), with
\[
 \delta^2+\delta+1=0,\qquad t=\delta+1=\delta^2.
\]
Define
\[
 A_{0,0}=t,\qquad A_{g,0}=A_{0,g}=A_{g,g}=\delta\quad(g\ne0),
\]
and, when \(gh(h-g)\ne0\), put
\[
 \boxed{A_{g,h}=\delta+\frac{1-\chi(gh(h-g))}{2}.} \tag{96.1}
\]
Here the quotient by 2 is the integer 0 or 1, subsequently
mapped into the coefficient field. All entries are nonzero.

The cubic polynomial \(gh(h-g)\) is invariant under
\((g,h)\mapsto(-h,g-h)\), so A has the required order-three
symmetry. Since \(\chi(-1)=-1\), transposition interchanges
delta and t at every generic position. Thus
\[
 A_{g,h}A_{h,g}=1=\frac{\delta}{(\delta-1)^2}
 \quad(gh(h-g)\ne0).
\]
Also \(\chi(2)=1\), giving
\[
 A_{2g,2h}=A_{g,h}=A_{g,h}^4. \tag{96.2}
\]

## 96.2 Every quadratic holds

Fix \(h\ne0\), and define a binary sequence
\[
 D_h(m)=\mathbf1_{\chi(hm(m-h))=-1}.
\]
It vanishes at 0 and h and satisfies \(D_h(m)=D_h(h-m)\).
Writing \(E_{g,h}=A_{g,h}+\delta\), the definitions give
\[
 E_{h,m}=D_h(m),\qquad
 E_{m,h}=1+D_h(m)+\mathbf1_{m=0}+\mathbf1_{m=h}.
\]
The row and column sums of E therefore add to 1 in
characteristic two. Expansion of the required correlation yields
\[
 \sum_m A_{g+m,h}A_{h,m}=1+I(g,h),\qquad
 I(g,h)=\sum_m D_h(m)E_{m+g,h}. \tag{96.3}
\]
Reflection of D pairs the terms of its autocorrelation by
\(m\mapsto h-g-m\). The unique fixed label is \((h-g)/2\).
Consequently
\[
 I(g,h)=|D_h|+D_h((h-g)/2)+D_h(-g)+D_h(h-g)\pmod2. \tag{96.4}
\]
The quadratic-character sum of \(m(m-h)\) is -1, so
\[
 |D_h|=\frac{p-2+\chi(h)}2
       \equiv\frac{1+\chi(h)}2\pmod2.
\]
For \(g\ne0,\pm h\), the three character signs in the last
three terms of (96.4) are
\[
 -\chi(h)\chi(h-g)\chi(h+g),\quad
 \chi(h)\chi(g)\chi(h+g),\quad
 -\chi(h)\chi(g)\chi(h-g).
\]
Their product is \(\chi(h)\), so the parity of the number of
negative signs is \((1-\chi(h))/2\). It follows that I is 1.
At \(g=h\) or \(-h\), two of the three D terms vanish and
the remaining sign is \(\chi(2h^3)=\chi(h)\); again I is 1.
At \(g=0\), the supports of \(D_h(m)\) and \(E_{m,h}\)
are disjoint, giving I equal to zero. This proves Q for every
nonzero h.

For \(h=0\), the axis formula is
\(A_{m,0}=A_{0,m}=\delta+\mathbf1_{m=0}\), and direct
expansion gives \(\delta^2+\mathbf1_{g=0}\), as required.
Thus all quadratics hold. Equations (71.2) and (96.2) now prove
every diagonal cubic \(C(g,g,k,k)=0\) as well.

## 96.3 A nonempty, exactly counted family of failing cubics

For any normalized matrix satisfying Q, expansion along the
zero row gives, for \(h\ne0\),
\[
 C(0,h,k,l)=\delta\mathbf1_{l=0}
       +A_{-k,h}A_{h,l-k}-A_{l,k}A_{h+k,l}. \tag{96.5}
\]
Choose b such that
\[
 \chi(b)=1,\qquad \chi(b+1)=-1,\qquad \chi(b+2)=1. \tag{96.6}
\]
Then \(b,b+1,b+2\) are all nonzero, and (96.1) gives
\[
 A_{-b,1}=A_{1,2}=\delta,\qquad
 A_{b+2,b}=A_{b+1,b+2}=t.
\]
Hence
\[
 \boxed{C(0,1,b,b+2)=\delta^2+t^2=1.} \tag{96.7}
\]

There are exactly \((p+1)/8\) choices of b. Indeed, eight
times their number is
\[
 \sum_x(1+\chi(x))(1-\chi(x+1))(1+\chi(x+2)).
\]
The expression vanishes at \(0,-1,-2\), so no exceptional
correction is needed. The single-character sums vanish; each
of the three distinct two-factor character sums is -1, and
their signed combination is 1. The three-factor sum is zero:
after \(u=x+1\), its polynomial is \(u^3-u\), and the
terms at u and -u cancel because \(\chi(-1)=-1\).
The resulting count is \((p+1)/8>0\).

For completeness, primes congruent to 7 modulo 8 are unbounded
without needing an analytic prime-distribution theorem. If there
were only finitely many, choose a positive even integer a divisible
by all of them. Every prime divisor q of \(2a^2-1\) has
2 as a quadratic residue, since \((2a)^2\equiv2\pmod q\),
and therefore is 1 or 7 modulo 8. Their product, including
multiplicities, is 7 modulo 8, so at least one is 7 modulo 8.
None of the old primes divides \(2a^2-1\), a contradiction.
This is an infinite family of counterexamples to a proposed
matrix implication, not an infinite family of HI categories.

## 96.4 The missing phase factorization is visible in four entries

Patch the core to the would-be phase cocycle by setting
\[
 \beta(a,b)=tA_{a,a+b}\quad(a+b\ne0),\qquad
 \beta(a,-a)=\delta\quad(a\ne0),\qquad \beta(0,0)=1.
\]
If phases existed, this would equal \(W_aW_b/W_{a+b}\),
and would satisfy the cocycle law. For each b in (96.6), however,
\[
 \beta(1,1)\beta(2,b)=1,\qquad
 \beta(1,b)\beta(1,b+1)=\delta^2\ne1. \tag{96.8}
\]
Thus no extension of the coefficient field can supply the phase
factorization. This distinction is necessary: Section 94 already
constructs actual phase solutions of Q and Frobenius at every
odd order, whereas (96.1) does not belong to that phase space.

The saved `hi_char2_paley_matrix.py` verifier checks every Q,
every diagonal C, the matrix symmetries and products, every
witness in (96.6), and the failure (96.8) at
\(p=7,23,31,47,71,79,103\). Its existing result file reports
completion in 0.291 seconds with peak RSS 14.44 MiB. These
finite checks support the hand proof above; the proof, rather
than extrapolation of the checks, establishes the uniform statement.

---

# 97. Boundary cubics characterize the phase cocycle and recover its canonical gauge

The obstruction in Section 96 has an exact converse. It also
clarifies why associativity of the ordinary phase cocycle cannot
by itself prove the remaining interior cubics: that associativity
is already encoded by the boundary part of the system.

Let k be a field of characteristic two containing delta, with
\(\delta^2+\delta+1=0\), and let \(G=\mathbb Z_n\), n odd.
Assume A satisfies the fixed origin and axes of Section 96,
order-three symmetry, every Q, and
\[
 A_{g,h}A_{h,g}=1\quad(gh(h-g)\ne0).
\]
Define the nonzero patched values beta as in Section 96.4.
In particular \(\beta(a,0)=\beta(0,a)=1\).

## 97.1 The zero-index cubics are exactly the cocycle equations

Under these hypotheses the following are equivalent:

1. \(C(0,h,k,l)=0\) for all \(h\ne0\) and all k,l.
2. \(\beta(a,b)\beta(a+b,c)=\beta(b,c)\beta(a,b+c)\)
   for all a,b,c.
3. Over an algebraic extension of k there are nonzero phases with
   \(W_0=1\), \(W_aW_{-a}=\delta\) for \(a\ne0\), and
   \(\beta(a,b)=W_aW_b/W_{a+b}\).

Here the phase identity reconstructs precisely the normalized
matrix A, with its stated exceptional entries.

To prove the first equivalence, use (96.5). For
\(a+b\ne0\), \(b+c\ne0\), and \(a+b+c\ne0\),
set
\[
 h=a+b,\qquad k=-a,\qquad l=b+c.
\]
Order-three symmetry gives
\(A_{b+c,-a}=A_{a,a+b+c}\), so the cocycle residual is exactly
\[
 \begin{split}
 &\beta(a,b)\beta(a+b,c)-\beta(b,c)\beta(a,b+c)\\
 &\hspace{18mm}=t^2 C(0,a+b,-a,b+c). \tag{97.1}
 \end{split}
\]
All exceptional cases of the cocycle law are automatic from
the already imposed matrix conditions. A zero individual label
uses normalization. If \(a+b=0\), the nontrivial case reduces to
\[
 \beta(-a,c)\beta(a,c-a)
       =t^2 A_{c,a}A_{a,c}=\delta,
\]
using order-three symmetry and the generic inverse product;
the cases \(c=0,a\) use the patched values directly.
If \(b+c=0\), the corresponding product is directly
\(t^2 A_{a,a+b}A_{a+b,a}=\delta\), with the same elementary
exceptions. If only \(a+b+c=0\), both sides reduce to delta
times the equality \(\beta(a,b)=\beta(b,c)\), which is
order-three symmetry.

Conversely, the cocycle law and (97.1) give every zero-index
cubic with \(l\ne0\) and \(l-k\ne0\). If \(l=k\ne0\),
(96.5) vanishes by
\(A_{-k,h}=A_{h+k,k}\) and the fixed diagonal and axis entries.
If \(l=0\), its two products are 1 and t in the generic case,
or t and 1 when \(k=0\) or \(k=-h\). In each case the
additional delta makes the residual zero. This completes both
directions including all exceptional indices.

For the phase reconstruction, choose u in an algebraic extension
with
\[
 u^n=\prod_{j=0}^{n-1}\beta(j,1),\qquad
 W_0=1,\qquad W_{j+1}=W_j u/\beta(j,1).
\]
The product condition makes \(W_n=W_0\). The cocycle law,
inductively in the second label, proves
\(\beta(a,b)=W_aW_b/W_{a+b}\). The patched value
\(\beta(a,-a)=\delta\) gives every inverse norm. Conversely
a quotient of this form always obeys the cocycle law. This is
an elementary cyclic-group reconstruction; no categorical
existence assertion is used in it.

## 97.2 Frobenius removes the root choice and descends the phases

Assume in addition \(A_{2a,2b}=A_{a,b}^4\). The patched beta
then satisfies
\(\beta(2a,2b)=\beta(a,b)^4\), including the exceptional
indices. If any of the equivalent conditions in Section 97.1
holds, the reconstructed phase sequence has
\(r(a)=W_a^4/W_{2a}\) a character. As in Section 71, twisting
by \(r(a)^{-(n+1)/2}\) gives the unique phase representative
with \(W_{2a}=W_a^4\).

The resulting phases have an explicit formula involving only A:
\[
 \boxed{
 W_0=1,\qquad
 W_a=\beta(a/2,a/2)^{-2}
     =tA_{a/2,a}^{-2}\quad(a\ne0).
 } \tag{97.2}
\]
Indeed, in the canonical gauge,
\(\beta(r,r)=W_r^2/W_{2r}=W_r^{-2}\). Substituting
\(r=a/2\) proves (97.2), and \(t^{-2}=t\) supplies its
matrix form. Thus these phases lie in k itself, even though
the preliminary reconstruction used an nth root in an extension.
Uniqueness also follows directly: the ratio of two phase lifts
is a character eta, while canonical covariance forces
\(\eta(a)^4=\eta(2a)=\eta(a)^2\), hence \(\eta(a)=1\).

Consequently the remaining characteristic-two completion question
can equivalently be stated entirely in matrix terms:
\[
 \begin{gathered}
 Q+\text{normalized symmetry and inverse products}
   +\text{Frobenius covariance}+\text{zero-index cubics}\\
 \stackrel{?}{\Longrightarrow}\text{all cubics}.
 \end{gathered} \tag{97.3}
\]
Section 94 supplies points satisfying the hypotheses at every odd
order. Section 96 shows why dropping the zero-index cubics from
this formulation is invalid. Neither theorem proves (97.3).
In particular the ordinary algebra with multiplication
\(e_a e_b=\beta(a,b)e_{a+b}\) is already associative for
every phase candidate, before Q is imposed; its associativity
cannot be substituted for the missing HI pentagons.
**Existence of HI categories for infinitely many orders is still
unproved.**

---

# 98. Exact Frobenius puts every phase in one row field at every odd order

The prime-order descent in Section 55 used the scalar H condition.
The central Frobenius theorem of Section 95 now supplies a different
argument valid at every odd order, including composite orders. It
uses the canonical analytic Q solution, but does not assume its
cubic equations or any class-field identification.

Retain the characteristic-zero notation of Sections 93--95:
\[
 K=\mathbb Q(\delta),\quad \delta=-d^{-1},\quad
 E=K(W_1,\ldots,W_{n-1}),\quad
 M=K(A_{g,h}:g,h\in\mathbb Z_n).
\]
Let L be the normal closure of E over K. Section 95 proves that
L is unramified above 2 and that its arithmetic Frobenius sigma
over K is central, with
\[
 \sigma(W_a)=W_{2a}. \tag{98.1}
\]
The base residue field at 2 is \(\mathbb F_4\), because
\(X^2-nX-1\) reduces to \(X^2+X+1\).

## 98.1 The character ambiguity is incompatible with central Frobenius

Take any \(\tau\in\operatorname{Gal}(L/M)\), and set
\[
 \chi(a)=\frac{\tau(W_a)}{W_a},\qquad \chi(0)=1.
\]
Since tau fixes the matrix and delta, the phase formula gives
\(\chi(a)\chi(b)=\chi(a+b)\) when \(a+b\ne0\).
When \(a+b=0\), the same equation follows from the inverse
norms. Thus chi is a cyclic character, and
\[
 \chi(a)^n=1. \tag{98.2}
\]

Arithmetic Frobenius acts on every odd-order root of unity in L
by its fourth power. This assertion also follows directly from
unramifiedness: reduction gives that fourth power, and the roots
of \(X^n-1\) have distinct reductions at 2, since n is odd.
Consequently centrality and (98.1) give two evaluations:
\[
 \begin{split}
 \sigma\tau(W_a)&=\chi(a)^4 W_{2a},\\
 \tau\sigma(W_a)&=\chi(2a)W_{2a}=\chi(a)^2 W_{2a}.
 \end{split}
\]
All phases are nonzero, so \(\chi(a)^2=1\). Together with
(98.2) and odd n this forces \(\chi(a)=1\). Every element of
\(\operatorname{Gal}(L/M)\) therefore fixes all phases.
The Galois correspondence gives
\[
 \boxed{E=M\quad\text{at every odd }n\ge3.} \tag{98.3}
\]
This is an exact global descent, not merely equality of residue
fields or of completions at 2.

There is also a direct check using the contraction, without
invoking centrality a second time. Fix a prime of L above 2.
Both W and \(\tau(W)\) are integral unit tuples solving
the quartic system (95.1), so their reductions obey canonical
Frobenius covariance. Since tau fixes B, for every nonzero a
both reductions have the same forced value
\[
 \overline W_a=\overline{B_{a/2,a}}^{-2}
              =\overline{\tau(W_a)}.
\]
Their origins agree as well. Uniqueness of the convolution lift
with a prescribed reduction, including the ramified case proved
in Section 95.1, now implies \(\tau(W)=W\). This gives the
same global descent by the Galois correspondence. In particular,
coincidence of the reductions is used together with the exact
contraction equations; it is not alone being used to infer
equality of algebraic numbers.

More generally, the same proof applies whenever a central
automorphism acts on a cyclic phase tuple by label multiplication
by r, acts on its possible character values by their qth powers,
and \(\gcd(n,q-r)=1\). A matrix stabilizer character must then
have both its nth and its \((q-r)\)th powers equal to 1.
Here \((q,r)=(4,2)\), so the coprimality holds uniformly for
odd n. Merely having a label-doubling automorphism would not
suffice: its arithmetic action on character values and its
centrality are both used.

## 98.2 One row generates the same field

For completeness, the equality with a single row uses only the
cyclic phase parametrization. Set
\[
 R_j=B_{1,j}\quad(2\le j<n),\qquad
 P_1=1,\qquad P_j=\prod_{s=2}^{j}R_s.
\]
The recursion \(R_j=W_1W_{j-1}/W_j\) gives
\[
 W_j=\frac{W_1^j}{P_j},\qquad
 W_1^n=\delta P_{n-1}. \tag{98.4}
\]
For integer representatives \(0<g,h<n\), the generic core
entries are consequently
\[
 B_{g,h}=
 \begin{cases}
 P_h/(P_gP_{h-g}),&g<h,\\[2mm]
 \delta P_{n-1}P_h/(P_gP_{n+h-g}),&g>h.
 \end{cases} \tag{98.5}
\]
All remaining entries are fixed constants in K. Thus the full
matrix field is the row field, and (98.3) strengthens this to
\[
 \boxed{
 K(W_1,\ldots,W_{n-1})
 =K(A_{g,h}:g,h\in\mathbb Z_n)
 =K(R_2,\ldots,R_{n-1}).
 } \tag{98.6}
\]
In particular the nth-root ambiguity in (98.4) introduces no
field extension for the canonical analytic candidate. This
does not provide a universal rational expression of bounded
degree for that root, nor assert that arbitrary phase trials
enjoy the same descent.

The one-column reality theorem of Section 54 also has an immediate
consequence: every K-embedding of E into the complex numbers over
the chosen negative-dimension real embedding has real image,
because it is generated by a row solving that real critical
algebra. This is a statement over that embedding of K; no
reality assertion at the other dimension embedding is inferred.

Equations (98.3)--(98.6) concern the fields of the uniformly
constructed Q solution. They do not prove the remaining cubic
completion (94.4) or (97.3), and do not establish HI infinitude.

---

# 99. Norm obstructions in the convolution lift and a two-update completion target

This section examines what the exact convolution system contributes
beyond its automatic Frobenius reduction. The resulting identities
are uniform. The completion tests at the end are finite statements.
Section 101 subsequently disproves the all-odd-order version without
Q; the version retaining all Q remains unproved.

Write \(t=\delta-1\), \(\lambda=\delta t\), and retain
the update
\[
 (\mathcal T X)_{2r}=-\lambda^{-1}X_r^2(X*X)_{2r}.
\]

## 99.1 Q makes one convolution update preserve the inverse norms

First work in characteristic zero, or in a coefficient ring where
delta and t are units. Suppose \(X_0=-1\) and
\(X_aX_{-a}=\delta\) for nonzero a. Let A be its normalized
phase matrix, and let \(Q_X(g,h)\) denote the quadratic residual,
without assuming that it vanishes. Set \(S=X*X\).

For \(h\ne0\), the phase formula and order-three symmetry give
\[
 \sum_a B_{a,h}=S_h/X_h,\qquad
 \sum_a B_{h,a}=S_{-h}/X_{-h}.
\]
Summing Q over its first index therefore gives
\[
 \sum_g Q_X(g,h)=\frac{S_hS_{-h}}{\delta t^2}-1.
\]
On the other hand, the inverse norm at \(h/2\) yields
\((\mathcal T X)_h(\mathcal T X)_{-h}=S_hS_{-h}/t^2\).
Thus, with no Q or C assumption,
\[
 \boxed{
 (\mathcal T X)_h(\mathcal T X)_{-h}-\delta
       =\delta\sum_g Q_X(g,h)\qquad(h\ne0).
 } \tag{99.1}
\]
Also \(S_0=1+(n-1)\delta=\lambda\), so
\((\mathcal T X)_0=-1\). In particular every full-Q phase
tuple is sent to an inverse-normalized tuple by one update.
This does not show that its updated tuple still satisfies Q:
only the zero Fourier modes appear in (99.1).

## 99.2 The origin error is forced to have one extra binary digit

Let Y be the unique integral convolution lift of any inverse-normalized
canonical residue tuple w, as in Section 95. It need not satisfy
Q or the inverse norms after lifting. Put
\[
 \xi=Y_0+1,\qquad \nu_a=Y_aY_{-a}-\delta\quad(a\ne0).
\]
Choose one representative of each nonzero pair \(\{a,-a\}\).
Since \(Y_0\) is a unit, its convolution equation is
\(Y_0(Y*Y)_0+\lambda=0\). Substitution of the norm defects
and \(\lambda=1+(n-1)\delta\) gives the exact relation
\[
 \boxed{
 \xi\,[\lambda+Y_0(Y_0-1)]
      =-2Y_0\sum_{a\bmod\pm1}\nu_a.
 } \tag{99.2}
\]
The bracket is a unit above 2. With \(v(2)=1\), this proves
\[
 v(\xi)\ge1+\min_{a\ne0}v(\nu_a). \tag{99.3}
\]
In particular the origin is correct modulo 4 for every such lift.
If all inverse norms hold exactly, then the origin is exactly -1.
Thus the origin imposes no separate obstruction once the inverse
norms have been established in the canonical residue branch.

## 99.3 An explicit quartic is the first norm obstruction

Let \(\omega=\bar\delta\), \(c=\omega^2=\omega+1\),
and let w be any tuple over a characteristic-two field with
\[
 w_0=1,\qquad w_aw_{-a}=\omega\quad(a\ne0),\qquad
 w_{2a}=w_a^4.
\]
It lies in a finite field by the last identity. Define
\[
 U_h(w)=\sum_{\substack{\{a,b\}\subset\mathbb Z_n\\a\ne b,\ a+b=h}}
                   w_aw_b,
 \qquad \epsilon_n=\frac{n-1}{2}\pmod2.
\]
Each unordered pair is counted once. For \(h=2r\ne0\), put
\[
 \boxed{
 \mathcal O_{2r}(w)
   =c+\epsilon_n\omega
       +c\bigl(w_r^2U_{-2r}(w)+w_{-r}^2U_{2r}(w)\bigr).
 } \tag{99.4}
\]
Then the first norm obstruction of the unique convolution lift Y
is exactly
\[
 \boxed{
 \mathcal O_h(w)=\overline{\frac{Y_hY_{-h}-\delta}{2}}.
 } \tag{99.5}
\]
Division by 2 here is performed on an integral norm defect before
reduction; it is not division in the residue field.

To prove the formula, choose an arbitrary integral lift X with
\(X_0=-1\) and all inverse norms exact. Such a lift exists by
choosing one unit in each opposite pair and setting the other
equal to delta divided by it. Contraction implies
\(Y\equiv\mathcal T X\pmod4\). Write
\[
 S_{2r}=X_r^2+2\widetilde U_{2r},\qquad
 S_{-2r}=X_{-r}^2+2\widetilde U_{-2r},
\]
where each \(\widetilde U\) is the same unordered sum on X.
Using the norm calculation in Section 99.1 gives
\[
 \frac{Y_{2r}Y_{-2r}-\delta}{2}
 \equiv t^{-2}\left[
 \delta^2\left(\frac{n+3}{2}-\delta\right)
 +X_r^2\widetilde U_{-2r}+X_{-r}^2\widetilde U_{2r}
 \right]\pmod2.
\]
Here the constant follows from
\(\delta^2-\delta t^2=\delta^2(n+3-2\delta)\).
Reduction, using \(\bar t^{-2}=c\) and
\((n+3)/2\equiv\epsilon_n\pmod2\), gives (99.4).
This also proves independence from the choice of X.

The obstructions satisfy
\[
 \mathcal O_{-h}=\mathcal O_h,\qquad
 \mathcal O_{2h}=\mathcal O_h^4. \tag{99.6}
\]
The second identity follows by doubling every unordered pair in U.
It therefore suffices to impose one quartic per doubling orbit
modulo negation. At \(n=3^k\) this is just k quartic equations.
Their vanishing is equivalent to preserving all inverse norms
modulo 4. It is not asserted to imply Q or C uniformly.

## 99.4 Exact finite tests, including a counterexample at order 15

`hi_convolution_norm_obstruction.py` first exhausts all norm/Frobenius
tuples at orders 3,5,7,9, verifies (99.3)--(99.5) on every tuple,
and lifts each one modulo \(2^8\). The complete run takes 2.86
seconds with peak RSS 17.11 MiB. A second mode evaluates (99.4)
first, then checks every Q and the lift of each survivor. It
exhausts every odd order through 17 in 18.37 seconds, with peak
RSS 15.94 MiB. All finite-field defining polynomials are independently
checked for irreducibility, and the seed subgroup generators have
their exact orders verified.

| n | All norm/Frobenius tuples | Norms preserved modulo 4 | Norms preserved modulo 8 | Full Q/C points |
|---:|---:|---:|---:|---:|
| 3 | 5 | 2 | 2 | 2 |
| 5 | 17 | 4 | 4 | 4 |
| 7 | 63 | 6 | 6 | 6 |
| 9 | 325 | 12 | 12 | 12 |
| 11 | 1025 | 12 | 12 | 12 |
| 13 | 4097 | 12 | 12 | 12 |
| 15 | 21675 | 32 | 24 | 24 |
| 17 | 66049 | 16 | 16 | 16 |

Every survivor modulo 8 passes all residue Q. The complete
canonical Q/C classifications in Sections 70 and 72 identify
these sets with the full Q/C sets at the listed orders. This
uses the existing finite cubic theorems, not an unproved uniform
Q-to-C implication. All of these true points also preserve the
norms through the tested precision \(2^8\).

At order 15 there are eight false points passing (99.4). One is
given in the binary polynomial model
\[
 \mathbb F_{256}=\mathbb F_2[z]/(z^8+z^6+z^5+z^4+z^3+z+1),
 \qquad \omega=z^6+z^5+z^3+z^2,
\]
by the following binary coefficient encodings:
\[
 (w_0,\ldots,w_{14})=
 (1,126,127,230,126,127,83,126,127,70,126,127,159,126,127).
\]
It has \(Q(1,1)=\omega\ne0\), although every first norm
obstruction vanishes. Its exact lift has minimum norm-defect
valuation 2 and origin-defect valuation 3; the nonzero coefficient
at that precision certifies these valuations for the full lift.
Thus preservation modulo 4 cannot be used as a uniform completion
criterion. The next digit rejects all eight false order-15 points.

There is also a characteristic-zero ideal check. The program
`hi_convolution_ideal.py` fixes \(W_0=-1\), imposes every
inverse norm and every quartic convolution equation, and reduces
all nontrivial Q polynomials by the resulting exact Groebner
basis over \(\mathbb Q(\delta)\). At orders 3,5,7 the ideal
has length 2,4,6 respectively, and every Q reduces to zero.
The existing characteristic-zero Q-to-C theorems then supply C
at these three finite orders. The bounded order-9 computation
times out after 20 seconds without a basis or implication result;
it is not included in this finite ideal theorem.

## 99.5 The second-digit test is explicit and its hypotheses exist uniformly

The test modulo 8 does not require an unbounded iteration. Choose
any inverse-normalized lift X of w in the unramified coefficient
ring modulo 8, with origin -1 and the prescribed lift of delta.
The contraction gives
\[
 \mathcal T^2X\equiv Y\pmod8. \tag{99.7}
\]
Thus checking inverse norms on \(\mathcal T^2X\) modulo 8 is
independent of every lift choice and involves just two explicit
convolution updates. The dimension lift depends on n modulo 8
and the specified root omega; there is no unspecified phase choice.

For the analytic candidate of Sections 93--95, all norms and
convolution equations hold exactly. Its reduction consequently
passes this test at every odd order. A new sufficient uniform
completion statement is therefore
\[
 \boxed{
 \begin{gathered}
 w_0=1,\quad w_aw_{-a}=\omega\ (a\ne0),\quad w_{2a}=w_a^4,\\
 (\mathcal T^2X)_a(\mathcal T^2X)_{-a}
          \equiv\delta\pmod8\quad(a\ne0)
 \quad\Longrightarrow\quad C(w)=0.
 \end{gathered}
 } \tag{99.8}
\]
This implication holds at the finite orders in the table and in
Section 100. Section 101 disproves it as an all-odd-order statement.
Proving it on some unbounded subsequence would still suffice by
the analytic reductions and Section 58. It also suffices for the goal
to prove (99.8) with all Q equations added to its hypotheses:
Section 94 already supplies Q uniformly. The stronger formulation
without Q is motivated by the finite census and need not be
proved in order to establish infinitude. A characteristic-zero alternative
is to prove that exact inverse norms and the quartic convolution
imply C; its finite ideal evidence is restricted to 3,5,7 above.
Completion with residue Q, or with exact characteristic-zero norms,
has not been proved uniformly.
**Infinitude remains unproved.**

---

# 100. The finite etale convolution algebra and an equivalent cubic ideal target

The convolution lift can be studied as a finite algebra, including all
its components rather than only one chosen phase tuple. This gives an
exact polynomial formulation of (99.8). The algebra theorem and the
equivalence are uniform; the ideal containments themselves are proved
only at the finite orders specified below. Section 101 shows that the
containments without residue Q fail at some larger orders.

## 100.1 The whole convolution algebra has rank \(4^n\)

Let n be odd and at least 3, and put
\[
 \mathcal O=\mathbb Z_2[\delta],\qquad
 \delta^2-n\delta-1=0,\qquad \lambda=\delta(\delta-1).
\]
This is the unramified quadratic integer ring, with residue field
\(\mathbb F_4\). In particular lambda is a unit and reduces to 1.
Use variables \(X_a\) for every \(a\in\mathbb Z_n\), including 0,
and define
\[
 \mathscr H_r=X_r^2\sum_a X_aX_{2r-a}+\lambda X_{2r},
 \qquad
 \mathcal A_n=\mathcal O[X_a:a\in\mathbb Z_n]/(\mathscr H_r:r\in\mathbb Z_n).
\]
Then
\[
 \boxed{\mathcal A_n\text{ is finite etale and free of rank }4^n
        \text{ over }\mathcal O.} \tag{100.1}
\]
An \(\mathcal O\)-basis is given by the monomials
\(\prod_aX_a^{e_a}\) with \(0\le e_a<4\).
No norm, origin, Q, or C equations are assumed in this statement.

Here is a finiteness argument that also rules out components escaping
the special fiber. Write
\(F_r=X_r^2\sum_aX_aX_{2r-a}\) for the homogeneous quartic part.
Pairing a with \(2r-a\) gives \(\bar F_r=X_r^4\).
Set \(D=3n+1\). Every monomial of degree D is divisible by some
\(X_r^4\), so the multiplication map
\[
 \bigoplus_r\mathcal O[X]_{D-4}\longrightarrow\mathcal O[X]_D,
 \qquad (f_r)_r\longmapsto\sum_r f_rF_r
\]
is surjective modulo 2. Its cokernel is a finite module over the local
ring \(\mathcal O\); Nakayama's lemma makes the map surjective over
\(\mathcal O\). In \(\mathcal A_n\), replacing
\(F_r\) by \(-\lambda X_{2r}\) consequently reduces every
degree-D monomial to degree \(D-3\). Factoring off a degree-D
monomial and inducting reduces every polynomial to degree at most
3n. Thus \(\mathcal A_n\) is a finite \(\mathcal O\)-module.

The Jacobian of the n equations is \(\lambda P+2R(X)\), where
P is the permutation matrix for doubling the label. Since 2 lies in
the Jacobson radical of the finite algebra, the determinant is a
unit. The square Jacobian criterion makes the algebra etale: the
standard smooth presentation has zero relative dimension. See the
[standard smooth criterion, Definition 10.137.5 and Lemma 10.137.6](https://stacks.math.columbia.edu/tag/00T1).
It follows that the finite algebra is free over the local base.
Modulo 2 the polynomials \(X_r^4+X_{2r}\) have pairwise coprime
leading monomials in a degree order. Their standard monomials give
dimension \(4^n\). Nakayama's lemma and freeness lift precisely
that monomial basis to \(\mathcal O\), proving (100.1).

Let \(M=\operatorname{ord}_n(2)\), and let \(\mathcal O'\)
be the unramified extension of \(\mathcal O\) with residue field
\(\mathbb F_{4^M}\). Each doubling cycle of length ell contributes
\(4^\ell\) solutions of \(w_{2a}=w_a^4\), including zero values;
all coordinates of every solution lie in this residue field. The
[classification of finite etale algebras over a henselian local ring](https://stacks.math.columbia.edu/tag/04GK)
therefore gives
\[
 \boxed{
 \mathcal A_n\otimes_{\mathcal O}\mathcal O'
  \simeq \prod_{w:\,w_{2a}=w_a^4}\mathcal O'.
 } \tag{100.2}
\]
There are \(4^n\) factors. The coordinate map on the factor w is
evaluation at its unique integral convolution lift \(Y(w)\) from
Section 95. This identifies the contraction with the splitting of a
finite algebra.

## 100.2 Imposing norms leaves explicit torsion factors

In \(\mathcal A_n\), let
\[
 J=(X_0+1,\ X_aX_{-a}-\delta\ (a\ne0)).
\]
For a residue tuple satisfying the normalized origin and inverse
norms, write
\[
 s_w=\min_{a\ne0}v_2\bigl(Y_a(w)Y_{-a}(w)-\delta\bigr),
 \qquad v_2(2)=1.
\]
Here \(s_w\) is a positive integer or infinity. On its factor in
(100.2), the ideal generated by the norm defects is
\((2^{s_w})\), with \((2^\infty)=(0)\).
Equation (99.3) puts the origin defect in the same ideal, and even
in \((2^{s_w+1})\). On every other residue factor, at least one
origin or norm generator is a unit. Hence
\[
 \boxed{
 (\mathcal A_n/J)\otimes_{\mathcal O}\mathcal O'
 \simeq
 \prod_{\substack{w_0=1,\ w_aw_{-a}=\bar\delta\ (a\ne0)\\
                   w_{2a}=w_a^4}}
        \mathcal O'/(2^{s_w}).
 } \tag{100.3}
\]

In particular the norm quotient need not be flat. Its generic fiber
retains exactly the factors with \(s_w=\infty\). Counting tuples
passing norms modulo \(2^k\) gives an upper bound for the number
of geometric characteristic-zero norm/convolution solutions, but a
finite-precision pass alone does not establish exact norms.

## 100.3 The factor-four ideal containment is exactly the modulo-8 test

Work now over
\[
 R_8=(\mathbb Z/8)[\delta]/(\delta^2-n\delta-1),\qquad t=\delta-1,
\]
and in \(R_8[X_a:a\in\mathbb Z_n]\) set
\[
 I_8=(\mathscr H_r\ (r\in\mathbb Z_n),\ X_0+1,
                 \ X_aX_{-a}-\delta\ (a\ne0)).
\]
Define a polynomial core, with its exceptional entries fixed, by
\[
 D_{g,h}=\begin{cases}
 \delta(\delta-2),&g=h=0,\\
 -\delta,&g=0\text{ or }h=0\text{ or }g=h,\quad(g,h)\ne(0,0),\\
 X_gX_{h-g}X_{-h},&\text{otherwise}.
 \end{cases}
\]
Modulo the origin and norm equations this is \(D=\delta t A\).
For every quadruple of indices put
\[
 \begin{split}
 P^C_{g,h,k,l}={}&
 \sum_mD_{m,g+h}D_{g,m+k}D_{h,m+l}\\
 &-\delta tD_{g+l,k}D_{h+k,l}
       +\delta^2t^3\mathbf1_{g=h=0}.
 \end{split} \tag{100.4}
\]
Thus \(P^C=(\delta t)^3C\) in that quotient; the multiplier
\(\delta t\) is a unit. For fixed n,
\[
 \boxed{\text{The implication (99.8) holds}
 \quad\Longleftrightarrow\quad
 4P^C_{g,h,k,l}\in I_8\text{ for every }g,h,k,l.}
 \tag{100.5}
\]

Indeed, base change to \(\mathcal O'/8\) is faithfully flat.
By (100.3) the quotient by \(I_8\) becomes the product of
\(\mathcal O'/(2^{\min(s_w,3)})\) over normalized canonical w.
If \(s_w\le2\), multiplication by 4 is zero in that factor.
If \(s_w\ge3\), then \(4P^C=0\pmod8\) is equivalent to
\(P^C=0\pmod2\), which is exactly \(C(w)=0\).
The latter factors are precisely the tuples passing (99.8), by
(99.7). Faithful flatness descends the containments, proving both
directions of (100.5).

There is an equally exact version that assumes Q only in the
residue field. Define
\[
 P^Q_{g,h}=\sum_mD_{g+m,h}D_{h,m}
       -\delta^2t^2\mathbf1_{g=0}
       +\delta t^2\mathbf1_{h=0},
 \qquad I_8^Q=I_8+(4P^Q_{g,h}:g,h\in\mathbb Z_n).
 \tag{100.6}
\]
Since \(P^Q=(\delta t)^2Q\), imposing these additional
generators leaves an \(s_w\ge3\) factor at exponent 3 exactly
when all residue Q vanish; otherwise its exponent drops to 2.
Consequently
\[
 \boxed{
 \bigl[\text{norms pass modulo 8 and }Q(w)=0\bigr]\Longrightarrow C(w)=0
 \quad\Longleftrightarrow\quad 4P^C_{g,h,k,l}\in I_8^Q\text{ for all indices}.
 } \tag{100.7}
\]
The factor 4 on the added Q polynomials is essential to this
equivalence: adding \(P^Q\) instead would require more than
residue Q on a surviving factor.

Either containment family, if established on unbounded odd orders,
would prove the requested infinitude. Sections 93--95 supply an
analytic norm/convolution solution with all Q at every such order;
reduction and the containment give all C, and Section 58 supplies
the characteristic-zero category. Equivalently, one can seek a
uniform polynomial syzygy over \(\mathbb Z[\delta,X]\) expressing
\(4P^C\) using the convolution, origin, norm, dimension, and
constant-8 generators, with the optional \(4P^Q\) generators.
No uniform syzygy has been obtained.

## 100.4 The complete order-27 two-update test

`hi_convolution_native_filter.py` evaluates the quartics (99.4)
using native finite-field arithmetic, independently checks their
formulas against the unordered-pair definition, and verifies the
residue Q and convolution lift of each surviving Frobenius orbit.
It reproduces the earlier counts at 3,5,7,9,15. At order 27 it
exhausts all 85,197,125 normalized Frobenius tuples in
\(\mathbb F_{2^{36}}\). The three obstruction polynomials have
28 monomials each; the power tables occupy 6 MiB.

| n | All normalized Frobenius tuples | Norms modulo 4 | Norms modulo 8 | Full Q/C points |
|---:|---:|---:|---:|---:|
| 19 | 262145 | 38 | 36 | 36 |
| 21 | 1289925 | 48 | 48 | 48 |
| 27 | 85197125 | 66 | 54 | 54 |

The 66 first-obstruction solutions split into three Frobenius
orbits of length 18 and two of length 6. Each length-18 orbit
satisfies all residue Q and preserves the norms through the tested
modulus 16. Both length-6 orbits fail Q and have exact minimum
norm-defect valuation 2 and origin-defect valuation 3. Thus the
next binary digit rejects precisely the 12 false points. The
existing complete order-27 canonical Q/C classification verifies
all C for the remaining 54 points; no uniform Q-to-C assertion
is used. This proves (99.8) at the additional finite order 27.

The saved JSON files record the field, subgroup generator, phase
exponents, and all orbit representatives. The complete native
run at the six orders takes 5.56 seconds; its parent peak RSS is
17.00 MiB and its child peak, including compilation, is 65.18 MiB.
A further completed run at 19 and 21 takes 1.19 seconds with peak
parent/child RSS 16.49/65.18 MiB. At 19 the two extra modulo-4
points form a Frobenius orbit of length 2, with norm/origin
valuations 2/3; Section 101 identifies their two-value construction.

The factor 4 in (100.5) also has a concrete sharpness test. At
15 and 27 there are factors with \(s_w=2\) and nonzero Q.
Since all C would imply all Q, some \(P^C(w)\) is nonzero in
the residue field on each such factor. Therefore \(2P^C\) is
nonzero in its \(\mathcal O'/4\) factor, so a uniform replacement
of 4 by 2 in (100.5) is false. This does not obstruct the stated
factor-four containment or its version with residue Q added.

## 100.5 Direct mixed-characteristic ideal certificates

`hi_convolution_mod8_ideal.py` constructs the exact ideal over
the integers with 8 as an additional generator. It fixes
\(X_0=-1\), imposes every inverse norm and nonzero-index
convolution equation, computes a strong standard basis, and
reduces every polynomial (100.4) multiplied by 1, 2, and 4.
The zero-index convolution follows from the fixed origin, norms,
and dimension equation, so this is precisely the quotient used
in (100.5). No Q equations are imposed in these runs.

| n | Strong basis size | Nonzero remainders of \(P^C\) | Of \(2P^C\) | Of \(4P^C\) |
|---:|---:|---:|---:|---:|
| 3 | 10 | 48 | 0 | 0 |
| 5 | 31 | 480 | 0 | 0 |
| 7 | 66 | 2040 | 0 | 0 |

Thus the stronger \(2P^C\in I_8\) is established for every
cubic at these three finite orders. The nonzero unmultiplied
remainders retain the torsion information in (100.3); they are
not characteristic-zero counterexamples. The order-3 run takes
0.02 seconds with peak RSS 18.81 MiB; orders 5 and 7 together
take 3.62 seconds with peak RSS 33.06 MiB. An order-9 run reaches
a basis of size 108 but times out after 25 seconds during the cubic
reductions, with peak RSS 48.66 MiB. Its saved log is incomplete
and does not supply an additional containment certificate.

An initial attempt using Singular's direct coefficient ring
\(\mathbb Z/8\) crashed and restarted internally. That log is
retained separately as `hi_convolution_mod8_ring_crash_results.txt`
and supplies no certificate. The completed calculations above
use the integer coefficient ring and the generator 8, representing
the same quotient; the driver rejects crash or restart diagnostics.

The uniform results of this section are (100.1)--(100.3) and
the equivalences (100.5), (100.7). Section 101 disproves the
all-odd-order norm-only containment in (100.5). The containments
with residue Q in (100.7), or norm-only containments on a suitable
unbounded subsequence, remain unproved. **HI infinitude remains open.**

---

# 101. A uniform two-value norm obstruction and counterexamples to norm-only completion

The finite success of (99.8) through order 27 does not extend to all
odd orders. Two-value Legendre phases give small exact counterexamples.
They also permit a uniform calculation of every binary digit of the
norm obstruction, which explains why increasing the precision alone
can be misleading. All counterexamples below fail residue Q, so they
do not refute (94.4), (97.3), or the Q-enriched criterion (100.7).

## 101.1 Reduction to three coordinates

Let \(p=8k+3\) be prime, let chi be its Legendre symbol, and use
\[
 \mathbb F_{16}=\mathbb F_2[z]/(z^4+z+1),\qquad
 \omega=z^2+z.
\]
Choose \(a\ne b\) with \(b=a^4\), \(ab=\omega\), and set
\[
 w_0=1,\qquad w_j=\begin{cases}a,&\chi(j)=1,\\b,&\chi(j)=-1.\end{cases}
 \tag{101.1}
\]
Both \(\chi(-1)\) and \(\chi(2)\) are -1, so these phases
have the inverse norms and canonical Frobenius covariance. There
are two unordered choices for \(\{a,b\}\): their sums are omega
and 1, respectively. In binary coefficient notation they are
\(\{11,13\}\) and \(\{2,3\}\), with omega encoded by 6.

The unique integral convolution lift is invariant under multiplication
of the labels by a quadratic residue. Write its three coordinate
values as x at 0, u on residues, and v on nonresidues, and put
\[
 N=uv,\qquad Z=u+v,\qquad B=(p+1)/4=2k+1.
\]
The elementary quadratic cyclotomic counts give
\[
 \begin{aligned}
 S_0&=x^2+(p-1)uv,\\
 S_R&=2xu+(B-1)u^2+2(B-1)uv+Bv^2,\\
 S_N&=2xv+Bu^2+2(B-1)uv+(B-1)v^2.
 \end{aligned} \tag{101.2}
\]
Here \(S=X*X\). Thus the complete convolution equations reduce to
\[
 xS_0+\lambda=0,\qquad u^2S_N+\lambda v=0,
                    \qquad v^2S_R+\lambda u=0,
 \quad\lambda=\delta(\delta-1),\quad\delta^2=p\delta+1.
 \tag{101.3}
\]
The first equation uses that x is a unit. Subtracting the other
two and dividing by the unit \(u-v\), then subtracting Z times
that difference from their sum and dividing by 2, gives
\[
 \begin{aligned}
 F(x,N)&=x(x^2+(p-1)N)+\lambda=0,\\
 D(x,N,Z)&=BZ^3-2NZ+2xN-\lambda=0,\\
 E(N,Z)&=BNZ^2-\lambda Z-N^2=0.
 \end{aligned} \tag{101.4}
\]
This calculation takes place in the characteristic-zero unramified
integer ring, which has no 2-torsion. It does not cancel 2 in a
quotient modulo a power of 2.

## 101.2 The exact valuation of the lifted norm defect

Select the branch with
\[
 a+b=\begin{cases}\omega,&k\text{ even},\\1,&k\text{ odd}.\end{cases}
\]
Then the exact convolution lift satisfies
\[
 \boxed{
 v_2(uv-\delta)=1+v_2(k(k-1)),\qquad
 v_2(x+1)=2+v_2(k(k-1)).
 } \tag{101.5}
\]
Both valuations are infinite when \(k=0\) or 1. On the other
nonconstant branch the norm and origin valuations are exactly 1
and 2. In particular exact inverse norms within this ansatz occur
only at \(p=3,11\).

Here is a proof, including the valuation comparison needed to pass
from an elimination polynomial to the actual convolution lift.
For any N congruent to delta, the first two equations of (101.4)
have unique solutions x(N), Z(N) with the prescribed residues:
their derivatives with respect to x and Z are units, while their
derivatives with respect to N, and the derivative of D with respect
to x, are even. Consequently changing N by an element of valuation
r changes x and Z by elements of valuation at least \(r+1\).
Inserting them into E, whose N derivative is congruent to \(Z^2\),
shows that
\[
 v_2\bigl(E(N_1,Z(N_1))-E(N_2,Z(N_2))\bigr)=v_2(N_1-N_2)
\]
whenever \(N_1\equiv N_2\equiv\delta\pmod2\).
Compare the actual root N with the trial value delta. At that trial
value \(x=-1\), and \(Z_0=Z(\delta)\) is the prescribed
simple root of
\[
 D_0(Z)=BZ^3-2\delta Z-\delta(\delta+1).
\]
Writing \(q(Z)=BZ^2-(\delta-1)Z-\delta\), the comparison gives
\[
 v_2(uv-\delta)=v_2(q(Z_0)). \tag{101.6}
\]

Set
\[
 h=3k\delta+1,\qquad
 Z_*=\frac{\delta(k\delta+k+1)}h.
\]
The denominator is always a unit. Direct polynomial algebra gives
\[
 BD_0(Z)-(BZ+\delta-1)q(Z)=2h(Z-Z_*), \tag{101.7}
\]
and
\[
 \begin{split}
 h^2q(Z_*)&=k(k-1)(2k+1)U_k,\\
 U_k&=512\delta k^3+448\delta k^2+144\delta k+16\delta
                              +64k^2+32k+5.
 \end{split} \tag{101.8}
\]
The factor \(U_k\) is a unit. Also
\(\bar Z_*\) is omega for even k and 1 for odd k. On the
selected branch \(Z_0\equiv Z_*\pmod2\), and both
\(D_0'(Z_0)\) and \(BZ_*+\delta-1\) are units. Thus (101.8)
and (101.7) evaluated at \(Z_*\) imply
\[
 v_2(Z_0-Z_*)=v_2(k(k-1)).
\]
Evaluation of (101.7) at \(Z_0\), where its leftmost term
vanishes and \(BZ_0+\delta-1\) is a unit, supplies the extra
factor of 2 in (101.5). On the other branch \(Z_0-Z_*\) is
a unit, giving norm valuation 1. Finally
\(F(-1,N)=-(p-1)(N-\delta)\), \(F_x\) is a unit, and
\(v_2(p-1)=1\); this gives the exact origin valuation.

For every fixed precision \(2^r\), r at least 2, primes
\(p\equiv3\pmod{2^{r+2}}\), other than 3 itself, therefore
have such tuples preserving norms modulo \(2^r\) but not exactly.
There are infinitely many such primes by
[Dirichlet's theorem on arithmetic progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html).
Hence no fixed norm precision uniformly forces exact norm preservation.
Equivalently, the torsion exponents \(s_w\) in the norm quotient
(100.3) are unbounded as the odd order varies.
This last uniform assertion concerns exact norms; it does not by itself
assert a failed residue cubic for every prime in those progressions.

## 101.3 Explicit failed cubics after successful high-precision norm tests

`hi_convolution_paley_obstruction.py` verifies (101.7)--(101.8)
symbolically, computes the three-coordinate lift modulo \(2^{16}\),
and compares it with the full p-coordinate convolution at
3,11,19,43,67. It checks both nonconstant residue branches and
computes the following Q and C residuals directly in \(\mathbb F_{16}\).

| p | a,b | Exact norm valuation | Exact origin valuation | Nonzero Q | Nonzero C |
|---:|:---:|---:|---:|:---|:---|
| 19 | 11,13 | 2 | 3 | \(Q(1,2)=\omega\) | \(C(0,2,1,18)=\omega^2\) |
| 43 | 2,3 | 3 | 4 | \(Q(1,5)=\omega\) | \(C(0,5,1,42)=\omega^2\) |
| 67 | 11,13 | 4 | 5 | \(Q(1,2)=1\) | \(C(0,2,1,66)=\omega\) |
| 131 | 11,13 | 5 | 6 | \(Q(1,2)=1\) | \(C(0,2,1,130)=\omega\) |
| 4099 | 11,13 | 10 | 11 | \(Q(1,2)=1\) | \(C(0,2,1,4098)=\omega\) |

The entries a,b are binary polynomial encodings as in (101.1).
The characteristic-zero norm defects have precisely these valuations,
not just the indicated lower bounds. For a quick independent relation
between the last two columns, if h and ell are nonzero and
\(j\notin\{0,-h,\ell,\ell-h\}\), the phase products cancel
in the boundary cubic, giving
\[
 C(0,h,j,\ell)=\omega Q(-\ell,h). \tag{101.9}
\]
The implementation nevertheless evaluates the displayed cubic sums
directly, rather than using (101.9) to declare them nonzero.

In particular order 43 already disproves (99.8). At each of
43,67,131,4099 the lift is a point of the norm/convolution ideal
modulo 8, while its displayed \(P^C\) is a unit. Thus its
\(4P^C\) is nonzero modulo 8, giving explicit failures of the
ideal containments in (100.5). At order 4099 even a norm test
modulo 1024 accepts a failed residue cubic.

The complete check takes 0.27 seconds with peak RSS 56.36 MiB;
the saved JSON records the field, seeds, lifted three coordinates,
dimension value, valuations, and Q/C witnesses. None of these
counterexamples has full residue Q. The uniform implication with
Q retained in (100.7) remains a sufficient, unresolved target.
The finite etale algebra theorem (100.1) is unaffected.
**HI infinitude remains unproved.**

---

# 102. Paired Q sums, norm precision, and explicit first Q lift obstructions

The failed norm-only criterion omitted information already present in
Q. This section identifies that information exactly and makes the
next Q lift errors into explicit residue-field polynomials. Their
vanishing is supplied uniformly by the analytic construction, but
their implication to the remaining cubics is not proved here.

## 102.1 The first norm obstruction is a paired sum of Q

Let X have origin -1 and exact inverse norms, without assuming any
Q or Frobenius identities. For nonzero h define the balanced quartic
\[
 F_X(g,h)=\sum_m X_mX_{h-m}X_{-m-g}X_{m+g-h}.
\]
Substitution \(m\mapsto h-m\) proves
\(F_X(-g,h)=F_X(g,h)\). The phase formula, including the
exceptional entries, gives
\[
 Q_X(g,h)=\frac{F_X(g,h)}{\delta t^2}\quad(g,h\ne0),
 \qquad Q_X(0,h)=0,\qquad t=\delta-1.
\]
Thus Q is even in its first index. This is an exact identity in
the normalized phase coordinates, not just a symmetry of its zero set.
For a direct check of the constants, writing \(S=X*X\) gives
\[
 \sum_gF_X(g,h)=S_hS_{-h},\qquad
 F_X(0,h)=2\delta+(n-2)\delta^2=\delta t^2.
\]
Choose one representative from each nonzero pair \(\{g,-g\}\).
Equation (99.1) consequently strengthens to
\[
 \boxed{
 (\mathcal TX)_h(\mathcal TX)_{-h}-\delta
       =2\delta\sum_{g\bmod\pm1}Q_X(g,h)
       =\frac{2}{t^2}\sum_{g\bmod\pm1}F_X(g,h),\quad h\ne0.
 } \tag{102.1}
\]
In particular Q modulo \(2^r\) makes one update preserve the
norms modulo \(2^{r+1}\).

Now let w be a canonical inverse-normalized residue tuple and Y
its unique convolution lift. Choose an exact inverse-normalized
lift X of w. Since \(Y\equiv\mathcal TX\pmod4\), (99.5)
and (102.1) give
\[
 \boxed{
 \mathcal O_h(w)=\omega\sum_{g\bmod\pm1}Q_w(g,h),
 \qquad \omega=\bar\delta.
 } \tag{102.2}
\]
Equivalently, this is \(\omega^2\sum_gF_w(g,h)\), with the
same opposite-pair representatives, since
\(Q_w(g,h)=\omega F_w(g,h)\) for nonzero indices. Therefore all
the quartic first-norm obstructions (99.4) already lie in the
residue Q ideal, and
\[
 Q(w)=0\quad\Longrightarrow\quad
 Y_aY_{-a}=\delta\pmod4,\qquad Y_0=-1\pmod8.
 \tag{102.3}
\]
The first implication follows from (102.2); the second uses (99.3).
The next norm digit can still add a condition, as discussed below.

## 102.2 Q precision always precedes norm precision by one digit

For an arbitrary canonical normalized residue tuple, form its exact
convolution lift Y. Define \(A(Y)\) by the usual fixed exceptional
entries and the generic ratio \(Y_gY_{h-g}/(tY_h)\), even if Y
does not yet have exact norms. This is well-defined because all its
coordinates are units. Put
\[
 q=\min_{g,h\ne0}v_2(Q_Y(g,h)),\qquad
 s=\min_{a\ne0}v_2(Y_aY_{-a}-\delta).
\]
Then
\[
 \boxed{s\ge q+1,\qquad v_2(Y_0+1)\ge q+2.} \tag{102.4}
\]
Infinite valuations have their usual meaning. In particular exact
nontrivial Q on the convolution lift forces the exact inverse norms
and the exact origin.

To prove the bound, start with \(s\ge1\). Suppose \(q\ge r\)
and norms already hold modulo \(2^r\). Correct one coordinate of
each opposite pair to obtain an exact inverse-normalized X with
\(X\equiv Y\pmod{2^r}\), and set its origin to -1. The origin
estimate (99.3) permits this last change at the same precision.
Then \(Q_X\equiv Q_Y\equiv0\pmod{2^r}\), so (102.1) gives
correct norms on \(\mathcal TX\) modulo \(2^{r+1}\).
Contraction gives \(\mathcal TX\equiv\mathcal TY=Y\)
at that modulus. Induction for \(r=1,\ldots,q\) proves (102.4),
and the same induction works at every finite r if q is infinite.

There is also an ideal formulation. Restrict the finite etale
convolution algebra of Section 100 to the components with normalized
residue origin and inverse norms; every phase coordinate is a unit
there. If \(\mathcal Q\) is the ideal of the patched rational
residuals \(Q_Y(g,h)\), \(g,h\ne0\), then
\[
 (Y_aY_{-a}-\delta:a\ne0)\subseteq2\mathcal Q,
 \qquad (Y_0+1)\subseteq4\mathcal Q. \tag{102.5}
\]
Indeed the containments follow from (102.4) on each unramified factor
in (100.2), then descend faithfully flatly. The coefficients clearing
the displayed rational residuals are units on these components.

For a more precise statement about the next digit, suppose q is at
least r. By (102.4) an exact normalized X can be chosen congruent to
Y modulo \(2^{r+1}\), and \(\mathcal TX\equiv Y\pmod{2^{r+2}}\).
Dividing (102.1) at this precision gives
\[
 \boxed{
 \overline{\frac{Y_hY_{-h}-\delta}{2^{r+1}}}
 =\omega\sum_{g\bmod\pm1}
                 \overline{\frac{Q_Y(g,h)}{2^r}}.
 } \tag{102.6}
\]
Thus each next norm obstruction records only a paired sum of the
first surviving Q errors. It does not require every such error to
vanish individually.

## 102.3 The convolution lift modulo 4 has an explicit Witt formula

Use length-two 2-typical Witt coordinates \((a,b)\) over the finite
residue field, representing \([a]+2[\sqrt b]\), where brackets
denote Teichmuller representatives. The operations are
\[
 \begin{aligned}
 (a,b)+(c,d)&=(a+c,b+d+ac),\\
 (a,b)(c,d)&=(ac,a^2d+c^2b),\\
 -(a,b)&=(a,b+a^2).
 \end{aligned} \tag{102.7}
\]
These formulas follow by the first two Witt polynomials
\(x_0\) and \(x_0^2+2x_1\); all coordinates on the right
are computed in characteristic two.

Put \(c=\omega^2\), \(\epsilon=(n-1)/2\pmod2\), and retain
the unordered pair sum \(U_a(w)\) from Section 99. Then
\[
 \delta=(\omega,\omega+\epsilon c),\qquad
 \lambda=\delta(\delta-1)=(1,\epsilon c).
\]
The unique convolution lift modulo 4 is
\[
 \boxed{
 Y_a=(w_a,e_a),\qquad
 e_a=(1+\epsilon c)w_a^2+w_aU_a(w)^2.
 } \tag{102.8}
\]
To check it directly, start T at the Teichmuller tuple \([w_a]\).
For \(a=2r\) the paired convolution is
\((w_r^2,U_a^2)\). Multiply it by
\([w_r]^2=(w_r^2,0)\) and
\(-\lambda^{-1}=(1,1+\epsilon c)\), and use
\(w_r^4=w_a\). One update agrees with Y modulo 4 by contraction,
giving (102.8). At the origin \(U_0=\epsilon\omega\), so
\(e_0=1\), consistent with \(Y_0=-1\pmod4\).

This formula needs only residue-field arithmetic; it does not
require choosing a polynomial model for an unramified integer ring.

## 102.4 Polynomial formulas for every first Q lift obstruction

Let \((d_{g,h},b_{g,h})\) be the Witt coordinates of the
polynomial core \(D_{g,h}(Y)\) from (100.4). They are explicit:
\[
 \begin{array}{c|c|c}
 (g,h)&d_{g,h}&b_{g,h}\\\hline
 (0,0)&c&c\\
 g=0\text{ or }h=0\text{ or }g=h,\ (g,h)\ne(0,0)
       &\omega&\omega+(\epsilon+1)c.
 \end{array}
\]
At a generic entry set \((i,j,k)=(g,h-g,-h)\). Then
\[
 \begin{aligned}
 d_{g,h}&=w_iw_jw_k,\\
 b_{g,h}&=(w_iw_j)^2e_k+(w_iw_k)^2e_j+(w_jw_k)^2e_i.
 \end{aligned}
\]
For nonzero g,h define \(r_m=d_{g+m,h}d_{h,m}\) and the polynomial
\[
 \boxed{
 \mathcal K_{g,h}(w)=
 \sum_m\bigl(d_{g+m,h}^2b_{h,m}+d_{h,m}^2b_{g+m,h}\bigr)
             +\sum_{m<j}r_mr_j.
 } \tag{102.9}
\]
The ordering in the last sum is any fixed ordering of \(\mathbb Z_n\).
It counts unordered pairs once and does not depend on that choice.
The polynomial has degree at most 15: \(e_a\) has degree at
most 5, \(b_{g,h}\) at most 9, and the last sum at most 12.
The calligraphic \(\mathcal K\) here denotes a Q lift obstruction,
distinct from the quartic reconstruction residual K of Section 52.

Assume all residue Q vanish. Equation (102.3) then gives exact
norms modulo 4, so \(D=\lambda A\) at that precision.
Also \(\lambda^2=1\pmod4\). The polynomial Q residual
\(P^Q_{g,h}=\sum_mD_{g+m,h}D_{h,m}\) therefore equals
the usual \(Q_Y(g,h)\) modulo 4. Applying the Witt addition
and multiplication formulas shows that its coordinates are
\((0,\mathcal K_{g,h}(w))\). Hence
\[
 \boxed{
 \mathcal K_{g,h}(w)=
       \left(\overline{Q_Y(g,h)/2}\right)^2.
 } \tag{102.10}
\]
These are the complete first Q lift errors, as opposed to the sums
of errors appearing in (102.6).

All of the following inputs now exist at every odd order:
\[
 w_0=1,\qquad w_aw_{-a}=\omega\ (a\ne0),\qquad w_{2a}=w_a^4,
 \qquad Q(w)=0,\qquad \mathcal K(w)=0. \tag{102.11}
\]
Indeed the analytic phases of Sections 93--95 have exact norms,
convolution, and all Q. Their unique convolution lift is the same
tuple at a prime above 2, so its first Q errors vanish. This proves
uniform nonemptiness of the stronger system (102.11).

A sufficient remaining completion statement is
\[
 \boxed{\text{The hypotheses (102.11) imply every residue cubic C.}}
 \tag{102.12}
\]
Its hypotheses imply the modulo-8 norm test by (102.4), so (102.12)
is a weaker assertion than the Q-enriched completion in (100.7).
Either assertion on unbounded odd orders would suffice for HI
infinitude. The false tuples in Section 101 satisfy neither assertion's
Q hypothesis.

There are two equivalent ideal formulations of (102.12). In
characteristic two, impose the normalized origin, inverse norms,
Frobenius equations, balanced Q quartics, and the polynomials
\(\mathcal K_{g,h}\). This ideal is radical: its quotient is
a quotient of the finite etale Frobenius algebra. Thus (102.12)
is equivalent to membership of every polynomial cubic residual
in this explicit ideal, without a radical or saturation operation.
Alternatively work over
\(R_4=(\mathbb Z/4)[\delta]/(\delta^2-n\delta-1)\)
and let \(I_4^{HQ}\) be generated by all convolution, origin,
norm, and polynomial Q equations \(P^Q\). Then
\[
 \boxed{(102.12)\quad\Longleftrightarrow\quad
            2P^C_{g,h,k,l}\in I_4^{HQ}\text{ for all indices}.}
 \tag{102.13}
\]
To see this, split the convolution algebra as in (100.2). On each
normalized residue factor, (102.4) makes the norm valuation strictly
larger than the minimum Q valuation q. Replacing the rational Q
by \(P^Q\) changes it only at the higher norm-defect precision,
so its minimum valuation is the same q. The quotient factor is
therefore \(\mathcal O'/(2^{\min(q,2)})\). Factors with q=0
vanish, factors with q=1 kill \(2P^C\) automatically, and factors
with \(q\ge2\) require precisely \(C(w)=0\). The latter are
exactly (102.11), by (102.10). Faithfully flat descent proves the
equivalence. No uniform membership proof has been found.

## 102.5 Independent finite checks

`hi_convolution_q_digits.py` checks (102.2) on all 5,17,63,325
normalized Frobenius tuples at orders 3,5,7,9, respectively. It
also verifies the exact identity (102.1) on perturbed integral
normalized lifts. At 5,7,9 the perturbations give Q valuations
1,2,3,4 and updated norm valuations exactly 2,3,4,5, so the
one-digit bound can be sharp. Every saved canonical Q orbit at
3,5,7,9,15,19,21,27 has all Q and norms zero through modulus 64
on its convolution lift. These are finite-precision checks and
do not prove exact Q on arbitrary residue branches. The complete
run takes 9.92 seconds with peak RSS 15.63 MiB.

`hi_convolution_witt_q.py` compares (102.8)--(102.10) against
independent arithmetic modulo 4. It includes 29 residue tuples at
3,5,7,9, including failed Q inputs for the underlying Witt formulas,
and all nontrivial Q coordinates on the saved canonical Q orbits
at 3,9,27. It checks 2218 Q coordinates in total, in 5.08 seconds,
with peak RSS 15.39 MiB. The direct arithmetic obtains Teichmuller
representatives by repeated squaring, independently of (102.8).

The new uniform results are the paired identity, the valuation
bounds, the explicit first-Q obstruction polynomials, and the
nonemptiness of (102.11). Uniform cubic completion (102.12) is
still missing. **HI infinitude remains unproved.**

---

# 103. Balanced first-Q obstructions and bounded-degree cubic certificates

The first lift obstruction admits a smaller polynomial expression
than the matrix formula in Section 102. This removes a dependence
on the dimension's second binary digit from the remaining residue
system. A separate certificate search tests how simple a uniform
Q-to-C identity could be. Neither step completes that identity.

## 103.1 The balanced obstruction has degree at most 11

Let w satisfy the normalized inverse norms and canonical Frobenius
equations, without yet assuming Q. For nonzero g,h put
\[
 \begin{aligned}
 I_m&=(m,h-m,-m-g,m+g-h),\\
 u_m&=\prod_{a\in I_m}w_a,\qquad
 f_{g,h}=\sum_m u_m=F_w(g,h).
 \end{aligned}
\]
The entries of \(I_m\) are counted with multiplicity. Define
\[
 \boxed{
 \mathcal L_{g,h}(w)=
 \sum_m\sum_{\nu=1}^4
   w_{(I_m)_\nu}\left(\prod_{\mu\ne\nu}w_{(I_m)_\mu}\right)^2
                    U_{(I_m)_\nu}(w)^2
       +\sum_{m<j}u_mu_j.
 } \tag{103.1}
\]
The first sum has degree at most 11 and the second at most 8.
All coefficients are in \(\mathbb F_2\). In particular the
formula contains no \(\epsilon=(n-1)/2\pmod2\).

In the Witt coordinates of Section 102, the balanced quartic of
the unique convolution lift satisfies
\[
 \boxed{F_Y(g,h)=(f_{g,h},\mathcal L_{g,h})\pmod4.} \tag{103.2}
\]
Indeed the second coordinate of a product of four phases is the
sum of \(e_a\) times the squares of the other three factors.
Inserting (102.8), the term
\((1+\epsilon\omega^2)\prod_{a\in I_m}w_a^2\)
occurs four times and cancels. The remaining terms are exactly
the first sum of (103.1). Adding the products over m introduces
the Witt carry \(\sum_{m<j}u_mu_j\). This proves the formula
even for repeated entries and for tuples failing Q.

## 103.2 An exact comparison with the matrix obstruction

Write \(c=\omega^2\), and set
\[
 \begin{split}
 E_{g,h}={}&w_hw_{-g-h}w_g+w_hw_{-g}w_{g-h}\\
           &+w_gw_{h-g}w_{-h}+w_{g+h}w_{-g}w_{-h}.
 \end{split}
\]
Then the degree-15 obstruction of (102.9) satisfies the exact
residue identity
\[
 \boxed{
 \mathcal K_{g,h}
 =c\mathcal L_{g,h}
    +(\omega+\epsilon c)f_{g,h}^2
    +\mathcal O_h^2(f_{g,h}+E_{g,h})^2.
 } \tag{103.3}
\]
It is important to retain the last two terms away from Q.

For a proof, let \(\nu_h=Y_hY_{-h}-\delta\) modulo 4.
The origin of Y is -1 modulo 4 even without Q. Introduce the
unpatched polynomial entries
\(\widetilde D_{a,b}=Y_aY_{b-a}Y_{-b}\).
In a column h with \(h\ne0\), the two exceptional entries
of \(D_{a,h}\) differ from \(\widetilde D_{a,h}\) by
\(\nu_h\). In the row h the same is true at positions 0 and h.
Thus for \(g,h\ne0\), expansion of the two factors gives
\[
 P^Q_{g,h}(Y)=\delta F_Y(g,h)
                    +\nu_h\bigl(F_Y(g,h)+E_{g,h}(Y)\bigr)\pmod4.
 \tag{103.4}
\]
The product of two exceptional corrections is zero, because
\(\nu_h^2=0\pmod4\). The unpatched product sums to
\((\delta+\nu_h)F_Y(g,h)\), and its four linear corrections
are exactly the displayed E terms. This also covers \(g=\pm h\),
where corrections can coincide.

Now \(\nu_h=(0,\mathcal O_h^2)\) in Witt coordinates,
\(\delta=(\omega,\omega+\epsilon c)\), and (103.2) gives
the coordinates of F. Applying (102.7) to (103.4) proves (103.3).

By (102.2), \(\mathcal O_h\) is a linear combination of
balanced Q quartics. Consequently, in the inverse-norm/Frobenius
coordinate algebra,
\[
 \boxed{(F_{g,h},\mathcal K_{g,h}:g,h\ne0)
             =(F_{g,h},\mathcal L_{g,h}:g,h\ne0).} \tag{103.5}
\]
This is an equality of ideals from an explicit identity, not an
inference from the finite examples. Thus the system
\[
 w_0=1,\quad w_aw_{-a}=\omega\ (a\ne0),\quad
 w_{2a}=w_a^4,\quad F(w)=0,\quad\mathcal L(w)=0
 \tag{103.6}
\]
is equivalent to (102.11) and is nonempty at every odd order.
Proving that its polynomial cubic residuals vanish on an unbounded
set of orders remains sufficient for the requested infinitude.

`hi_convolution_balanced_witt.py` checks 2292 instances of (103.3)
on 62 tuples at orders 3,5,7,9, including tuples failing Q. It
independently checks 40 balanced quartics in an unramified integer
ring modulo 4. The run takes 0.51 seconds with peak RSS 14.82 MiB.

## 103.3 Testing a bounded-degree uniform certificate strategy

A direct polynomial identity for C would be more decisive than
further point counts. To investigate its possible form, eliminate
opposite phases over \(\mathbb F_4\) by
\[
 W_a=x_a\ (1\le a\le r),\qquad
 W_{-a}=\omega x_a^{-1},\qquad W_0=1,
 \quad r=(n-1)/2.
\]
The balanced Q quartics become Laurent polynomials
\(F_{g,h}\). Their sign and interchange symmetries allow
\(1\le g\le h\le r\) as generators. For a cross-free cubic
quadruple, let P denote its balanced residual
\(\sum_m\prod_iW_{m+a_i}\prod_jW_{-m+c_j}
 -\prod_{i,j}W_{a_i+c_j}\).
The search asks for an identity
\[
 P=\sum_{1\le g\le h\le r}\ \sum_{\|e\|_1\le L}
       c_{g,h,e}x^eF_{g,h},\qquad c_{g,h,e}\in\mathbb F_4.
 \tag{103.7}
\]
No Frobenius or lift-obstruction equations are used in this search;
it tests the stronger Q-only certificate strategy.

All the generators and targets have cyclic character weight zero.
Thus only multipliers satisfying
\(\sum_{a=1}^r ae_a=0\pmod n\) can contribute. Omitting other
weight blocks is exact: different character weights form a direct
sum of vector spaces. For fixed L, (103.7) is therefore a finite
linear system over \(\mathbb F_4\).

`hi_laurent_q_certificate.py` performs exact row reduction using
two binary coefficient planes and saves every positive certificate
as a list of monomial multiples of Q. Each positive result is
replayed as a Laurent polynomial identity before acceptance.
The selected targets and first successful bounds are:

| n | Cubic quadruple | Multiplier bound L | Nonzero certificate terms |
|---:|:---:|---:|---:|
| 3 | (1,1,1,1) | 6 | 4 |
| 5 | (1,1,1,1) | 5 | 10 |
| 7 | (1,1,1,1) | 6 | 62 |
| 9 | (1,2,5,3) | 5 | 187 |
| 11 | (1,2,5,3) | 5 | 599 |
| 13 | (1,2,5,3) | 6 | 2667 |
| 15 | (1,2,5,3) | 6 | 8528 |

These are certificates for the chosen cubic, not new full
categorification theorems. The bounds are degrees of Laurent
multipliers in the specified norm coordinates, not total degrees
of a homogenized polynomial ideal.

There is also an independently replayable obstruction to the
degree-5 ansatz at order 13. A linear functional supported on just
40 Laurent monomials annihilates all 5901 allowed monomial multiples
of Q and takes value 1 on the target. This proves that (103.7)
with \(L=5\) is impossible for that target, even though a
degree-6 certificate exists. It refutes an all-odd-order bound of
5 for this certificate form; it does not refute cubic completion.
Completed linear-algebra tests also fail at \(L=5\) for 15 and 17.

The independent `hi_laurent_q_replay.py` verifies all seven saved
identities and the order-13 separating functional without reusing
the elimination algorithm. Replay takes 0.23 seconds with peak
RSS 18.07 MiB. The completed order-15 degree-6 search takes 76.59
seconds with peak RSS 279.70 MiB. Earlier bounded attempts that
stopped at a time or memory limit are retained as incomplete logs;
their terminal limits are not nonmembership certificates.

No common formula for the coefficients in (103.7), no uniform
degree bound, and no uniform cubic containment for (103.6) have
been proved. The explicit degree-11 equations and the certificate
tests guide the next algebraic step; **HI infinitude remains unproved.**

---

# 104. Odd-order recognition from an actual intertwiner

There is a separate sufficient route through an already associative
bimodule category. The complete proof and the flatness literature audit
are in [the recognition note](hi_odd_bimodule_recognition_20260907.md).
The word **Q-system** in this section means a special associative
\(C^*\)-Frobenius algebra object. It is not the polynomial system Q
used elsewhere in these notes.

Let \(G\) be abelian of odd order \(n\), and let
\(d=(n+\sqrt{n^2+4})/2\). In a semisimple rigid \(C^*\)-tensor category
with simple unit and split projections, suppose there is an untwisted
pointed subcategory \(\operatorname{Vec}_G\), a self-dual simple
\(\rho\) of intrinsic dimension \(d\), and isomorphisms

\[
 \alpha_g\rho\cong\rho\alpha_{-g}.
 \tag{104.1}
\]

Assume the objects \(\alpha_g\rho\) are mutually inequivalent.
Then **one nonzero actual morphism**
\(v:\rho\longrightarrow\rho^2\) implies

\[
 \rho^2\cong\mathbf1\oplus\bigoplus_{g\in G}\alpha_g\rho.
 \tag{104.2}
\]

Indeed, conjugation by \(\alpha_a\) sends \(\rho\) to
\(\alpha_{2a}\rho\) and preserves \(\rho^2\). Applying it to \(v\)
supplies all \(n\) noninvertible summands, since doubling is bijective.
Self-duality supplies the unit. Their total positive dimension is
\(1+nd=d^2\), so there can be no additional summands or multiplicities.
The \(2n\) specified simples are then closed under products and duals.
Thus the ambient category need not have finite depth in advance:
the generated subcategory is a unitary HI fusion category.

An actual normalized standard Q-system on \(A=\mathbf1\oplus\rho\)
automatically supplies \(v\). With isometric unit and multiplication
\(m\), write \(b:\rho^2\to\rho\) for its indicated block. Standardness
and the two unit laws give

\[
 mm^*=(1+d)\operatorname{id}_A,\qquad
 bb^*=(d-1)\operatorname{id}_\rho.
 \tag{104.3}
\]

Consequently \(b^*/\sqrt{d-1}\) is the required isometry. In particular,
an irreducible finite-index factor bimodule \(X\) of index \(d+1\),
with \(X\bar X=\mathbf1\oplus\rho\) and simple \(\rho\), suffices
if an honest outer action of \(G\) has the free orbit and covariance
in (104.1). The canonical Q-system of \(X\bar X\) provides (104.3).
Frobenius reciprocity then forces the principal graph with \(n\)
length-three arms

\[
 \alpha_g-X_g-\alpha_g\rho-Y,\qquad X_g=\alpha_gX.
 \tag{104.4}
\]

Simplicity of the common endpoint \(Y=\rho X-X\) is a conclusion.
No uniform family satisfying the actual covariance in (104.1)
has been constructed. A phase cocycle or a biunitary matrix has
not been shown to supply that bimodule isomorphism. The recognition
criterion therefore does not discharge the missing C equations of
the existing analytic candidate.

---

# 105. The two monodromy quotients carry the proposed quadratic forms

Section 59 already compares the Pell monodromy with the two-segment
S-fold family. The following calculation identifies its two finite
quadratic modules, including the signs of their Gauss sums. It is a
uniform arithmetic calculation, not a categorification argument.

## 105.1 Quotients by the integer and by the different

Retain the matrices of (59.1):

\[
 M_n=\begin{pmatrix}n&1\\1&0\end{pmatrix},\qquad
 P_n=M_n^2,\qquad D=n^2+4.
\]

In the quadratic order \(\mathcal O_n=\mathbb Z[d]\), with basis
\((d,1)\), they represent multiplication by \(d\) and \(d^2\).
Besides \(P_n-I=nM_n\), we have

\[
 P_n+I=\begin{pmatrix}n^2+2&n\\n&2\end{pmatrix},\qquad
 \operatorname{SNF}(P_n+I)=\operatorname{diag}(1,D).
 \tag{105.1}
\]

The entries have gcd 1 and the determinant is \(D\). The ideal
identities explaining both quotients are

\[
 (d^2-1)=(n),\qquad
 (d^2+1)=(2d-n)=\mathfrak D_{\mathcal O_n},
 \tag{105.2}
\]

because \(d^2-1=nd\), \(d^2+1=d(2d-n)\), and \(d\) is a unit.
The different of this monogenic order is generated by the derivative
\(2d-n=\sqrt D\) of its defining polynomial. Equivalently, its trace
dual is \((\sqrt D)^{-1}\mathcal O_n\). These statements apply also
when \(\mathcal O_n\) is nonmaximal. In fact \(P_n+I\) is precisely
the trace Gram matrix of the basis \((d,1)\).

Thus, writing additive quotient groups,

\[
 A:=\operatorname{coker}(P_n-I)\cong\mathcal O_n/(n)
      \cong(\mathbb Z/n)^2,\qquad
 \Gamma:=\operatorname{coker}(P_n+I)
      \cong\mathcal O_n/\mathfrak D_{\mathcal O_n}
      \cong\mathbb Z/D.
 \tag{105.3}
\]

For the last identification, the constant element 1 is a generator
and \(d\) maps to \(n/2\) modulo \(D\). Fractions with denominator 2
in finite odd-order groups mean multiplication by its modular inverse.

## 105.2 A pairing and its explicit quadratic refinement

Put \(J=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)\).
For \(s=\pm1\), \(K_s=P_n+sI\), define

\[
 b_s([v],[w])=v^T J K_s^{-1}w\pmod{\mathbb Z}.
 \tag{105.4}
\]

This is well defined, symmetric and nondegenerate. To check the
first variable and symmetry, respectively, the exact identities are

\[
 K_s^T J K_s^{-1}=sJP_n^{-1}\in M_2(\mathbb Z),\qquad
 JK_s^{-1}-(JK_s^{-1})^T=sJ.
 \tag{105.5}
\]

Changing the second variable by \(K_sz\) changes the value by
the integer \(v^TJz\). If \(b_s(v,w)=0\) for every integral \(v\),
then \(JK_s^{-1}w\) is integral, hence \(w\in K_s\mathbb Z^2\).
This proves nondegeneracy.

Oddness gives the unique homogeneous refinement
\(q_s(v)=\tfrac12b_s(v,v)\). Here the half is taken in the
odd-torsion subgroup of \(\mathbb Q/\mathbb Z\); halving an arbitrary
rational representative would be incorrect.
Let \(t_m=2^{-1}\pmod m\). Direct inversion gives

\[
 \begin{aligned}
 JK_-^{-1}&=\begin{pmatrix}-1/n&1\\0&1/n\end{pmatrix},&
 q_A(x,y)&=\frac{t_n(-x^2+y^2)}n,\\
 JK_+^{-1}&=\frac1D
   \begin{pmatrix}n&-(n^2+2)\\2&-n\end{pmatrix},&
 q_\Gamma(u)&=-\frac{nt_Du^2}{D}.
 \end{aligned}
 \tag{105.6}
\]

All quadratic values here and below are modulo \(\mathbb Z\).
The coordinate on \(\Gamma\) is \(u=y+nt_Dx\). For \(A\), the
invertible change of coordinates

\[
 U=y-x,\qquad V=t_n(y+x)
 \quad\Longrightarrow\quad q_A=UV/n
 \tag{105.7}
\]

identifies it with the hyperbolic quadratic module.
In order coordinates \(z=xd+y\), the same formulas are

\[
 q_A(z)=\frac{t_n\operatorname{Nm}(z)}n,\qquad
 q_\Gamma(z)=\frac12\left(-\frac{\operatorname{Tr}(dz^2)}D\right).
 \tag{105.8}
\]

The second half again has the odd-torsion meaning. For example,
\(\operatorname{Tr}(dz^2)=(n^3+3n)x^2+
2(n^2+2)xy+ny^2\), verifying (105.8) against (105.6).
Multiplication by \(d\) sends each quadratic form to its negative.
On \(A\) its square is the identity; on \(\Gamma\) its square is
negation. These are arithmetic symmetries, with no asserted
categorical realization.

## 105.3 Opposite Gauss sums at every odd order

Write \(\gamma(q)=|H|^{-1/2}\sum_{x\in H}e^{2\pi iq(x)}\).
The hyperbolic expression gives \(\gamma(q_A)=1\) by character
orthogonality. For the other factor, \(D\equiv5\pmod8\) and
\(\gcd(n,D)=1\). The odd quadratic Gauss sum formula gives

\[
 \gamma(q_\Gamma)=\left(\frac{-nt_D}{D}\right)=-1.
 \tag{105.9}
\]

Indeed \(D\equiv1\pmod4\), so
\[
 \left(\frac{-1}{D}\right)=1,\qquad
 \left(\frac{n}{D}\right)=\left(\frac{D}{n}\right)
     =\left(\frac4n\right)=1,\qquad
 \left(\frac{t_D}{D}\right)=\left(\frac2D\right)=-1.
\]
This proof uses Jacobi symbols, so neither \(n\) nor \(D\) needs
to be prime or squarefree.

For \(\gamma_m(q)=|H|^{-1/2}\sum_xe^{2\pi imq(x)}\), also
\(\gamma_m(q_A)=\gcd(m,n)\) and \(\gamma_2(q_\Gamma)=1\).
Finally, \(\gamma_3(q_\Gamma)=-1\) if \(3\mid n\) and \(+1\)
otherwise: \(3\nmid D\) and
\(\gamma_3(q_\Gamma)=-\left(\frac3D\right)\), whose sign reduces
by reciprocity to \(D\bmod3\).

## 105.4 Modular matrices, the twist comparison, and an invariant vector

With involution \(-1\), both fixed subgroups in (105.3) are trivial.
The sizes differ by 4, and (105.9) supplies opposite Gauss sums.
These forms therefore satisfy the hypotheses of
[Grossman–Izumi, Definition 3.1, Lemma 3.4 and Theorem 3.6](https://arxiv.org/pdf/1906.07397):
the associated \(S,T\) are unitary modular matrices with nonnegative
integral Verlinde coefficients. This theorem constructs matrices,
not a modular tensor category.

Label them by \(\{0,\pi\}\sqcup(A\setminus0)/\{\pm1\}\sqcup
(\Gamma\setminus0)/\{\pm1\}\), put \(a=1/n,b=1/\sqrt D\), and
write \(\chi_H(v,w)=e^{2\pi i b_H(v,w)}\). The blocks are

\[
 S=\begin{pmatrix}
 (a-b)/2&(a+b)/2&a&b\\
 (a+b)/2&(a-b)/2&a&-b\\
 a&a&a(\chi_A+\overline{\chi_A})&0\\
 b&-b&0&-b(\chi_\Gamma+\overline{\chi_\Gamma})
 \end{pmatrix},\qquad
 T=\operatorname{diag}(1,1,e^{2\pi iq_A},e^{2\pi iq_\Gamma}).
 \tag{105.10}
\]

Constant blocks have the indicated sizes. There are \(n^2+3\)
labels, and \(S^2=(ST)^3=I\). Dividing the first row by \(S_{00}\)
gives dimensions \(1,d^2,1+d^2,d^2-1\) on the four blocks.

Using the generators in the S-fold source's equation (2), namely
\(S_{\rm src}=-J,T_{\rm src}=R\), gives
\[
 S_{\rm src}T_{\rm src}^{-n}S_{\rm src}T_{\rm src}^{n}=-P_n.
 \tag{105.11}
\]
Thus its parameters \(p_+,p_-\) are \(-n^2,-D\). The relative twist
exponents at levels \((-n,n)\) are \((-x^2+y^2)/n\) and
\(-nu^2/D\); the source's \(\operatorname{Gal}_2\) multiplies them
by \(2^{-1}\), giving exactly (105.6).
[Jeong–Sohn, equations (43), (74)–(75)](https://arxiv.org/html/2608.11946v1#S4.SS2).
This compares relative twists; it assumes no categorical Galois construction.

There is an exact invariant vector. In hyperbolic coordinates choose
\(L=\{(x,0)\}\subset A\), and set
\[
 v_0=v_\pi=1,\qquad v_{[g]}=2\,\mathbf1_{g\in L},\qquad
 v_{[\gamma]}=0.
 \tag{105.12}
\]
Then \(Sv=Tv=v\). The first two entries follow from
\(a+(n-1)a=1\). A nonzero \(g\in A\) has entry
\(2a\sum_{\ell\in L}\chi_A(g,\ell)=2\mathbf1_{g\in L}\),
since \(L^\perp=L\); the \(\Gamma\) entries cancel. Its formal
dimension is
\[
 1+d^2+(n-1)(1+d^2)=n(1+d^2)=1/S_{00}.
 \tag{105.13}
\]
Therefore, **if** a unitary modular tensor category realizes
(105.10), (105.12) specifies an object with trivial twist and the
dimension required for a Lagrangian algebra. It does not specify
a multiplication, associativity, commutativity or separability.
The rank-one matrix \(vv^T\) commuting with \(S,T\) does not supply
those missing structure maps.

The physics source leaves identification of the complete simple
lines and a corresponding check of its proposed full \(S\) to
further work.
[Jeong–Sohn, Section 5](https://arxiv.org/html/2608.11946v1#S5).
The category realizing (105.10) and an actual Lagrangian algebra on
(105.12) have not been constructed here uniformly. Section 106
proves that, given those two inputs, the module fusion rules are
automatically cyclic HI. The separate recognition criterion of
Section 104 also still needs actual bimodule data.

The small [verification script](hi_pell_metric_groups.py) checks
the exact matrix identities at all 50 odd orders from 3 through 101
and 6000 deterministically sampled rational quotient/form comparisons.
It checks the Gauss evaluations numerically and (105.10)–(105.12)
at 3,5,7,9. The [saved run](hi_pell_metric_groups_results.txt) uses
about 13 MiB of memory. These cross-checks of the written uniform
arithmetic proof provide no new category-existence certificates.
**Infinitude remains unproved.**

---

# 106. A specified Lagrangian algebra forces the cyclic HI category

The full proof is in
[the modular recognition note](hi_modular_lagrangian_recognition_20260907.md).
It removes the separate fusion-rule identification step from Section 59
and the end of Section 105, subject to the two still-unconstructed
categorical inputs.

**Conditional theorem.** Let \(n\geq3\) be odd. Suppose a unitary
modular tensor category \(\mathcal B\) realizes the labeled matrices
(105.10), and suppose the object

\[
 \Lambda=\mathbf1\oplus\pi\oplus
        \bigoplus_{x=1}^{(n-1)/2}2g_{(x,0)}
 \tag{106.1}
\]

admits an actual connected commutative separable unitary algebra
structure. Then \(\mathcal C=\mathcal B_\Lambda\) is a unitary
cyclic HI fusion category with untwisted pointed subcategory.

Here \(g_{(x,y)}\) labels the hyperbolic quadratic module in (105.7).
The theorem does not assume any simple-object decomposition or
fusion coefficients for \(\mathcal C\).

The dimension calculation (105.13) makes \(\Lambda\) Lagrangian.
For the central free-module functor \(F\) and its adjoint \(I\),
\(I(\mathbf1)=\Lambda\). The underlying induction formula
\(FI(X)=\bigoplus_Y YXY^*\) implies

\[
 \operatorname{rank}\mathcal C=\dim\operatorname{End}(\Lambda)=2n.
 \tag{106.2}
\]

Verlinde and \(Sv=v\) give the full adjunction Gram matrix
\[
 \langle F(i),F(j)\rangle
     =\sum_k S_{ik}S_{jk}\frac{v_k}{S_{0k}}.
 \tag{106.3}
\]
Its explicit evaluation yields one actual class \(R=F(\gamma)\)
of dimension \(nd\) and squared norm \(n\), and virtual integral
classes \(K_y=F(g_{(x,y)})-R\). For the nonzero pairs \(y,-y\),
these classes are orthogonal, have dimension 2 and squared norm
2, and are orthogonal to both \(R\) and the unit.

An orthogonal-projection equality determines the entire positive
simple-dimension vector:
\[
 \mathbf f=\mathbf a+d\mathbf m,\qquad
 \mathbf a=\mathbf e_1+\sum_{[y]\ne0}K_y,\quad
 \mathbf m=[R],\qquad
 \|\mathbf a\|^2=\|\mathbf m\|^2=n.
 \tag{106.4}
\]
Since \(\mathbf m\) is nonnegative integral on \(2n\) simples,
at least \(n\) entries are zero. On these entries the positive
dimensions are the integers \(a_X\). They exhaust
\(\|\mathbf a\|^2=n\). Thus there are exactly \(n\) dimension-one
simples and \(n\) dimension-\(d\) simples, and \(R\) contains each
noninvertible exactly once. This also proves that each \(K_y\)
is an actual pair of invertibles, rather than an arbitrary virtual
difference.

The character coordinates of the central image give
\(K_yK_z=K_{y+z}+K_{y-z}\), with \(K_0=2\mathbf1\).
Consequently \(K_y=\alpha^y+\alpha^{-y}\) and \(\alpha\) generates
the invertible group of order \(n\).
Comparing the rational and irrational dimensions of \(XY^*\)
for noninvertible simples shows that the left cyclic action is
free and transitive.
Centrality of \(K_1\) restricts the right action to the identity
or inversion. The identity would make the entire fusion ring
commutative and force \(F_*\) to be surjective, contradicting
\(\operatorname{rank}F_*=(n+3)/2\) from (106.3).
Hence inversion is forced; duality and oddness then give

\[
 \rho^*=\rho,\qquad \rho\alpha=\alpha^{-1}\rho,\qquad
 \rho^2=\mathbf1+\sum_{g\bmod n}\alpha^g\rho.
 \tag{106.5}
\]

Finally \(I(\alpha)=\bigoplus_{x\bmod n}g_{(x,1)}\), whose twists
are all \(n\)-th roots of unity. The central-induction formula
gives \(\nu_n(\alpha)=1\), forcing the cyclic pointed associator
class to vanish. The recognition note includes the primary
reconstruction and indicator references and every intermediate
Gram entry.

The verifier in Section 105 checks all the entries of (106.3)
against the derived branching at 3,5,7,9. The argument above is
uniform, independent of those finite checks. It proves no
existence of the category \(\mathcal B\) or the algebra
multiplication on (106.1). **Those two construction problems, and
HI infinitude, remain unresolved.**

---

# 107. The degree-six Q-only certificate bound fails for the full system

Section 103 tested one chosen cross-free cubic at each order.
A shared row-space calculation now tests all cross-free cubic
orbits at 13 and 15. This distinction changes the proposed
bounded-degree strategy: its degree-six version is false.
The implication Q-to-C itself is not disproved.

## 107.1 A larger product degree need not make a target harder

For the previously chosen tuple \((1,2,5,3)\), the two triples
are \(a=(0,4,1)\), \(c=(3,-5,-3)\). Three opposite pairs cancel
in the nine-factor product, giving, at all odd orders \(n\geq9\),

\[
 \prod_{i,j}W_{a_i+c_j}
   =\omega^3 W_{-5}W_7W_{-2}=W_{-5}W_7W_{-2}.
 \tag{107.1}
\]

Thus this target's product term has Laurent degree 3, rather
than 9. It is cross-free, but it should not be used as the sole
representative of all cubic difficulty. Conversely, degree by
itself does not order that difficulty: at \(n=13\), the target
\((1,3,3,11)\) has product degree 9 yet admits a multiplier-degree-5
certificate with 2350 terms. That identity is independently
replayed in the saved files.

The improved search checks membership during each degree level.
At order 13 it recovers the identical previously saved 2667-term
certificate after 7296 rows, rather than finishing all 14133 rows
through degree 6. The positive identity is replayed before acceptance;
an early stop never asserts nonmembership. This reduces the
comparison run to 0.99 seconds and 31.23 MiB.

## 107.2 A complete order-13 bound and a degree-six obstruction at 15

Use exactly the Laurent coordinates and multiplier convention
of (103.7). The new batch calculation shares one exact
\(\mathbb F_4\) row space among all orbit representatives.
Their coverage is the established permutation, translation,
interchange and unit-scaling reduction of Sections 34–40.
Unit scaling permutes the Laurent coordinates up to inversion
and a nonzero \(\mathbb F_4\) coefficient, so it preserves
multiplier \(\ell^1\) degree. The other beta symmetries preserve
the target polynomial itself after reindexing.

At \(n=13\), all 30 representatives have replayable certificates:
8 are found by degree 5 and 22 by degree 6. They cover all
1111 scalar-normalized cross-free quadruples. The earlier
degree-5 separating functional for \((1,2,5,3)\) shows that
the maximum required bound at this order is exactly 6.

At \(n=15\), the 86 representatives cover all 26390 cross-free
quadruples, using the composite-order reduction. Of these,
63 have saved degree-six certificates. The complete degree-six
row calculation leaves 23 unresolved targets and produces
the following independently replayed obstruction for one of them.

Set
\[
 P=\sum_{m\bmod15}W_m^3W_{2-m}W_{-1-m}^2-W_2^3W_{-1}^6.
 \tag{107.2}
\]
This is the balanced residual of \(C(1,1,1,1)\), with
\(a=(0,0,0)\) and \(c=(2,-1,-1)\).
Let \(F_{g,h}\) be the balanced Q quartics in (103.7), and write
\(x^e=\prod_{a=1}^7x_a^{e_a}\).
The file
[degree-six separating functional](hi_laurent_q_15_q1_1_1_1_bound6_obstruction.json)
defines an \(\mathbb F_4\)-linear functional \(\ell\), supported
on 328 Laurent monomials, for which

\[
 \ell(P)=1,\qquad
 \ell(x^eF_{g,h})=0
 \quad
 \left(
 \begin{array}{l}
 1\leq g\leq h\leq7,\\
 \|e\|_1\leq6,\quad\sum_{a=1}^7ae_a=0\pmod{15}.
 \end{array}
 \right)
 \tag{107.3}
\]

The independent replay enumerates and checks all 36148 allowed
rows, without repeating Gaussian elimination. Since every Q
generator and \(P\) has character weight zero, multipliers of
other weights cannot contribute to the desired identity.
Equation (107.3) therefore proves

\[
 \boxed{P\notin
 \operatorname{span}_{\mathbb F_4}
 \{x^eF_{g,h}:\|e\|_1\leq6\}.}
 \tag{107.4}
\]

This refutes a uniform degree-six bound for (103.7), even though
the selected tuple in Section 103 has a degree-six certificate
at the same order. Any Q-only certificate for (107.2) in this
Laurent form needs multiplier degree at least 7. It does not
assert nonmembership in the full Q ideal, nor exhibit a Q
solution with failed C. The full finite Q-to-C implication
at 15 remains the previously established one.

## 107.3 Consequence for the uniform proof strategy

The obstruction target (107.2) is a diagonal cubic.
Section 71 proves uniformly that Q plus the matrix Frobenius
relations already implies every \(C(g,g,k,k)\). The analytic
candidate has these Frobenius relations at every odd order by
Sections 94–95. Thus the failed degree-six target is already
known to vanish on that candidate by a uniform argument.

The calculation identifies a limitation of the stronger Q-only
certificate ansatz. It motivates using the proved Frobenius
relations, and possibly the first Q-lift equations (103.6),
when seeking a uniform interior-cubic identity. Such an identity
has not been proved here. Increasing the Q-only degree to 7
also has no established uniform justification.

The batch search takes 2.14 seconds and 139.89 MiB at 13,
and 82.57 seconds and 689.84 MiB at 15. Independent replay of
all 63 positive order-15 identities and the separator takes
9.94 seconds with peak RSS 421.57 MiB. The compressed bundles
retain every coefficient and the orbit coverage; their
decompressed bytes were checked against the original JSON
before removing the larger generated copies.

Separate order-17 degree-six attempts stopped near the specified
1 GiB memory cap. The checkpointed run had processed 57800
rows; it did not complete the degree level and gives neither a
positive certificate nor bounded nonmembership. No such search
is still running. **Infinitude remains unproved.**

---

# 108. Certificates in the Frobenius algebra and a uniform degree obstruction

The Frobenius relations are available for the canonical analytic candidate
at every odd order. They can be imposed before searching for Q-to-C
identities, using the exact coordinate algebra of Section 72.1.
This produces smaller finite certificate bounds, but it does not make
the uniform implication automatic. In fact, multiplier degree four
is insufficient on an explicit infinite family.

## 108.1 The full coordinate algebra, without choosing a solution

Put \(c=\omega^2\) and \(V_a=c^{-1}W_a\) for \(a\ne0\).
The norm and canonical Frobenius relations become
\[
 V_{-a}=V_a^{-1},\qquad V_{2a}=V_a^4.
 \tag{108.1}
\]
For a doubling orbit of length \(s\) disjoint from its negative,
choose one seed \(z_i\). The orbit and its negative are parametrized
by \(z_i^{4^j}\) and \(z_i^{-4^j}\), with
\(z_i^{4^s-1}=1\). If the orbit equals its negative, \(s\) is even;
its half-turn is negation and the seed instead satisfies
\(z_i^{2^s+1}=1\). Thus the entire coordinate algebra is
\[
 R_n=\mathbb F_4[z_1^{\pm1},\ldots,z_t^{\pm1}]
       /(z_i^{M_i}-1:1\le i\le t),
 \qquad
 M_i=
 \begin{cases}
 4^{s_i}-1,&O_i\cap(-O_i)=\varnothing,\\
 2^{s_i}+1,&O_i=-O_i.
 \end{cases}
 \tag{108.2}
\]
Every nonzero phase is \(c\) times one root monomial, and \(W_0=1\).
Conversely each \(z_i=c^{-1}W_{a_i}\), so this parametrization has
an inverse on coordinate algebras, not just on selected points.
All \(M_i\) are odd. The algebra is finite etale of dimension
\(\prod_iM_i\); no Q or cubic relation has yet been used.

For comparison with Section 107, retain the original Laurent
multiplier length
\[
 x^e=\prod_{a=1}^{(n-1)/2}W_a^{e_a},\qquad
 |e|_1=\sum_a|e_a|.
 \tag{108.3}
\]
The new certificates express a balanced cubic \(P_{\mathbf q}\) as
\[
 P_{\mathbf q}=\sum_{g,h,e}\lambda_{g,h,e}\,x^e F_{g,h}
 \quad\hbox{in }R_n,\qquad |e|_1\le L.
 \tag{108.4}
\]
Here \(F_{g,h}\) are exactly the balanced Q quartics of Section 103.
The former character-weight restriction must be removed: (108.1)
identifies the exponent \(4e_a\) with \(e_{2a}\), whose cyclic
character weights differ. The search enumerates all multiplier
weights and combines root monomials modulo the periods \(M_i\).
Equivalent multipliers are deduplicated only up to a nonzero
\(\mathbb F_4\) scalar.

## 108.2 Finite certificates and an explicit order-15 separator

The saved bundles certify all cross-free beta orbits at these orders:

| \(n\) | Periods \(M_i\) | Orbits certified | Upper bound \(L\) |
|---:|:---|---:|---:|
| 3 | 5 | 1/1 | 0 |
| 5 | 17 | 2/2 | 1 |
| 7 | 63 | 6/6 | 2 |
| 9 | 65, 5 | 14/14 | 3 |
| 11 | 1025 | 17/17 | 3 |
| 13 | 4097 | 30/30 | 3 |

These are identities in (108.2), rather than in the free Laurent
ring of Section 107. They therefore use both norms and Frobenius.
The orbit coverage remains valid: unit relabeling preserves
these hypotheses and sends each original Laurent phase variable
to a phase or its inverse, up to a scalar.

At \(n=15\), the periods, with seeds at labels \(1,3,5\), are
\((255,17,5)\). The complete degree-three calculation has
549 distinct root multipliers, 15372 nonzero input rows, 14596
columns and rank 14393. It certifies 71 of the 86 cubic orbits.
For the first remaining target \(\mathbf q=(1,1,2,2)\), define
\[
 \ell(f)=[z_1^{96}z_3^{13}z_5^3]f,
 \tag{108.5}
\]
where exponents are reduced modulo \(255,17,5\), respectively.
The saved one-coordinate functional gives
\[
 \ell(P_{(1,1,2,2)})=1,\qquad
 \ell(x^eF_{g,h})=0\quad(|e|_1\le3).
 \tag{108.6}
\]
Independent replay checks all 16100 original rows, including
duplicate root multipliers. Hence degree three is rigorously
insufficient for (108.4) at 15. This target is still a diagonal
cubic, whose vanishing under Q and Frobenius has the separate
uniform proof of Section 71.

A degree-four run certifies 83 of 86 order-15 orbits before its
time limit. It does not finish the degree level and gives no
degree-four nonmembership claim. At order 17, a completed
degree-two run certifies 3 of 63 orbits and exports a separating
functional for \((1,1,1,1)\); all 5220 rows are replayed.
The first multi-order trial's high-water memory check incorrectly
prevented its order-17 stage from starting after the order-15
cap was reached. The implementation now checks current resident
memory; the separate order-17 run supplies the stated result.

The independent verifier constructs Q and C first in the old
free Laurent coordinates and then substitutes (108.2). It does
not repeat Gaussian elimination. All accepted identities are
also replayed before export. A resource stop is explicitly
distinguished from a completed bounded search.

## 108.3 A degree-five lower bound at infinitely many orders

**Proposition.** For every integer \(r\ge11\), let \(n=2^r-1\).
In \(R_n\), the balanced cubic with
\(\mathbf q=(1,5,13,41)\) is not in the
\(\mathbb F_4\)-span of the \(x^eF_{g,h}\) with \(|e|_1\le4\).
Consequently any certificate (108.4) for this cubic has
multiplier degree at least five.

**Proof.** Its balanced triples and nine cross-sums are
\[
 a=(0,12,36),\quad c=(6,-13,-41),\qquad
 (a_i+c_j)_{i,j}=
 \begin{pmatrix}
 6&-13&-41\\
 18&-1&-29\\
 42&23&-5
 \end{pmatrix}.
 \tag{108.7}
\]
All cross-sums are nonzero modulo \(n\). Their positive odd parts
are the nine distinct integers
\[
 \mathcal T=\{1,3,5,9,13,21,23,29,41\}.
 \tag{108.8}
\]
These occupy nine distinct doubling orbits, also distinct after
negation, and each orbit has length \(r\).

Here is a uniform verification of that assertion. Multiplication
by 2 modulo \(2^r-1\) cyclically rotates the \(r\)-bit expansion.
Each member of \(\mathcal T\) is odd and has all its set bits in
positions 0 through 5. A nontrivial rotation by \(j\) positions
that wraps no set bit is even, so cannot be another member of
\(\mathcal T\). If a set bit wraps, then \(j\ge r-5\ge6\);
the original bit at position 0 becomes a bit at position \(j\).
The rotated value is therefore at least 64, again outside
\(\mathcal T\). This proves distinctness and the full orbit length.
Moreover each member has at most four set bits, whereas the
negative of a member modulo \(n\) has at least \(r-4\ge7\).
Rotations preserve this count, excluding all negative-orbit
identifications.

For each \(q\in\mathcal T\), use the seed \(z_q=\omega W_q\)
in (108.2). The nine corresponding periods are \(4^r-1\).
The product term of this cubic is the single basis monomial
\[
 Z=z_1^{-1}z_3^4z_5^{-1}z_9^4z_{13}^{-1}
          z_{21}^4z_{23}z_{29}^{-1}z_{41}^{-1}.
 \tag{108.9}
\]
Its coefficient is \((\omega^2)^9=1\). Every one of these nine
coordinates has a nonzero exponent modulo its period.

Define the coordinate support of a root monomial to be the
number of seed coordinates with nonzero exponent. A product
of \(k\) phases or inverse phases has coordinate support at
most \(k\); reduction modulo the separate periods cannot
introduce a coordinate. Each summand of the six-factor sum
in \(P_{\mathbf q}\) has support at most six. Thus coefficient
extraction at \(Z\) takes value 1 on \(P_{\mathbf q}\).

Each summand of \(x^eF_{g,h}\) has support at most
\(|e|_1+4\le8\). Coefficient extraction at \(Z\) consequently
kills every such Q multiple, proving the assertion. \(\square\)

The checker verifies the orbit assertion exactly for
\(r=11,\ldots,128\), using only integer rotations and \(O(r)\)
stored integers. The uniform conclusion comes from the binary-rotation
and coordinate-support proof, not from extrapolating these
118 checks.

## 108.4 What this establishes for the existence problem

Frobenius does shorten finite certificates, but a uniform bound
of three or four in (108.4) is false. Degree at least five, or a
different identity, is necessary even with the proved Frobenius
relations included. This is not a Q-to-C counterexample: the
proposition gives a separating functional for a bounded space
of multiples, not for the full Q ideal.

The analytic candidate still satisfies norm, Frobenius, Q and
the first Q-lift equations uniformly. Neither (108.4) with a
sufficient uniform bound nor completion from the stronger
Q-plus-lift hypotheses has been proved. No new category
existence is claimed here. **Infinitude remains unproved.**

The small searches through order 13 finish in under five seconds
with peak RSS below 100 MiB. The completed order-15 degree-three
search uses 32.17 seconds and 258.52 MiB. The degree-four run
stops after 95.05 seconds, including certificate checks and
export, at 301.69 MiB. Replay of the degree-three order-15
and degree-two order-17 bundles takes 7.10 seconds and
380.79 MiB. All 83 identities in the partial degree-four bundle
also replay independently, in 8.21 seconds with peak RSS
438.86 MiB. No computation in this section needs a large memory
reservation.

---

# 109. First Q-lift certificates and their character law

The stronger system (103.6) is nonempty at every odd order.
This section incorporates its first lift equations into the exact
certificate search, and identifies their behavior under character
gauge. The latter prevents an unjustified Fourier-projection
shortcut to extra equations.

## 109.1 A derivative expression for the lift error

For this calculation introduce independent variables
\(X_0,\ldots,X_{n-1}\), including the origin, and write
\[
 \widehat F_{g,h}(X)=\sum_m\prod_{a\in I_m}X_a,\qquad
 \mathcal J_{g,h,a}(w)=
       \left.\frac{\partial\widehat F_{g,h}}{\partial X_a}
       \right|_{X=w},\qquad
 \mathcal E_{g,h}(w)=\sum_{m<j}u_mu_j.
 \tag{109.1}
\]
The derivative must precede substitution of the origin and
inverse norms. The carry retains the original list of \(n\)
quartic summands, even when equal monomials cancel in F.
Then (103.1) becomes the uniform identity
\[
 \boxed{\mathcal L_{g,h}(w)=
       \mathcal E_{g,h}(w)+
       \sum_a w_a U_a(w)^2\mathcal J_{g,h,a}(w)^2.}
 \tag{109.2}
\]
Indeed the formal derivative is the sum of all products obtained
by deleting one occurrence of \(X_a\). Squaring this sum in
characteristic two removes cross terms and gives exactly the
slot sum in (103.1). Repeated indices are counted with their
correct multiplicities. This identity requires neither Q nor
Frobenius.

The formula exhibits the lift error as a known carry vector
plus a matrix of squared formal derivatives applied to the
vector \((w_aU_a^2)_a\). It supplies structure that is absent
from an undifferentiated list of degree-eleven monomials.
It does not itself solve the resulting compatibility equations.

## 109.2 The exact character law and its limitation

Assign \(w_a\) character weight \(a\) modulo \(n\). This grading
is well defined after imposing the origin and inverse norms,
but before imposing Frobenius. The carry \(\mathcal E_{g,h}\)
has weight zero; \(U_a\) has weight \(a\); and
\(\mathcal J_{g,h,a}\) has weight \(-a\). Consequently
\[
 \mathcal B_{g,h,a}:=w_a U_a^2\mathcal J_{g,h,a}^2
 \quad\hbox{has weight }a.
 \tag{109.3}
\]
For any \(n\)-th root \(\chi\), let \(w^\chi_a=\chi^a w_a\).
The exact transformation law is
\[
 \boxed{\mathcal L_{g,h}(w^\chi)=
       \mathcal E_{g,h}(w)+
       \sum_a\chi^a\mathcal B_{g,h,a}(w).}
 \tag{109.4}
\]
For clarity, the weight-zero component is also explicit.
Writing \(\epsilon=(n-1)/2\bmod2\) and using the triple sum
\(E_{g,h}\) of Section 103.2, one has
\[
 U_0=\epsilon\omega,\qquad
 \mathcal J_{g,h,0}=E_{g,h},\qquad
 \mathcal L_{g,h}^{(0)}
       =\mathcal E_{g,h}+\epsilon\omega^2 E_{g,h}^2.
 \tag{109.5}
\]
The derivative identity at the origin includes the coincident
exceptional terms when \(g=\pm h\).

Unlike Q and the cubic matrix equations, \(\mathcal L=0\) is
not invariant under arbitrary character twists. Such twists
also change the canonical Frobenius condition:
\[
 \frac{(w^\chi_a)^4}{w^\chi_{2a}}=\chi^{2a}
 \quad\hbox{if }w_a^4=w_{2a}.
 \tag{109.6}
\]
Since \(n\) is odd, preserving this condition for every \(a\)
forces \(\chi=1\). Thus neither the uniform analytic construction
nor character invariance of Q licenses setting every separate
weight component in (109.4) to zero.

An explicit full cubic point already demonstrates the issue
at \(n=3\). Let \(c=\omega^2\), choose
\[
 z^2+cz+1=0,\qquad
 w=(1,cz,cz^{-1}).
 \tag{109.7}
\]
Then \(z\) has order five, the phases have the required norms
and canonical Frobenius, and their balanced Q quartic is
\(\omega+z^2+z^3=0\). They give a complete cubic solution.
Direct substitution in (109.1)--(109.3) gives
\[
 (\mathcal E_{1,1}+\mathcal B_{1,1,0},
      \mathcal B_{1,1,1},\mathcal B_{1,1,2})
       =(0,c,c).
 \tag{109.8}
\]
Hence, for \(\chi^3=1\),
\[
 \mathcal L_{1,1}(w^\chi)=c(\chi+\chi^2)
   =\begin{cases}0,&\chi=1,\\c,&\chi\ne1.\end{cases}
 \tag{109.9}
\]
All three twists give the same normalized matrix and therefore
the same full cubic solution. The two nontrivial twists fail
canonical Frobenius, so (109.9) does not contradict the proposed
completion under (103.6). On those twists it evaluates the
polynomial \(\mathcal L\); (103.2) does not identify that value
with a canonical convolution lift of the twisted tuple.
It shows precisely why character
projection cannot add hypotheses to that completion problem.

## 109.3 Certificates using both Q and the first lift equations

The batch search now supports identities in \(R_n\) of the form
\[
 P_{\mathbf q}=\sum_{g,h,e}
       \lambda_{g,h,e}x^eF_{g,h}
       +\sum_{g,h,e}\mu_{g,h,e}x^e\mathcal L_{g,h},
       \qquad |e|_1\le L.
 \tag{109.10}
\]
Every term records whether its generator is Q or \(\mathcal L\).
The original Q-only bundles remain valid and retain their
original meaning.

Sign changes and interchange of \(g,h\) remain exact
symmetries of the lift generators. For Q, the changes
\(g\mapsto-g\), \(h\mapsto-h\), and
\((g,h)\mapsto(h,g)\) respectively reindex the quartet family
by \(m\mapsto h-m\), \(m\mapsto-g-m\), and
\(m\mapsto m+g-h\). They permute quartet entries.
Both the slot sum and the unordered pair carry in (103.1)
are invariant under these permutations. Unit relabeling
similarly preserves the full family of lift equations.
Thus the previous generator and cubic-orbit reductions apply,
with all multiplier character weights retained.

The independently replayed upper bounds for every cubic orbit are:

| \(n\) | Q only in \(R_n\) | Q plus \(\mathcal L\) in \(R_n\) |
|---:|---:|---:|
| 3 | 0 | 0 |
| 5 | 1 | 1 |
| 7 | 2 | 1 |
| 9 | 3 | 2 |
| 11 | 3 | 2 |
| 13 | 3 | 3 |

At 13 the last upper bound is supplied by the already replayed
Q-only certificates. A new complete degree-two calculation
has 3570 rows, 4097 columns and rank 3564. Its saved functional,
supported on 2705 root monomials, takes value 1 on
\(P_{(1,1,1,1)}\) and kills every allowed Q and
\(\mathcal L\) multiple. Independent replay checks all 3570
rows. The worst required bound at this order is therefore
exactly three even with the additional lift generators.

The order-15 degree-three trial is incomplete. It stops at
the 90-second limit after 16595 rows, with rank 16581 and
peak RSS 180.52 MiB. Its seven accepted cubics already vanish
in the norm/Frobenius ring; no additional cubic is certified.
This supplies no degree-three nonmembership claim.

The symbolic generator checks compare two constructions:
direct expansion of phase index lists in \(R_n\), and products
and squares in the free Laurent ring followed by substitution.
They verify 56 generator pairs through order 13, their formal
derivative decompositions, character weights and symmetries.
A separate comparison checks 480 finite-field coordinates
against the previously verified Witt formula. The order-3
example includes all 81 cubics and all three character twists.
The small certificate and separator replay takes 0.70 seconds
and 76.98 MiB.

The stronger hypotheses have now been used in explicit finite
certificates, with their gauge dependence accounted for.
A uniform identity (109.10), or another completion argument
for (103.6), is still needed. The finite bounds and the
derivative formula do not prove it. **HI infinitude remains
unproved.**

---

# 110. Product Fourier sums, their residues, and a continuous Euler transform

The exact column transform in Section 93 permits a different attack on
the interior cubics. A Fourier transform in one cubic index replaces
the six-factor sum by a transformation of two column products. This
section proves that finite reduction, evaluates both product sums in
an ordered index range at the convergent frequencies by two four-gamma
integrals, and derives the relevant continuous Euler identity.
The period shifts needed to connect the two finite product sums
are resolved in Section 111, which also removes the frequency
restriction by induction.

## 110.1 An exact finite transformation target

Retain the periods and core matrix of Section 93, and set
\[
 u_p(a)=\mathsf B_{a,p},\qquad \tau=\delta-1=-B,\qquad
 S_{p,q,s}(k)=\sum_{a\bmod n}u_p(a)u_q(a+s)e^{-2\pi ika/n}.
 \tag{110.1}
\]
The subscripts in this finite definition are read modulo n. For
nonzero g,h,g+h, write the scaled cubic residual as
\[
 \mathcal C_{g,h}(k,l)=
 \sum_m\mathsf B_{m,g+h}\mathsf B_{g,m+k}\mathsf B_{h,m+l}
 -\tau\mathsf B_{g+l,k}\mathsf B_{h+k,l}.
\]
Order-three symmetry gives
\(\mathsf B_{g,a}=u_{-g}(a-g)\). Consequently, with
\(\xi=2\pi j/n\),
\[
 \boxed{
 \sum_k\mathcal C_{g,h}(k,l)e^{-i\xi k}
 =e^{-i\xi g}\left[
 \widehat u_{-g}(j)S_{g+h,-h,l-h}(-j)
 -\tau e^{-i\xi l}S_{-g-l,l,g+h+l}(j)\right].
 }\tag{110.2}
\]
This is an identity away from the Q or C solution scheme. For the
first term, the Fourier transform of the row indexed by g is
\(e^{-i\xi g}\widehat u_{-g}(j)\), and translating its argument
by m supplies \(e^{i\xi m}\). For the second term, substitute
\(a=k-g-l\). These are precisely the two terms in (110.2).

Thus, for fixed g,h, all its cubics hold if and only if the
bracket in (110.2) vanishes for every j,l. The single-column
factor has the proved evaluation (93.1). No Q-to-C implication
is being assumed in this reformulation.

## 110.2 Signed representatives and the two-ratio shift

Signed column labels simplify the contour. If \(-n<q<0\), then
\[
 \boxed{
 u_q(a)=\frac{(-1)^{q(a+1)}}{\sqrt d F(q)}
              \frac{F(a)}{F(a-q)},\qquad 0\le a<n .
 }\tag{110.3}
\]
Unlike (93.2), this formula has no exceptional sample. Indeed,
the right side is \(\delta f(a)/(f(a-q)f(q))\), where f is the
meromorphic phase interpolation. At the diagonal \(a=n+q\),
its denominator contains \(f(n)=1/d\), so the value is
\(\delta d=-1\). At \(a=0\), inverse norms give -1 as well.
All other samples follow from the ordinary phase quotient.

For arbitrary integers p,q,s, put
\[
 R_p(z)=F(z)/F(z-p),\qquad
 K(z)=\frac{\pi e^{-i\omega z}}{\sin\pi z}R_p(z)R_q(z+s),
 \quad
 \omega\equiv 2\pi k/n+\pi(p+q-1)\pmod{2\pi}.
\]
Define
\[
\begin{aligned}
 J_1(z)&=\gamma(-z)\gamma(z-p)
           \gamma(B-z-s)\gamma(A+z+s-q),\\
 J_2(z)&=\gamma(A-z)\gamma(B+z-p)
           \gamma(-z-s)\gamma(z+s-q).
\end{aligned}
\]
There is the exact meromorphic identity
\[
 \boxed{
 K(z+n)-K(z)=-4\pi e^{-i\omega z}
 \left[(-1)^q\sin(\pi p/A)J_1(z)
       +(-1)^s\sin(\pi q/A)J_2(z)\right].
 }\tag{110.4}
\]
To prove it, write \(M_p=R_p(z+n)/R_p(z)\) and
\(M_q=R_q(z+s+n)/R_q(z+s)\). Split its multiplier as
\[
 (-1)^{p+q}M_pM_q-1
 =\bigl((-1)^pM_p-1\bigr)(-1)^qM_q
   +\bigl((-1)^qM_q-1\bigr).
\]
Apply the sine identity in Section 93 to each bracket. In the
second term, \(\sin(\pi(z+s))/\sin(\pi z)=(-1)^s\).
The remaining ratios are
\[
 R_q(z+s+n)=\gamma(B-z-s)\gamma(A+z+s-q),\qquad
 R_p(z)=\gamma(A-z)\gamma(B+z-p),
\]
which gives (110.4).

## 110.3 An ordered product Fourier formula, with every correction retained

Suppose
\[
 g,h\ge1,\qquad p=g+h<n,\qquad 1\le l\le h,\qquad
 q=-h,\quad s=l-h.
\]
Choose the principal \(\omega\) in (110.4), and set
\[
 c_0=\frac{(-1)^{p+q+qs}}{dF(p)F(q)},\quad
 a_0=(-1)^q\sin(\pi p/A),\quad
 b_0=(-1)^s\sin(\pi q/A).
\]
Let
\[
 I_i=\int_{\mathcal C_i}e^{-i\omega z}J_i(z)
                       \frac{dz}{i\sqrt\Omega}
\]
use meromorphically continued separating contours. Then
\[
 \boxed{
 S_{p,q,s}(k)=-2\sqrt\Omega\,c_0(a_0I_1+b_0I_2).
 }\tag{110.5}
\]
This theorem holds at every odd n in the stated index range,
at every discrete frequency.

Here is the pole audit. Let \(L=\lfloor p/B\rfloor\) and
\(\sigma=-\varepsilon\), with
\[
 0<\varepsilon<\min\{1,(L+1)B-p\}.
\]
Since \(s\le0\), neither numerator of K has a pole in
\(\sigma<\Re z<\sigma+n\). The denominator \(F(z+s-q)=F(z+l)\)
has no zero there. The only noninteger poles of K in this
strip are
\[
 z_j=p-jB,\qquad 1\le j\le L.
\]
The shifted kernel \(K(z+n)\) is regular at all these points.
Irrationality of B rules out coincidences with poles from its
other factors.

The left poles of \(J_1\) that cross the line are exactly
\(z_0=p,z_1,\ldots,z_L\); those of \(J_2\) are exactly
\(z_1,\ldots,z_L\). Their other left poles lie at or to the
left of \(-l\), and their right poles are nonnegative.
No left and right pole coincide: the potentially negative
pair sums are \(-p\) and \(B-g-l\), and a coincidence would
express an integer strictly between 0 and n as a nonnegative
period combination with a positive B coefficient.

Write
\[
 r_{i,j}=\operatorname*{Res}_{z=z_j}e^{-i\omega z}J_i(z).
\]
Equation (110.4) gives
\(\operatorname{Res}_{z_j}K=4\pi(a_0r_{1,j}+b_0r_{2,j})\)
for \(j\ge1\). Passing from the vertical line to the two
separating contours adds
\[
 \frac{2\pi}{\sqrt\Omega}\sum_{j=0}^Lr_{1,j}
 \quad\hbox{and}\quad
 \frac{2\pi}{\sqrt\Omega}\sum_{j=1}^Lr_{2,j},
\]
respectively. The residue rectangle therefore yields
\[
 \sum_{a=0}^{n-1}\operatorname{Res}_{z=a}K
 =-2\sqrt\Omega(a_0I_1+b_0I_2)+4\pi a_0r_{1,0}.
 \tag{110.6}
\]
All its horizontal boundaries vanish: the ratio product decays
as \(O(e^{-\pi g|\Im z|/\Omega})\), and
\(|\omega|\le\pi<\pi(1+g/\Omega)\).

For integer sampling, the shifted negative column has no
correction in this range. Its numerator arguments lie strictly
between \(-h\) and n; its denominator arguments are \(a+l>0\),
and the value at n gives the correct diagonal. Only the
positive column contributes a patch:
\[
 S_{p,q,s}(k)=c_0\sum_a\operatorname{Res}_{z=a}K
       -B u_q(p+s)e^{-2\pi ikp/n}.
\]
Finally,
\[
 r_{1,0}=\frac{\sqrt\Omega}{2\pi}e^{-i\omega p}
                \gamma(-p)R_q(p+s+n),\qquad
 c_0\,4\pi a_0r_{1,0}
       =B u_q(p+s)e^{-2\pi ikp/n}.
\]
The last equality uses the same sine normalization as Section 93,
and \(R_q(p+s+n)=(-1)^qR_q(p+s)\) at this integer.
It cancels the patch exactly and proves (110.5).

## 110.4 Moving the sampling interval evaluates the other product

Keep \(g,h,l\) in the range of Section 110.3, and abbreviate
\[
 G=g+l,\quad H=g+h,\quad t=H+l,\qquad
 (p',q',s')=(-G,l,t).
\]
Formula (110.5), with all its parameters replaced by these primed
ones, also holds for the right product whenever
\[
 |\omega|<\pi(1-g/\Omega).
 \tag{110.6a}
\]
The proof samples the same finite sum on the interval
\[
 a=-t,-t+1,\ldots,n-t-1.
\]
Both numerator interpolations now avoid positive multiples of n.
The two raw columns differ from their actual samples only at
\(a=-G\) and \(a=-H\), respectively, each by B.

Let \(L_h=\lfloor h/B\rfloor\) and
\(L_l=\lfloor l/B\rfloor\). Put
\(\sigma=-t-\varepsilon\), where
\[
 0<\varepsilon<
 \min\{1,(L_h+1)B-h,(L_l+1)B-l\}.
\]
There are again no numerator poles in the rectangle. Its
noninteger poles are the two families
\[
 -G-jB\ (1\le j\le L_h),\qquad
 -H-jB\ (1\le j\le L_l).
\]
The shifted kernel is regular at them. The crossed left poles
of \(J_1\) are the first family including its \(j=0\) point;
those of \(J_2\) are the first family with \(j\ge1\) and the
second family including \(j=0\). The other left poles stay to
the left of \(\sigma\), and all right poles stay to its right.
All noninteger residues therefore cancel just as in (110.6).

If \(h\ne l\), the two remaining integer residues cancel the
two sample patches separately. More precisely, their normalized
contributions are
\[
 B u_l(h)e^{2\pi ikG/n},\qquad
 B u_{-G}(-H)e^{2\pi ikH/n}.
\]
If \(h=l\), the noninteger poles of \(J_2\) and K can be double.
The cancellation uses their full residues and still follows
from the meromorphic identity (110.4). At the common integer
point, the second contribution uses the raw first column,
whose diagonal value is \(1/d\), whereas the first contribution
uses the actual second column with value -1. Their sum is
\[
 B(1/d-1)e^{2\pi ikH/n}
 =(d^{-2}-1)e^{2\pi ikH/n}.
\]
This is exactly the difference between the raw product of
the two diagonal values, \(d^{-2}\), and the actual product,
1. Thus the coincident-diagonal \(B^2\) correction is retained.
The decay condition for the rectangle is precisely (110.6a),
since now \(p'+q'=-g\).

The frequency restriction has an exact count. Write the
principal frequency as \(\omega=\pi v/n\), with v an integer
of parity \(g+1\), considered modulo \(2n\). Since
\[
 n(1-g/\Omega)=n-g+2g/A,\qquad 0<2g/A<2,
\]
condition (110.6a) is equivalent to
\[
 |v|\le n-g. \tag{110.6b}
\]
It therefore admits exactly \(n-g+1\) of the n frequencies
and excludes \(g-1\). In particular, when \(g=1\), both
product formulas are proved at every frequency in the
stated index range.

## 110.5 The continuous Euler identity has an explicit six-step proof

For general separating-contour parameters define
\[
 I(a,b;c,e;y)=
 \int e^{2\pi iyz/\Omega}
       \gamma(a+z)\gamma(b+z)\gamma(c-z)\gamma(e-z)
                         \frac{dz}{i\sqrt\Omega}.
\]
Put \(\Sigma=a+b+c+e\) and \(r=(\Sigma-\Omega)/2\). Then
\[
 \boxed{
 I(a,b;c,e;y)=
 \frac{\gamma(a+c)\gamma(b+e)\gamma(a+e)\gamma(b+c)}
      {\gamma(\Sigma/2+y)\gamma(\Sigma/2-y)}
 I(a-r,b-r;c-r,e-r;y).
 }\tag{110.7}
\]
As throughout this section, the periods satisfy \(AB=A+B=\Omega\).
This identity is first proved in a common convergence domain;
elsewhere the integrals mean their meromorphic continuations,
including the necessary contour residues.

For a direct proof, introduce
\[
 U=\Omega/4+(r+s)/2,\quad V=\Omega/4+(r-s)/2,\qquad
 K_4(r,s,x,y)=\int e^{2\pi iyz/\Omega}
       \gamma(U\pm z)\gamma(V\pm(z+x))\frac{dz}{i\sqrt\Omega},
\]
and \(G_r(v)=\gamma(\Omega/2+r+v)\gamma(\Omega/2+r-v)\).
The two-gamma Fourier formula used in Section 93 gives, by
Fourier convolution,
\[
 K_4(r,s,x,y)=G_r(s)e^{-2\pi ixy/\Omega}
                           K_4(-r,-s,-y,x). \tag{110.8}
\]
The source formula is equation (2.17) of
[Belousov--Sarkissian--Spiridonov](https://arxiv.org/html/2412.07562v2).
Interchanging the two positive gamma parameters and translating
the contour also gives
\[
 K_4(r,s,x,y)=e^{\pi iy(s-x)/\Omega}K_4(r,x,s,y).
 \tag{110.9}
\]
Denote (110.8) by D and (110.9) by P. Applying DPDPDP sends the
arguments through
\[
\begin{aligned}
 (r,s,x,y)&\longmapsto(-r,-s,-y,x)
 \longmapsto(-r,-y,-s,x)\\
 &\longmapsto(r,y,-x,-s)
 \longmapsto(r,-x,y,-s)\\
 &\longmapsto(-r,x,s,y)
 \longmapsto(-r,s,x,y).
\end{aligned}
\]
The six exponential exponents sum to zero. The three Fourier
prefactors multiply to \(G_r(s)G_r(x)/G_r(y)\), using
\(G_{-r}(y)=G_r(y)^{-1}\). Thus
\[
 K_4(r,s,x,y)=\frac{G_r(s)G_r(x)}{G_r(y)}
                                 K_4(-r,s,x,y). \tag{110.10}
\]
Centering the general I by \(z\mapsto z+(c-a)/2\) proves
(110.7). All intermediate formulas have a common nonsingular
convergence neighborhood of the origin in \(r,s,x,y\), which
justifies the composition before continuation.

## 110.6 The remaining period shifts are explicit

For the ordered left product in (110.2), the two integrals in
(110.5) have centered parameters
\[
\begin{gathered}
 r=-g/2,\qquad
 s_1=-\Omega/2-g/2-h,\qquad s_2=\Omega/2-g/2-h,\\
 x=n/2+g/2+l,\qquad y=-\Omega\omega/(2\pi).
\end{gathered}
\]
Their centering prefactors are \(e^{\pi ipy/\Omega}\) and
\(e^{\pi i(n+p)y/\Omega}\), respectively.

For the right product labels
\((p',q',s')=(-g-l,l,g+h+l)\), the corresponding formal
four-gamma parameters have
\[
 r'=g/2,\qquad s'_1=x-A,\quad s'_2=x+B,\qquad
 x'=n/2+g/2+h=-s_1-B=-s_2+A.
 \tag{110.11}
\]
Away from endpoint choices, its principal frequency can be
chosen with \(y'=-y\). Euler reflection, P, and reflection of
the integration variable send the left integrals to kernels
with parameters
\[
 (g/2,x,x'+B,-y),\qquad (g/2,x,x'-A,-y).
\]
The right product would instead require
\[
 (g/2,x-A,x',-y),\qquad (g/2,x+B,x',-y).
\]
The two pairs are different. Their sine coefficients, gamma
prefactors and contour corrections cannot be dropped.
At the frequencies admitted by (110.6b), both finite sums
have now been expressed by these integrals, so a correctly
normalized relation between the four kernels would prove the
corresponding Fourier components of C.

There are also the excluded frequencies for \(g>1\) and
the other index ranges. A generic change of \(\omega\)
destroys the exact n-shift multiplier in (110.4), so analytic
continuation in frequency alone does not fill that gap.
The continuous Euler symmetry supplies neither the required
period-shift relation nor this extension by itself. Section 111
supplies the additional contour primitive and induction.

The accompanying checker verifies (110.2) exactly on 276 rational
phase examples that all have nonzero cubic residuals, and verifies
the six-step Euler word by exact exponent arithmetic. Independent
double-sine checks cover signed samples, the off-real two-ratio
shift, every extra residue in the selected test ranges, and the
diagonal cancellation at 3,5,7. Optional numerical quadrature checks
both the continuous Euler identity and the corrected product formulas;
they are regression checks, not interval certificates. At 80 nodes
and cutoff 12, the Euler discrepancy is \(3.90\cdot10^{-16}\),
the first product discrepancy is \(2.45\cdot10^{-13}\), and
the shifted-interval product discrepancy is \(2.90\cdot10^{-10}\).
The latter also checks the coincident-diagonal residue to 28-digit
working precision. The runs use less than 30 MiB peak RSS.

These are uniform analytic reductions and identities. The finite
transformation (110.2) is completed by the additional arguments
in Section 111.

---

# 111. Infinitude: Fourier induction and the exact Frobenius action

**Theorem.** Let n be odd and at least 3. If
\(-1\in\langle2\rangle\subset(\mathbb Z/n\mathbb Z)^\times\),
the analytic phases of Section 93 satisfy every cubic identity.
They therefore give a complex spherical fusion category with the
cyclic Haagerup--Izumi fusion rules. In particular,
\[
 \boxed{\text{such categories exist at every }n=2^m+1,\quad m\ge1.}
 \tag{111.1}
\]
Algebraic conjugation also supplies pseudo-unitary categorifications
at these orders. Unitarity is not asserted.

The input already proved in Sections 93--95 is an algebraic,
norm-normalized phase tuple satisfying all Q and carrying a field
automorphism \(\sigma(W_a)=W_{2a}\), with \(\sigma(\delta)=\delta\).
Section 110 provides the two product-contour formulas and the
continuous Euler identity. The new ingredients below are the missing
period-shift relation, an induction removing the excluded Fourier
frequencies, and a signed normal form for the remaining indices.

## 111.1 A four-term relation from one exact contour difference

Write \(K_4\) for the centered four-gamma integral of Section 110.5.
For
\[
 g,h\ge1,\quad p=g+h<n,\quad 1\le l\le h,\quad G=g+l,
 \qquad
 R=g/2,\quad X=(n+g)/2+l,\quad Y=(n+g)/2+h,
\]
the needed relation is
\[
\begin{aligned}
 0={}&\sin(\pi h/A)K_4(R,X,Y+B,Z)\\
 &+(-1)^{G+1}\sin(\pi p/A)e^{-2\pi iZA/\Omega}
                              K_4(R,X,Y-A,Z)\\
 &+(-1)^p\sin(\pi G/A)e^{-\pi iZA/\Omega}
                              K_4(R,X-A,Y,Z)\\
 &-\sin(\pi l/A)e^{-\pi iZB/\Omega}
                              K_4(R,X+B,Y,Z).
\end{aligned}\tag{111.2}
\]
It is a meromorphic identity with separating-contour conventions.
For the application below, \(|\Re Z|<(\Omega-g)/2\).

Here is an explicit proof, including a domain in which the contour
shift has no residue. Begin with general
\[
 u=\Omega/4+(R+X)/2,\qquad v=\Omega/4+(R-X)/2
\]
and set
\[
\begin{gathered}
 \zeta=u-B+z,\quad \eta=u-A-z,\quad
 \theta=v-B+Y+z,\quad \nu=v-Y-z,\\
 c=2u-\Omega,\quad D=v+Y-u,\quad E=c+D,\quad
 f=u-v-A+Y.
\end{gathered}
\]
Thus \(\eta+\zeta=c\), \(\eta+\theta=E\), and
\(\eta-\nu=f\). In this proof only, abbreviate
\[
 a(t)=\sin(\pi t/A),\qquad b(t)=\sin(\pi t/B),\qquad
 \lambda=e^{2\pi iZB/\Omega}.
\]
Use the four coefficients
\[
 \kappa_1=\frac{a(f-c)}{a(D)},\quad
 \kappa_2=\lambda\frac{b(E)}{b(D)},\quad
 \kappa_3=-\lambda\frac{b(c)}{b(D)},\quad
 \kappa_4=\frac{a(E-f)}{a(D)}.
\]
Let \(T_i(z)\) be \(e^{2\pi iZz/\Omega}\) times the four
gamma products in the following table:

| i | gamma product in \(T_i\) |
|---:|---|
| 1 | \(\gamma(\zeta)\gamma(\eta+\Omega)\gamma(\theta+B)\gamma(\nu)\) |
| 2 | \(\gamma(\zeta+\Omega)\gamma(\eta)\gamma(\theta+B)\gamma(\nu)\) |
| 3 | \(\gamma(\zeta+B)\gamma(\eta)\gamma(\theta+\Omega)\gamma(\nu)\) |
| 4 | \(\gamma(\zeta+B)\gamma(\eta+\Omega)\gamma(\theta)\gamma(\nu)\) |

Define the primitive
\[
 P(z)=e^{2\pi iZz/\Omega}
       \gamma(\zeta)\gamma(\theta)\gamma(\eta+\Omega)\gamma(\nu+B).
\]
The gamma shifts give the pointwise meromorphic identity
\[
 \boxed{\sum_{i=1}^4\kappa_iT_i(z)=P(z+B)-P(z).}
 \tag{111.3}
\]
For verification, divide by
\(-8e^{2\pi iZz/\Omega}
 \gamma(\zeta)\gamma(\eta)\gamma(\theta)\gamma(\nu)\).
The identity becomes
\[
\begin{aligned}
 &\kappa_1a(\eta)b(\eta)a(\theta)
 +\kappa_2a(\zeta)b(\zeta)a(\theta)
 +\kappa_3a(\zeta)a(\theta)b(\theta)
 +\kappa_4a(\zeta)a(\eta)b(\eta)\\
 &\hspace{20mm}=-b(\eta)
       \{\lambda a(\zeta)a(\theta)+a(\eta)a(\nu)\}.
\end{aligned}
\]
The coefficient of \(\cos(\pi\eta/B)\) on the left vanishes
by \(\kappa_2b(c)+\kappa_3b(E)=0\). Its remaining coefficient
reduces to
\(\kappa_1a(\theta)+\kappa_4a(\zeta)=-a(\nu)\),
by the ordinary sine addition formula. This proves (111.3).

To integrate it legitimately, one nonempty initial domain is
\[
 u=\Omega/2+\epsilon,\quad v=B/2+\epsilon,\quad
 Y=A/2+\eta_0,\quad \Re z=-n/2,
 \qquad 0<\epsilon<A/4,\quad 0<|\eta_0|<\epsilon .
\]
The real parts of \(\zeta,\eta,\theta,\nu\) on this line are
\(\epsilon,\epsilon,\epsilon+\eta_0,\epsilon-\eta_0\).
Every table entry therefore has a separating vertical contour.
For P, the first right poles are at distances
\(\Omega+\epsilon\) and \(B+\epsilon-\eta_0\) from this
line, both greater than B. Thus moving its contour by B
crosses no pole. For
\(|\Re Z|<(A-4\epsilon)/2\), the horizontal boundaries decay
exponentially as well. Integration of (111.3) consequently gives zero.

The four table integrals, with measure \(dz/(i\sqrt\Omega)\),
are respectively
\[
\begin{gathered}
 e^{2\pi iZB/\Omega}K_4(R,X,Y+B,Z),\qquad
 e^{-2\pi iZA/\Omega}K_4(R,X,Y-A,Z),\\
 e^{-\pi iZA/\Omega}K_4(R,X-A,Y,Z),\qquad
 e^{\pi iZB/\Omega}K_4(R,X+B,Y,Z).
\end{gathered}
\]
This follows by the translations \(z\mapsto z-B,z+A,z+A/2,
z-B/2\) in the four original centered kernels, respectively.
The resulting identity continues meromorphically with its
separating contours.

At the HI parameters,
\[
 c=G-B,\quad D=h-l,\quad E=p-B,\quad f=p+l-B.
\]
For \(h>l\), substitute
\[
 b(p-B)=(-1)^p a(p),\quad
 b(G-B)=(-1)^G a(G),\quad
 b(h-l)=(-1)^{h-l+1}a(h-l)
\]
and cancel the common factors. This is (111.2).
For \(h=l\), one has \(X=Y\); (110.9) makes its first and
fourth terms cancel, and its second and third terms cancel.
Thus this case does not require division by \(\sin(\pi(h-l)/A)\).

For completeness, there is no final contour pinch in this
specialization. The four lists of pair sums of opposite gamma
parameters are
\[
\begin{array}{c|c}
 1&(A+G,\ B-l,\ \Omega+p,\ -h)\\
 2&(A+G,\ B-l,\ p,\ \Omega-h)\\
 3&(G,\ \Omega-l,\ A+p,\ B-h)\\
 4&(\Omega+G,\ -l,\ A+p,\ B-h).
\end{array}
\]
The possibly negative entries \(-h,-l,B-h,B-l\) cannot be
of the form \(-rA-sB\) with \(r,s\ge0\): \(A>n\), and
B is irrational. This also justifies the displayed continued
values when same-side poles have merged.

## 111.2 The admitted Fourier coefficients of every ordered cubic vanish

There is a signed version of (93.1) particularly suited to
the same convergence range. Let
\(\omega_R\equiv2\pi j/n+\pi(-g-1)\pmod{2\pi}\) be principal.
If \(|\omega_R|<\pi(1-g/\Omega)\), then
\[
 \boxed{
 \widehat u_{-g}(j)=
 -B e^{ig\omega_R/2}
 \gamma\!\left((\Omega-g)/2+\Omega\omega_R/(2\pi)\right)
 \gamma\!\left((\Omega-g)/2-\Omega\omega_R/(2\pi)\right).
 }\tag{111.4}
\]
Indeed, use \(h=-g\) in the kernel identity (93.3) and
sample on \(0,\ldots,n-1\). Formula (110.3) has no patch.
The rectangle has no noninteger poles, and the two-gamma
integral already has a separating vertical line
\(-\epsilon+i\mathbb R\), \(0<\epsilon<1\).
The horizontal boundaries vanish under the displayed
frequency condition. The two-gamma Fourier formula and
\[
 2\sin(-\pi g/A)\gamma(g)=(-1)^gF(-g)
\]
give precisely (111.4).

Now use the two product formulas from Section 110 in (110.2).
Put
\[
 \omega_L=\omega_{g,-j}=-\omega_R,\qquad
 Z=\Omega\omega_L/(2\pi),\qquad
 D_0(Z)=\gamma((\Omega-g)/2+Z)\gamma((\Omega-g)/2-Z).
\]
The admitted frequencies exclude the ambiguous endpoints,
so these branch choices are compatible. Apply (110.10),
(110.9), and reflection of the integration variable to the
two left product integrals. They become the first two
kernels of (111.2); the two right product integrals are its
last two kernels.

Here is the full coefficient normalization. After the common
factor \(-2\sqrt\Omega\) from the product formulas is removed,
the four coefficients in the bracket of (110.2) are
\[
 M\left(
 \sin(\pi h/A),\
 (-1)^{G+1}\sin(\pi p/A)e^{-2\pi iZA/\Omega},\
 (-1)^p\sin(\pi G/A)e^{-\pi iZA/\Omega},\
 -\sin(\pi l/A)e^{-\pi iZB/\Omega}
 \right), \tag{111.5}
\]
where the common factor is
\[
 M=\frac{B(-1)^{g+h(l+1)}F(G)}{dF(l)}
                          e^{\pi iZ(A+l-g)/\Omega}.
\]
To check the gamma part explicitly, if
\(s_1=-\Omega/2-g/2-h\), the first Euler multiplier is
\[
 \frac{G_{-g/2}(s_1)G_{-g/2}(X)}{G_{-g/2}(-Z)}
 =\frac{F(p)F(G)}{F(h)F(l)}
       \frac{\sin(\pi h/A)}{\sin(\pi p/A)D_0(Z)}.
\]
The ratio of the second Euler multiplier to the first is
\((-1)^g\sin^2(\pi p/A)/\sin^2(\pi h/A)\).
These identities follow from reflection,
\(\gamma(A+a)=F(-a)\), \(\gamma(B-a)=1/F(-a)\), and
\(2\sin(\pi a/A)\gamma(-a)=(-1)^aF(a)\).
The two sample prefactors simplify to
\[
 c_L=\frac{(-1)^{g+hl+1}F(h)}{dF(p)},\qquad
 c_R=\frac{(-1)^{lp+1}F(G)}{dF(l)}.
\]
Finally (111.4) is
\(\widehat u_{-g}(j)=-B e^{-\pi igZ/\Omega}D_0(Z)\),
and
\(\omega_L\equiv-2\pi j/n+\pi(g-1)\pmod{2\pi}\)
cancels the remaining integer phases. These substitutions
give (111.5) with all four signs and exponentials retained.

Equation (111.2) now proves
\[
 \boxed{
 \sum_k\mathcal C_{g,h}(k,l)e^{-2\pi ijk/n}=0
 \quad\text{at all }n-g+1\text{ frequencies in (110.6b).}
 }\tag{111.6}
\]
This is a uniform exact vanishing result, not a numerical
comparison of four integrals.

## 111.3 Induction removes every excluded frequency

**Proposition.** At every odd n, the analytic matrix satisfies
\[
 \mathcal C_{g,h}(k,l)=0
 \quad\text{whenever}\quad
 g,h\ge1,\quad g+h<n,\quad 1\le l\le h,
 \quad k\in\mathbb Z_n. \tag{111.7}
\]

Fix n and induct on g. When \(g=1\), (111.6) covers all n
Fourier coefficients, proving the base case. In general, its
excluded frequencies form a consecutive cyclic block of
length \(g-1\): the principal integers
\(n\omega_R/\pi\) have step 2, and (110.6b) removes their
central interval. Consequently, with
\(\zeta_n=e^{2\pi i/n}\), the residual sequence has the form
\[
 \mathcal C_{g,h}(k,l)=\zeta_n^{ak}P(\zeta_n^k),
 \qquad \deg P\le g-2, \tag{111.8}
\]
for some integer a and polynomial P.

We exhibit \(g-1\) distinct zeros, at \(k=1,\ldots,g-1\).
If the cross-sum matrix (34.3) has a zero, the collision
reduction of Section 34 already supplies C from Q. Otherwise
its balanced residual can be permuted and translated without
changing whether it vanishes. Explicitly, for the triples in
(34.2), put
\[
 S=\sum_m\prod_iW_{m+a_i}\prod_jW_{c_j-m},\qquad
 P_9=\prod_{i,j}W_{a_i+c_j}.
\]
The cross-free residual has the exact factorization
\[
 \mathcal C_{g,h}(k,l)=
 \frac{W_{-g-h}W_gW_h}{\delta^5}
             \{\delta^2S-(\delta-1)P_9\}. \tag{111.8a}
\]
Indeed, away from its origin correction the core is
\(\mathsf B_{a,b}=\delta^{-1}W_aW_{b-a}W_{-b}\).
Substituting this in C gives (111.8a) by inverse norms.
Its prefactor is nonzero. Both S and \(P_9\) are invariant
under the indicated permutations and opposite translations.
The collision reductions likewise use the algebraic inverse
norms and dimension equation, so they apply at \(\delta<0\).

For \(1\le k<g\), use
\[
 (g,h,k,l)\longmapsto
 \begin{cases}
 (k,h,g,l+g-k),&l+g-k\le h,\\
 (k,n-h-k,k+h-l,n-g-l),&l+g-k>h.
 \end{cases} \tag{111.9}
\]
In the first case, permute the rows of the balanced pair as
\((1,0,2)\), keep its columns, and translate its first row
entry to zero. In the second, use rows \((2,0,1)\) and
columns \((2,1,0)\), then normalize in the same way.
The indices here refer to the positions \(0,1,2\) in (34.2).

Both resulting quadruples have first index k, strictly less
than g, and are in the ordered range of (111.7).
For the second case,
\[
 k+(n-h-k)=n-h<n,\quad
 1\le n-g-l\le n-h-k;
\]
the last inequality is equivalent to \(l+g-k\ge h\).
The first case satisfies the ordered inequalities directly.
The induction hypothesis therefore makes each residual zero.
Its phase normalization is nonzero in the cross-free case,
so the original residual vanishes too.

The \(g-1\) numbers \(\zeta_n,\ldots,\zeta_n^{g-1}\)
are distinct, including when n is composite. Equation (111.8)
forces \(P=0\). This completes the induction and proves
(111.7). No analytic continuation into the excluded frequency
range is required.

## 111.4 A signed ordered normal form

**Lemma.** Every cross-free balanced pair of triples on
\(\mathbb Z_n\) can be put in the ordered form of (111.7)
by permutations and opposite translation of the triples,
possibly after simultaneously negating all six entries.

Let \(X_{ij}\in\{1,\ldots,n-1\}\) represent \(a_i+c_j\).
Balance implies
\[
 X_{00}+X_{11}+X_{22}\in\{n,2n\}.
\]
If the sum is n, negate both triples; the new sum is \(2n\).
We claim there are \(i\ne j\) with \(X_{ij}\ge X_{jj}\).
Otherwise each diagonal entry would be the strict maximum
of its column. The three row labels would then be distinct.
Let \(d_j>0\) be the forward cyclic gap from \(a_j\) to the
next row label. These gaps sum to n. The strict-maximum
property, together with the absence of cross zeros, gives
\[
 X_{jj}+d_j>n.
\]
Summing gives \(\sum_jX_{jj}>2n\), a contradiction.

Choose such i,j and let r be the remaining position. Use
the row and column ordering \((i,r,j)\), then translate the
first row label to zero. The resulting indices satisfy
\[
 g=n-X_{rr},\qquad h=n-X_{jj},\qquad l=n-X_{ij}.
\]
Their sum is
\[
 g+h=2n-X_{rr}-X_{jj}=X_{ii}<n,
\]
and \(1\le l\le h\). All the remaining nonzero requirements
follow from cross-freeness. This proves the lemma.

## 111.5 Frobenius supplies the sign and reconstruction gives the categories

Suppose \(2^m\equiv-1\pmod n\). The exact field automorphism
of Section 95 satisfies
\[
 \sigma^m(W_a)=W_{-a},\qquad
 \sigma^m(\mathsf B_{a,h})=\mathsf B_{-a,-h},\qquad
 \sigma^m(\delta)=\delta. \tag{111.10}
\]
Thus simultaneous negation of every cubic index preserves
vanishing of its residual. This conclusion uses the exact
characteristic-zero automorphism, rather than merely a
residue congruence.

By the lemma, every cross-free cubic is equivalent, with
this optional sign change, to an ordered cubic. Proposition
(111.7) proves all those ordered cubics. Every collision and
boundary case follows from the already proved Q identities,
as in Section 34. Hence all C hold at n.

The core \(\mathsf A=\mathsf B/(\delta-1)\) has the required
order-three symmetry, axes and column sum. The polynomial
identity (52.1) supplies the quartic equations as well.
Therefore the reconstruction theorem gives a spherical fusion
category with the cyclic HI fusion rules and noninvertible
categorical dimension \(\delta=-1/d\).
The external reconstruction result permits this negative
embedding: [Evans--Gannon, Theorem 2(a)](https://arxiv.org/pdf/1506.03546).

All matrix entries are algebraic by Section 93. A field
embedding taking \(\delta\) to its positive conjugate d
extends to the coefficient field and gives a spherical
categorification with dimensions 1 and d. Its global
dimension is its Frobenius--Perron dimension, so this
conjugate is pseudo-unitary. The Hermitian condition required
for unitarity by Evans--Gannon's Theorem 2(c) is a further
condition not proved here.

Finally, \(n=2^m+1\) is odd and satisfies
\(2^m=-1\pmod n\), for every \(m\ge1\).
These n are unbounded, and the corresponding ranks \(2n\)
are distinct. This proves (111.1) and the requested
infinitude of complex categorifications.

## 111.6 Reproducible proof audits

The checker independently expands (111.3) as a rational
Laurent identity in eight formal variables; its numerator
is exactly zero. It also checks the exact cross-free residual
factor (111.8a) on 572 rational phase examples away from the
solution scheme. It checks the descending permutations and
consecutive frequency blocks in 202,368 cases through
order 35, and the constructive signed normal form for all
95,496 cross-free quadruples through odd order 17.
Exactly half of the latter use negation.

Separate 32-digit calculations at 3,5,7,9 verify the off-real
gamma primitive, the signed finite Fourier formula, and
152 full coefficient quadruples in (111.5), including the
coincident case \(h=l\). The largest reported coefficient
relative error is below \(2.1\cdot10^{-31}\). These numerical
checks audit normalization and branches; the displayed
analytic and combinatorial proofs establish uniformity.
The combined checker takes 18.81 seconds and 57.88 MiB peak RSS.

A further 32-digit order-5 audit uses \(g=1,h=l=2\), where
the shifted product has a genuine noninteger double pole.
The full double residue, calculated from gamma Laurent
coefficients, agrees with the independently differentiated
cosecant kernel to relative error \(1.1\cdot10^{-32}\).
The coincident integer patch error is below \(3.1\cdot10^{-33}\);
the 80-node corrected integral discrepancy is
\(6.6\cdot10^{-12}\). This separate numerical audit takes
83.09 seconds and 29.07 MiB peak RSS.

The result is infinitude of complex spherical, and
pseudo-unitary, cyclic HI categorifications. Unitary
existence, all odd orders outside the stated Frobenius
criterion, and the stronger class-field/Stark identifications
remain separate questions.

---

## Available mathematical software

In addition to PARI/GP and the Python tools used above, this machine has
Magma at `/home/tzuchen/Software/Magma/magma`, Macaulay2, Singular,
Prover9, Vampire, Julia with TensorCategories and Oscar, and Mathematica
with Anyonica. The inspected package files identify TensorCategories
0.7.2 and Anyonica 0.9.20.1; Oscar 1.8.1 and 1.8.2 are both present in
the Julia package cache. Julia's `v1.12` environment lists TensorCategories
as a direct dependency. Anyonica is installed at
`/home/tzuchen/.Mathematica/Paclets/Repository/Anyonica-0.9.20.1`.
Its `FusionRingHI` constructs the fusion ring; its existence does not
itself provide associators. TensorCategories includes pentagon checking
and saved order-3 Haagerup examples. These capabilities are available for
independent categorical checks of future constructions. Native FLINT
3.4.0 is also available (`pkg-config --modversion flint`). The user
requests notification whenever a useful package cannot be found.
The user also has other memory-intensive workloads and requests
notification before a computation needs more than half of system
memory. The current system reports approximately 62.5 GiB total;
use approximately 31 GiB across this research's simultaneous jobs
as the notification threshold, and check available memory before
starting a large calculation. No such reservation is currently needed.

## Files from this exploration

- [The infinitude proof audits](hi_infinitude_fourier_checks.py)
  and [their results](hi_infinitude_fourier_checks_results.txt):
  The exact Laurent identity for the contour primitive, both descending
  cubic permutations, the signed ordered normal form, and independent
  signed-Fourier and coefficient-normalization checks for Section 111.

- [The double-pole audit](hi_infinitude_double_pole_check.py)
  and [its results](hi_infinitude_double_pole_check_results.txt):
  A genuine merged noninteger pole at order 5, its full residue,
  and the coincident-diagonal correction.

- [The product Fourier and Euler checks](hi_shintani_column_products.py),
  [their results](hi_shintani_column_products_results.txt), and
  [the shifted-interval results](hi_shintani_column_products_right_results.txt):
  Exact off-solution reindexing and Euler-word checks, signed-column
  interpolation, two-ratio shifts, full residue cancellations in the
  ordered range, and numerical checks of the continuous integrals.

- [The lift-polynomial expansion](hi_lift_q_polynomials.py),
  [its independent checks](hi_lift_q_polynomial_checks.py),
  and [the check results](hi_lift_q_polynomial_checks_results.txt):
  First-Q lift generators, their derivative and character decompositions,
  and an exact full-cubic example showing the failure of unrestricted
  character projection.

- [The Q-plus-lift search log](hi_frobenius_ql_small_L2_results.txt),
  [the independent replay log](hi_frobenius_ql_small_replay_results.txt),
  and [the order-13 degree-two separator bundle](hi_frobenius_ql_batch13_L2_certificates.json.gz):
  Finite certificates using the stronger uniform hypotheses, and the
  completed obstruction to multiplier degree two.

- [The Frobenius quotient batch search](hi_frobenius_q_batch.py),
  [its independent replay](hi_frobenius_q_replay.py),
  [the order-13 bundle](hi_frobenius_q_batch13_L3_certificates.json.gz),
  [the order-15 degree-three bundle](hi_frobenius_q_batch15_L3_certificates.json.gz),
  [its compact separator](hi_frobenius_q_15_q1_1_2_2_bound3_obstruction.json),
  and [the partial degree-four bundle](hi_frobenius_q_batch15_L4_certificates.json.gz):
  Exact finite Q-to-C certificates modulo norm and canonical Frobenius,
  with completed bounded obstructions separated from resource stops.

- [The uniform orbit-bound checker](hi_frobenius_word_bound.py)
  and [its results](hi_frobenius_word_bound_results.txt):
  Exact binary-rotation checks accompanying the uniform degree-five
  lower bound for every order \(2^r-1\), \(r\ge11\).

- [The shared Laurent batch search](hi_laurent_q_batch.py),
  [the independent replay](hi_laurent_q_replay.py),
  [order-13 certificates](hi_laurent_q_batch13_certificates.json.gz),
  [order-15 certificates and obstruction](hi_laurent_q_batch15_certificates.json.gz),
  and [the compact degree-six separator](hi_laurent_q_15_q1_1_1_1_bound6_obstruction.json):
  All 30 cross-free orbit certificates at 13; 63 positive identities
  and an explicit obstruction to the proposed degree-six bound at 15.
  Search and replay logs have the corresponding batch filenames.

- [The modular recognition note](hi_modular_lagrangian_recognition_20260907.md):
  Full conditional reconstruction of cyclic HI from the prescribed
  modular matrices and Lagrangian algebra, including positivity,
  covariance, and the untwisted pointed associator.

- [The recognition note](hi_odd_bimodule_recognition_20260907.md):
  Conditional odd-order recognition, the canonical Q-system
  intertwiner, the principal graph, and the flatness literature audit.

- [The lattice and quadratic-form verifier](hi_pell_metric_groups.py)
  and [its results](hi_pell_metric_groups_results.txt):
  Exact checks for Section 105, with numerical Gauss sums, small
  modular matrices and the invariant vector.

- `hi_convolution_balanced_witt.py`, `hi_convolution_balanced_witt_results.txt`:
  Degree-11 balanced lift errors and their exact comparison with the
  matrix obstruction, including off-Q correction terms.

- `hi_laurent_q_certificate.py`, `hi_laurent_q_replay.py`, their result logs,
  `hi_laurent_q_*_certificate.json`, and
  `hi_laurent_q_13_bound5_obstruction.json`:
  Bounded Laurent multiplier searches, seven independently replayed
  single-cubic identities, and a separating functional proving the
  order-13 degree-5 obstruction. Incomplete search logs are distinguished
  from completed bounded nonmembership results.

- `hi_convolution_q_digits.py`, `hi_convolution_q_digits_results.txt`:
  Exact paired-Q norm identities, exhaustive small residue checks,
  perturbed precision tests, and Q on saved convolution lifts modulo 64.

- `hi_convolution_witt_q.py`, `hi_convolution_witt_q_results.txt`:
  Explicit residue-field formulas for the convolution lift modulo 4
  and its first Q errors, checked against independent integer-ring arithmetic.

- `hi_convolution_paley_obstruction.py`, its results and JSON certificates:
  The uniform two-value norm-valuation identity, independent convolution
  checks, and explicit counterexamples to norm-only completion at
  43,67,131,4099, including norm preservation modulo 1024 at the last order.

- `hi_convolution_native_filter.py`, `hi_convolution_native_filter_results.txt`,
  `hi_convolution_native_filter1921_results.txt`, and
  `hi_convolution_native_*_certificates.json`:
  Native exhaustive first-obstruction censuses, including 85,197,125
  tuples at 27, followed by independent norm lifts and complete residue Q.

- `hi_convolution_mod8_ideal.py`, `hi_convolution_mod8_ideal_results.txt`,
  `hi_convolution_mod8_ideal57_results.txt`, and
  `hi_convolution_mod8_ideal9_results.txt`:
  Complete integer strong-basis cubic containments modulo 8 at 3,5,7;
  the order-9 reductions timed out and are explicitly incomplete.
  The separate `hi_convolution_mod8_ring_crash_results.txt` is a failed
  direct-coefficient-ring run and supplies no mathematical certificate.

- `hi_convolution_norm_obstruction.py`,
  `hi_convolution_norm_obstruction_results.txt`, and
  `hi_convolution_first_obstruction_results.txt`:
  Exact first-obstruction formulas, origin estimates, complete
  norm/Frobenius censuses through order 17, and the eight false
  order-15 points which survive modulo 4 but fail modulo 8.

- `hi_convolution_ideal.py`, `hi_convolution_ideal_results.txt`,
  `hi_convolution_ideal7_results.txt`, and `hi_convolution_ideal9_results.txt`:
  Exact characteristic-zero norm/convolution-to-Q ideal containments
  at orders 3,5,7 and the explicitly incomplete order-9 attempt.

- `hi_char2_paley_matrix.py`, `hi_char2_paley_matrix_results.txt`:
  Exact finite checks of the uniform Legendre-symbol counterfamily
  in Section 96: full Q, diagonal C, Frobenius, inverse products,
  explicitly counted failing cubics, and the failed phase cocycle.

- `hi_convolution_hensel.py`, `hi_convolution_hensel_results.txt`:
  Exact arithmetic modulo \(2^{24}\), contraction-rate checks,
  arithmetic Frobenius versus label doubling, all Q/C for three
  known finite certificates, and a non-Q negative control.

- `hi_shintani_fourier.py`, `hi_shintani_fourier_results.txt`:
  Independent numerical checks of the uniform finite Fourier
  evaluation, complete residue cancellation, every quadratic,
  the canonical chamber, and the convolution identity used to
  prove unit reduction and canonical Q nonemptiness in characteristic two.

- `hi_ghost_growth.py`, `hi_ghost_growth_results.txt`:
  Exact fusion-gauge product invariants and independent integral
  checks of the uniform ghost-amplitude estimates through order 1001.

- `hi_ghost_trace_bound.py`, `hi_ghost_trace_bound_results.txt`:
  Normalized cup-stack bounds, improved off-pentagon estimates,
  and rational replay of the stronger finite correction criterion.

- `hi_transparent_residual_bound.py`, `hi_transparent_residual_bound_results.txt`:
  Uniform full-pentagon residual formulas, off-solution categorical
  regressions, inverse and Fourier norm checks, and exact rational
  replay of the finite correction inequalities.

- `hi_shintani_correction_results.txt`:
  Complete FLINT/Arb verification of the sufficient full-associator
  correction criterion at 3, 7, and 11, using nine extrapolation levels.

- `hi_shintani_correction_checks_results.txt`:
  Independent integral comparisons for all nine new half-sample balls.

- `hi_nonunitary_pentagon_correction.py`, `hi_nonunitary_pentagon_correction_results.txt`:
  Exact boundary, spanning-tree, and constant checks for the general
  linear correction theorem, with off-pentagon algebraic-trace,
  derivative, and iteration regressions for both Fibonacci dimension roots.

- `hi_shintani_boundary_series.c`, `hi_shintani_boundary_series_results.txt`:
  FLINT/Arb enclosures of canonical double-sine samples using elementary
  series, rigorous tails, and a uniform real-axis extrapolation bound;
  complete residual bounds at 3, 7, and 11.

- `hi_shintani_boundary_series.py`, `hi_shintani_boundary_series_checks_results.txt`:
  Exact rational extrapolation identities and independent numerical
  comparisons of the series and printed balls with double-sine integrals.

- `hi_reduced_affine_associator.py`, `hi_reduced_affine_associator_results.txt`:
  Exact reduced pentagons, affine and general monomial support
  uniqueness, explicit balanced unitary HI trials, and the uniform
  invertible-output obstruction which survives changes of phases
  and augmented blocks.

- `hi_right_pentagon_correction.py`, `hi_right_pentagon_correction_results.txt`:
  Exact transport and constant checks for the uniform correction theorem,
  with independent off-pentagon cochain, derivative, and iteration
  regressions on Fibonacci fusion spaces. No unbounded HI trial family
  has been constructed.

- `hi_unitary_handle_bound.py`, `hi_unitary_handle_bound_results.txt`:
  Independent numerical tensor-functor tests of the proved off-pentagon
  handle bound, including balanced and unbalanced unit-channel data.

- `hi_associahedron_path_bound.py`, `hi_associahedron_path_bound_results.txt`,
  `hi_associahedron_path_bound_certificates.json`:
  Exact, replayed spanning-tree and face certificates for the
  reassociation operator bound on four through seven tensor factors.

- `hi_pentagon_stability.py`, `hi_pentagon_stability_results.txt`:
  Exact free-word verification of the five-object boundary relation,
  canonical face transports and correction constants, with independent
  small unitary-matrix regressions. No unbounded HI correction
  certificate has been constructed.

- `hi_alltop_operator_limit.py`, `hi_alltop_operator_limit_results.txt`:
  Exact five-cycle character sums and the uniform Alltop operator
  obstruction in Section 84, with explicitly labelled numerical probes.

- `hi_char2_cayley_geometry.m`, `hi_char2_cayley_geometry_results.txt`:
  Exact checks of the uniform conic, trace-zero, and projective Cayley
  parametrization in Section 83, through coordinate order 513.

- `hi_char2_cayley_trace.py`, `hi_char2_cayley_trace_results.txt`:
  The uniform trace-extension identities and exact first-Q failures
  at orders 513 and 32769 for every order-9 and order-33 input.

- `hi_char2_cayley_degree2.py`, `hi_char2_cayley_degree2.cpp`,
  `hi_char2_cayley_degree{2,4}_*.json`, `.txt`, and their result files:
  Binary-linear exporters for arbitrary algebraic-degree bounds and
  exact finite-field searches. The historical script name does not
  restrict its `--degree` argument to two.

- `hi_char2_cayley_boundary.py`, `hi_char2_cayley_classify.py`,
  and their order-9 and order-33 result files:
  Complete infinity-chart searches and exact scalar-orbit counts.

- `hi_char2_cayley_verify.py` and `hi_char2_cayley_verify*_results.txt`:
  Conversion to the existing independent complete-Q/C GP verifier,
  with five order-33 orbit certificates and two order-9 certificates.

- `hi_char2_ray_count33_results.txt`:
  Certified class-number and unit-index calculation matching the new
  complete canonical phase count of 100.

- `hi_char2_normal_basis_candidate.m`, `hi_char2_linear_cayley.m`,
  `hi_char2_cayley_function_fit.py`, and their result files:
  Exact rejection of the tested short normal-basis, affine-linear,
  and single-feature semilinear formulas at order 33.

- `hi_char2_cayley_semilinear_rank.py`, its results, and
  `hi_char2_cayley_semilinear_rank_certificates.json`:
  The exact necessary-and-sufficient single-feature criterion and
  its rejection of all 100 order-33 points even for arbitrary h.

- `hi_char2_cayley_permuted_fit.py`,
  `hi_char2_cayley_permuted_fit{9,33}_results.txt`, and
  `hi_char2_cayley_two_feature33_results.txt`:
  All binary Frobenius-commuting input permutations, the reciprocal
  boundary chart, and exact one- and two-feature interpolation tests.

- `hi_char2_cayley_two_feature_coverage.py` and its result file:
  A 24-dimensional common-fiber and 256-pattern certificate that the
  tested two-feature union covers the entire finite order-33 chart;
  fitting that union imposes no additional HI constraint at this order.

- `hi_char2_cyclic_basis.py`, `hi_char2_cyclic_basis_results.txt`:
  Exact Weyl-basis coefficients, support and rank comparisons, and the
  centered cluster-monomial basis probe in Section 82.

- `hi_char2_cyclic_pentagon.m`, `hi_char2_cyclic_pentagon_results.txt`:
  Exact checks of the uniform finite cyclic quantum-dilogarithm matrix
  and its fifth-order conjugation action in Section 81.1.

- `hi_char2_transfer_spectrum.py`, `hi_char2_transfer_spectrum_results.txt`:
  Sparse-transfer spectral comparison on saved orders 3,9,27, including
  the complete Jordan correction of Section 81.2.

- `hi_char2_cyclic_phase_probe.m`, `hi_char2_cyclic_phase_probe_results.txt`:
  Failed phase extractions from the cyclic operator's eigenprojectors;
  the parameter convention is \(\delta=\rho^{-1}\).

- `hi_shintani_abel_plana.py`, `hi_shintani_abel_plana_results.txt`:
  Independent checks of the separate A/B/n shifts and the convergent
  unweighted contour formula in Section 80. The uniform target
  evaluations remain unproved.

- `hi_shintani_telescoper.py`, `hi_shintani_telescoper_results.txt`:
  Exact quadratic period primitives, the uniform pole-chain and
  Laurent-degree obstruction for a rational cubic primitive, and
  independent complex double-sine checks.

- `hi_shintani_quadratic_contour.py` and its result file:
  A single absolutely convergent vertical contour for the quadratic
  finite sum, with the extra boundary pair included; checks at and
  away from the RM parameters.

- `hi_char2_canonical_ideal.py`, `hi_char2_canonical_ideal_results.txt`:
  Magma generator and saved benchmark for norm/Q ideals with Frobenius
  covariance imposed. Order 9 completed with length 12; order 27 is
  stopped without a basis or length.

- `hi_char2_phase1519_length.m`, `hi_char2_phase1519_length_results.txt`:
  completed full quadratic-algebra length at 15 and the stopped
  length test at 19, without Frobenius assumptions or an order-19 result.

- `hi_ray_unit19_incomplete_results.txt`:
  Preserved log of the stopped degree-72 unit-search run. The initial
  norm and arithmetic Frobenius checks completed, but the unit-lattice
  search produced no completed selection or additional HI certificate.

- `hi_shintani_canonical.py`, `hi_shintani_canonical_results.txt`:
  exhaustive integer checks of the canonical-lift and sign lemmas,
  and numerical checks of the two finite targets in Section 79.

- `hi_shintani_monodromy.py`, `hi_shintani_monodromy_results.txt`:
  symbolic Bezout and resultant identities, and independent numerical
  checks of the uniform rational shift formulas in Section 78.

- `hi_shintani_beta.py`, `hi_shintani_beta_results.txt`: numerical
  normalization check of the correctly balanced continuous beta integral
  in Section 77.4.

- `hi_shintani_meromorphic.py`, `hi_shintani_meromorphic_results.txt`:
  independent complex-argument factorization, shift, jump, and residue
  checks for Sections 76--77.

- `hi_shintani_single.py` and `hi_shintani_single_results.txt`
  The one-double-sine phase formula, off-RM product comparisons, and
  independent numerical Q/C checks for Section 76.

- `hi_shintani_lens.py` and `hi_shintani_lens_results.txt`
  The fixed-period lens product, intrinsic origin normalization, and
  exact Bernoulli/sign check for the analytic construction of Section 75.

- `hi_char2_scalar_action.py` and `hi_char2_scalar_action_results.txt`
  Complete scalar stabilizers and Frobenius-factor comparisons with the
  quadratic-overorder ray actions at all odd orders through 31.
- `hi_char2_scalar_small_search_results.txt`
  Reconstructed full certificates at 5, 7, 11, and 13 used in the scalar
  comparison. Its maximal-order-only count at 11 is distinguished from
  the correct sum over both overorders in Sections 73 and 74.

- `hi_char2_general_search.py` and `hi_char2_general_search_results.txt`
  General doubling-orbit parametrization and exhaustive complete phase
  classifications at 15, 17, 19, 21, 23, 25, 29, and 31.
- `hi_char2_ray_count.py` and `hi_char2_ray_count_results.txt`
  Certified sums of ray-class degrees over quadratic overorders, with
  exact comparison to all completed counts through 31.
- `hi_char2_phase17_length.m` and `hi_char2_phase17_length_results.txt`
  Magma Q-algebra length 272, proving full characteristic-two completion
  at 17 by comparison with the independently classified cubic scheme.
- `hi_char2_sat81_search_results.txt`
  The completed one-hour SAT attempt, with no SAT/UNSAT conclusion.

- `hi_char2_cubic_frobenius.py` and `hi_char2_cubic_frobenius_results.txt`
  Exact off-solution convolution identities and unique Frobenius-gauge
  recovery across every character twist of all saved finite branches.

- `hi_char2_phase_ideal.py` and `hi_char2_phase_ideal_results.txt`
  Complete characteristic-two Q-to-C ideal containments and nonzero
  phase-algebra lengths at every odd order through 13.
- `hi_char2_quadratic_orbits.py` and `hi_char2_quadratic_orbits_results.txt`
  Exact coverage checks for the uniform linear count of Q orbits through 729.
- `hi_char2_sat.py`, `hi_char2_sat_checks.py`, and their result files
  Native-XOR searches, exact off-solution arithmetic checks through 81,
  and complete independent finite certificates at 3 and 9.


- `hi_char2_firstq_linear.py` and `hi_char2_firstq_linear_results.txt`
  Exact linear elimination of lower Frobenius seeds from the first Q,
  recovery of the saved branches, and finite tests through order 81.
- `hi_char2_ratio_bound.py` and `hi_char2_ratio_bound_results.txt`
  Exact checks of the uniform patched rational-ratio obstruction and
  minimum interpolation degrees for the saved certificates.

- `hi_stark_seedless.gp` and `hi_stark_seedless_results.txt`
  Construction without HI seeds and exact complete Izumi certificates
  for \(n=7,11,13,17,29\), including exact identification of the earlier
  \(n=13,17\) polynomials.

- `hi_stark19_certificate.gp`, `hi_stark25_certificate.gp`,
  `hi_stark199_certificate.gp`, and
  `hi_stark_verify_certificate.py`
  Saved exact matrix data and an independent existence verifier.

- `hi_stark19_results.txt`, `hi_stark199_construction_results.txt`,
  `hi_stark199_cubic_results.txt`, and `hi_certificate_verification_results.txt`
  Complete construction, polynomial-identification, and verification logs.

- `hi_stark_prime_power.gp`, `hi_stark25_artin.gp`,
  `hi_stark_single_root.gp`, `hi_stark25_construction_results.txt`, and
  `hi_stark25_verification_results.txt`
  Prime-power one-root construction, the exact conjugate-prime twist at
  order 25, and its complete independent verification.

- `hi_single_root_checks.gp`, `hi_single_root_results.txt`,
  `hi_prime_power_signs.py`, and `hi_prime_power_signs_results.txt`
  Exact single-root reconstruction and sign-selection checks, and
  independent off-solution tests of the linear sign identity.

- `hi_stark_cubic_batches.py`
  Exact integer-polynomial cubic verification in disjoint local batches.

- `hi_ray_unit_search.gp`, `hi_ray_unit_search_results.txt`,
  `hi_ray_unit199_results.txt`, and `hi_ray_unit_explicit_results.txt`
  Unit-lattice selection with exact full Izumi certificates at eight prime orders; numerical shortest-shell selection is distinguished from exact acceptance.

- `hi_pentagon_operator.gp`, `hi_pentagon_operator.py`, and their result files
  Exact operator certificates and numerical indexing checks for the uniform fifth-order reformulation of the cubic equations.

- `hi_shintani_ghost.py` and `hi_shintani_ghost_results.txt`
  Explicit double-sine construction with fixed signs and high-precision numerical checks; no algebraic seeds or arithmetic reciprocity are assumed.

- `hi_cubic_quartic.py` and `hi_cubic_quartic_results.txt`
  Exact off-solution checks of the uniform cubic-to-quadratic and cubic-to-quartic residual identities.

- `hi_column_barrier.py` and `hi_column_barrier_results.txt`
  Convex construction with a uniform existence and algebraicity proof for one complete quadratic column; further Izumi checks are numerical.

- `hi_column_trace.py`, `hi_column_trace_exact.py`, and their result files
  Numerical scalar and period-40 trace tests, plus exact scalar-completion certificates at orders 3, 5, and 7 using finite-algebra rank comparisons.

- `hi_paley_obstruction.py` and `hi_paley_obstruction_results.txt`
  A symbolic obstruction to an infinite two-value quadratic-character family,
  with complete exact Q and C certificates for its remaining orders 3 and 11.

- `hi_finite_field_transfer.py` and `hi_finite_field_transfer_results.txt`
  Off-solution transfer identities and complete characteristic-2 checks
  of the corrected pentagon criterion, rank-three defect, and order 30.

- `hi_finite_field_certificate.py`, `hi_finite_field_certificate_results.txt`,
  and `hi_finite_field_char2_results.txt`
  Independent complete finite-field certificates, supporting categorical
  lifting rather than only modular rank bounds.

- `hi_char2_frobenius.py`, `hi_char2_frobenius_results.txt`,
  and `hi_finite_field_certificates/*.json`
  Exhaustive Frobenius-covariant searches at 3, 9 and 27, followed by
  independent checks of every cubic for all six Frobenius representatives.

- `hi_char2_elliptic.py` and `hi_char2_elliptic_results.txt`
  A fixed-curve rational-function construction with complete finite
  certificates at 3, 9 and 27, and exhaustive rejection of its proposed
  recurrence at order 81.

- `hi_char2_ray_indices.gp`, `hi_char2_twisted_norm.py`, and their result files
  Certified conjugate-prime and Frobenius relations, and exact norm
  compatibility across the saved order-9 and order-27 branches.

- `hi_char2_small_field_obstruction.py` and its result file
  Exact off-solution checks for the uniform four-element-field and
  quotient inflation obstructions, and the complete F16 search at order 43.

- `hi_char2_conjugate_norm.m`, `hi_char2_conjugate_norm_results.txt`
  Exact diagonal-residual projection under a dimension-conjugating
  involution, the resulting fixed-line and relative-norm-one
  obstructions, and the quadratic-character/Möbius construction test.

- `hi_char2_field_tower.py` and its result file
  Exact checks for the uniform first-phase degree theorem and the
  irreducible cubic construction with prescribed normalized relative norm.

- `hi_char2_partial_completion.py`, `hi_char2_rational_recursion.py`,
  and their result files
  Exact inflation identities and false partial solutions, plus the
  exhaustive rejection of stationary degree-six and single-branch
  degree-three rational preimage recursions.

- `hi_column_fullq.py` and `hi_column_fullq_results.txt`
  The complete order-13 quadratic-to-cubic implication by matching a
  full quadratic modular upper bound with an exact cubic lower bound.

- `hi_column_circuits.py` and `hi_column_circuits_results.txt`
  Uniform prime-order critical-algebra multiplication matrices and exact
  scalar-completion certificates through orders 11 and 13.

- `hi_column_arrangement.gp` and `hi_column_arrangement_results.txt`
  Exact hyperplane-arrangement counts supporting the uniform classification of all one-column solutions.

- `hi_column_counterexample.py` and `hi_column_counterexample_results.txt`
  Exact algebraic obstruction to extending an arbitrary one-column solution to all columns.

- `hi_explicit_ray_unit.gp` and `hi_explicit_ray_unit_results.txt`
  Exact checks of the uniform integral ray-unit construction and its nonzero diagonal quadratic residual.

- `hi_ray_norm.gp` and `hi_ray_norm_results.txt`
  Ray-field norm elements constructed without Stark or HI seeds; no additive Izumi claim.

- `hi_row11_verify.py`, `hi_row11_homogeneous_basis.txt.gz`,
  `hi_row11_basis.txt`, and `hi_row11_verification_results.txt`
  Exact homogeneous Hilbert comparison and the complete order-11 quadratic-to-cubic certificate.

- `hi_diagonal_counterexample.py`, `hi_diagonal_kummer.gp`, and their `_results.txt` files
  An exact physical obstruction to the diagonal-only quadratic reduction, and its failure of the one-root condition.

- `hi_row_ideal.py` and `hi_row_ideal_results.txt`
  Exact quadratic-to-cubic checks in the quotient by cyclic character gauge.

- `hi_amplitude_ideal.py` and `hi_amplitude_ideal_results.txt`
  Exact varying-amplitude elimination and algebraic branch lengths at orders 5 and 7.

- `hi_design_alltop.py` and `hi_design_alltop_results.txt`
  Weighted-design reformulation and checks of the uniform Alltop
  rigidity obstruction.

- `hi_beta_reductions.py`, `hi_quadratic_ideal.py`,
  `hi_composite_signs.py`, and their corresponding `_results.txt` files
  Reproducible beta, ideal-membership and composite sign checks.

- `hi_pell_ray.gp` and `hi_pell_ray_results.txt`
  Exact fixed-field Lucas-family ray arithmetic and maximal-order RM
  characteristics. These arithmetic tests do not assert HI existence.

- `hi_stark19_partial_results.txt`
  Exact field and row-root checkpoint at \(n=19\); full matrix
  verification was not completed in the bounded run.

- `hi_phase_reductions.py` and `hi_phase_reductions_results.txt`
  Reproducible cocycle, binary sign, and Fourier-reduction checks.

- `z17_haagerup_izumi_minpolys.sage`
  Exact reconstructed \(\mathbb Z_{17}\) minimal-polynomial data.

- `z17_stark_test.gp`
  Reproducible exact ray-group, Stark-polynomial, field-isomorphism, discriminant, signature, and short-orbit-relation checks for \(p=17\).

- `z7_stark_test.gp`
  Exact derivation from Evans–Gannon's \(\mathbb Z_7\) solution and the full Stark-orbit comparison.

- `z11_stark_test.gp`
  Reproducible checks for the two \(p=11\) conductors and branch fields.

- `z13_stark_test.gp`
  High-precision \(p=13\) reconstruction and exact ray-field, Stark-orbit, discriminant, and Frobenius-\((2)\) checks.

- `z19_ray_test.gp`
  Exact \(p=19\) class group, ray group, subgroup fields, discriminants, and full Stark-field checks.

- `z19_stark_test.gp`
  High-precision two-branch reconstruction, exact Hilbert-class factorization and full-ray-field checks, plus the numerical Stark-quotient search.

- `haagerup_izumi_class_field_stark_notes.md`
  This handoff.
