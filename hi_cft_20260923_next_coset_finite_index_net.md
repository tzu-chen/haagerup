# Finite-index descent for the actual opposite coset: net theorem and VOA boundary

23 September 2026. Read-only algebra/literature audit; no numerical computation.

Let A=A_L, C_B=Com(A,B), and C_U=Com(A,U). The inputs already established
in the project are that B=V_(E6+A2), U and A are strongly rational unitary
VOAs, U is conformal in B, A is its own double commutant in both U and B,
and the actual C_B is strongly rational. The latter is the standard
diagonal coset identified in
`hi_cft_20260923_next_structure_residual_identification.md`.

These inputs prove that the conformal net of C_U is completely rational,
and that its inclusion in the net of C_B has finite index. They do not,
by the theorems audited here, prove C2-cofiniteness of the VOA C_U.
The distinction matters when applying a VOA mirror theorem.

Write N_V for the conformal net of a unitary subVOA V of B, and put

    delta = [N_B : N_U],       t = [N_CB : N_CU].

Both numbers are finite and t <= delta. The actual extra K currents give
the stronger equality t=delta, using the known VOA/net identification for
A. In particular,

    C_U = C_B  if and only if  U = B.

The symbol delta below is a net index. It is not silently identified with
the previously defined VOA categorical index s.

## 1. All nets and inclusions here are actual

B is a tensor product of positive-level affine VOAs, so its bounded
localized vertex operators produce the usual loop-group tensor-product
net. Every unitary subVOA used here inherits bounded localized vertex
operators. Since U is regular and conformal in B, [Tener, Corollary
4.24](https://link.springer.com/article/10.1007/s00039-024-00685-8) gives
delta<infinity. Applying the same corollary to A and its regular coset
C_B gives

    r_B = [N_B : N_A tensor N_CB] < infinity.

Tener's construction and the strongly local construction agree on these
subalgebras: they agree on ambient B; each subnet has vacuum space equal
to the Hilbert completion of its subVOA; and the subnet/subVOA
correspondence recovers that subVOA from its vacuum space.
Specifically, [CKLW, Theorems 7.1, 7.4 and Proposition
7.8](https://arxiv.org/html/1503.01260) establish inheritance of strong
locality, recovery of subVOAs, and equality of the two coset constructions.
Thus N_CU is exactly the AL coset subnet in N_U, and N_CB is exactly the
AL coset subnet in N_B. No conjectural replacement of a coset is used.

The ambient N_B is completely rational. Finite-index descent applied to
N_A tensor N_CB shows both factors completely rational. Similarly N_U
is completely rational. The required net results are [Longo, Theorem 24
and Lemma 25](https://arxiv.org/html/math/0102196).

## 2. The expectation restricts to the smaller coset

Here is an elementary argument for the step not supplied by a general
VOA coset theorem. [Longo, Lemma 13](https://arxiv.org/html/math/0102196)
provides coherent vacuum-preserving normal conditional expectations

    E_I : N_B(I) -> N_U(I),

meaning E_K restricted to N_B(I) is E_I whenever I is contained in K.
The finite-index net inclusion is irreducible (Longo, Lemma 14), so these
expectations are minimal and satisfy the Pimsner--Popa bound

    E_I(x) >= delta^(-1) x     for x >= 0.

Take c in N_CB(I). For a sufficiently small interval J, choose a proper
interval K containing I and J. If a is in N_A(J), then a is in N_U(K),
and bimodularity plus coherence give

    [E_I(c),a] = E_K([c,a]) = 0.

Arbitrary intervals J can be covered by small intervals of this kind;
net additivity proves commutation with every N_A(J). Therefore E_I(c)
belongs to N_CU(I). Conversely E_I fixes N_CU(I). Hence its restriction
is a conditional expectation

    E_I restricted to N_CB(I) : N_CB(I) -> N_CU(I).

The same positive-operator inequality holds on this subalgebra, proving
t<=delta. Since the cosets share the stress omega_B-omega_A, this is a
conformal subnet inclusion. Longo's finite-index theorem now gives
complete rationality of N_CU.

Index multiplicativity also gives

    [N_U : N_A tensor N_CU] = r_B t / delta < infinity.

Thus A and C_U form a genuine normal cofinite pair of completely rational
nets. This conclusion is unconditional on properness of U in B and does
not require C2-cofiniteness of C_U.

## 3. Full AL branching and equality of indices

The certified AL type of the two extra K currents E,F is
y_3=(tau,i=6). Their AL energy is 1/5 and H-charges are +/-2;
the other type at AL energy 1/5 has charges +/-4. See
`hi_cft_20260923_next_structure_residual_category.md` for the actual
top-label argument. In Q=Rep(A)=Fib tensor SO3_13,

    y_3 tensor y_3 = (1+tau) tensor (0+2+4+6+8+10+12).

It contains all fourteen simple objects. Therefore any fusion subcategory
of Q containing y_3 is all of Q.

For clarity, the identification Rep_net(A)=Q has a source-based route.
Ambient B satisfies condition B by [Gui, Theorem
3.40](https://binguimath.github.io/Files/2020_Strong-Braiding.pdf).
Theorem3.34 of that paper applies directly to its regular mutual cosets
A,C_B and gives condition B for both. The tensor-product theorem3.37 and
comparison theorem3.39 then give the VOA/net equivalence for A tensor C_B
and for each factor individually, using the known equivalence for B.

For a normal cofinite pair of completely rational nets, the AL labels
occurring in the vacuum branching form a fusion subcategory, with
simple, pairwise distinct mirror coset sectors. This is [Xu, Proposition
3.7](https://arxiv.org/html/math/0505367). Equivalently it follows by
applying [Davydov--Nikshych--Ostrik, Theorem
3.6](https://arxiv.org/html/1109.5558) to the local extension algebra in
Q tensor Rep_net(C_U): mutual commutants make both one-factor algebra
intersections trivial, leaving a graph algebra of a braid-reversed
equivalence between fusion subcategories.

The y_3 witness forces the AL subcategory to be all Q in U and in B.
Writing a=Dim(Q), the graph algebra has dimension
sum_i dim(i)^2=a, so

    [N_U : N_A tensor N_CU] = a
      = [N_B : N_A tensor N_CB].

Substitution into the index identity in Section 2 proves t=delta.
If C_U=C_B, then delta=1, so N_U=N_B and the subnet/subVOA
correspondence gives U=B. The reverse implication is immediate.

## 4. An actual finite category reduction

The mirror copy Q^rev in Rep_net(C_U) is nondegenerate. Its Mueger
centralizer R therefore gives

    Rep_net(C_U) = Q^rev tensor R.

Under this factorization, the AL/coset extension algebra is the canonical
diagonal algebra in Q tensor Q^rev, tensored with 1_R. Its local-module
category is R, whereas the local-module category of this extension is
Rep_net(U). Consequently

    Rep_net(C_U) = Q^rev tensor Rep_net(U),
    Rep_net(C_B) = Q^rev tensor Rep_net(B).

These are braided equivalences. The splitting uses the nondegenerate
case of [DNO, Proposition 4.3](https://arxiv.org/html/1109.5558).
In particular,

    rank Rep_net(C_U) = 14 rank Rep_net(U),
    Dim Rep_net(C_U) = a Dim Rep_net(U).

This proves existence of a finite modular category for the actual C_U
net and reduces its category by a known factor. It does not classify
all finite-index subnets of the known C_B, bound delta, or select the
Haagerup category. Without further structural information the unknown
factor is exactly Rep_net(U), so the splitting by itself adds no numerical
index bound.

## 5. What remains missing on the VOA side

The exact B=U direct sum X decomposition implies, on taking AL-vacuum
multiplicity spaces,

    C_B = C_U direct sum Hom_AL(AL,X).

This is a vector-space and C_U-module decomposition. Simplicity of X as
a U-module does not prove that its AL-vacuum multiplicity space is a
simple C_U-module. The displayed decomposition alone is neither a
Z2-orbifold realization nor a proved finite fusion-category extension
of C_U.

[McRae's finite-index theorem, Theorem
1.2(2)](https://arxiv.org/html/2103.07657) assumes C2-cofiniteness of the
smaller VOA. His [2026 coset rationality
theorem](https://arxiv.org/abs/2108.01898) also requires C2-cofiniteness
of the opposite coset. Neither theorem supplies that hypothesis here.
The [general mirror theorem, Theorem
1.1](https://arxiv.org/html/2107.06577) requires the coset branching modules
to belong to an already constructed HLZ braided tensor category. It
transfers rigidity and simplicity once that category exists; it does
not construct the category from regularity of U and AL alone.

Complete rationality of N_CU likewise must not be relabeled as
C2-cofiniteness of C_U without an applicable additional theorem.
This audit found no such general finite-index descent theorem. An
actual rational conformal frame inside C_U, an explicit finite orbifold
description, or a direct C2 proof would close the VOA gap. After that,
McRae gives strong rationality and the same full mirror argument gives
Rep(C_U)=Q^rev tensor Rep(U) in the VOA setting.

Finally, the Heisenberg/lattice coset theorem can prove regularity of
Com(V_L,U), but C_U requires also commuting with the nonpointed PF3 and
PF13 factors of AL. Thus the [Heisenberg coset
theorem](https://arxiv.org/html/1611.00305) does not by itself reach C_U.

## 6. The categorical index s is not yet identified with delta

For the actual regular conformal inclusion U in B, Tener's theorem proves
finiteness of delta and existence of the net representations associated
with the finitely many U-submodules of B. In the proper case it therefore
gives the actual finite-index net sector pi_X and

    delta = 1 + dim_net(pi_X).

The analogous VOA identity is s=1+qdim_U(X). Equating these dimensions
requires more than the existence and finite index of pi_X. In particular,
the proof of [Gui, Theorem3.39, pp.52--53](https://binguimath.github.io/Files/2020_Strong-Braiding.pdf)
uses his braided C*-tensor embedding to identify the quantum dimension of
the extension object with its net dimension. Its hypotheses include
condition A for the smaller VOA. That condition contains strong unitarity
and analytic assumptions on generating intertwiners; it has not been
established for this U merely from strong rationality and U subset B.

The mutual-coset theorem3.34 cannot supply that hypothesis by taking U as
the subalgebra of B: since U is conformal, its B-coset is trivial and its
B-double-coset is B, so the required double-coset equality would already
assert U=B. Likewise Gui's complete-unitarity extension theorem ascends
from a completely unitary conformal subalgebra; it is not a descent
theorem from B to U.

The creation/annihilation operators inherited from B do supply vacuum
channels for X and prove its finite net index. Tener's Corollary4.17 and
Section5.3 distinguish this partial local fusion information from an
identification of the full VOA fusion product with Connes fusion. This
audit did not find a theorem extracting equality of these two dimensions
from the vacuum channel alone. No equality delta=s is asserted here.

**Later source update.** Henriques--Tener2507.20735v3 does give a reverse
net-to-VOA module construction, including admissible weak modules without
finite-energy multiplicity assumptions. Combined with regularity of U,
it yields a fully faithful linear *-functor from finite net sectors to
ordinary unitary U-modules. The proof and its scope are recorded in
`hi_cft_20260923_next_m3_unitarity_scope.md`. This improves the representation
comparison, but that source does not identify the tensor structures or
categorical dimensions, so it does not yet prove delta=s.

A proved condition A for U would close this comparison immediately:
Gui's Corollary3.23 identifies extension-object dimensions, and
Theorem3.39 transfers essential surjectivity from B, giving

    Rep_net(U) = Rep(U),       delta=s,
    Rep_net(C_U) = Q^rev tensor Rep(U),
    [N_CB:N_CU]=s.

This conditional result does not require C2-cofiniteness of C_U as a VOA.

## 7. What the known c=18/5 net currently constrains

No classification of all completely rational nets at central charge18/5,
or of all finite-index conformal subnets of this particular C_B, was found
in this audit. The established mirror decomposition by itself does not
give such a classification. The index and global-dimension identities are

    Dim Rep_net(C_U) = delta^2 Dim Rep_net(C_B)
                    = delta^2 Dim(Q) * 9,
    Dim Rep_net(U) = 9 delta^2.

These restate the original conformal inclusion's unknown index. The
known Q factor contributes no upper bound on delta, and central charge
modulo8 only reproduces the same Witt-class constraint. Even if delta=s
is subsequently established, these formulas alone do not distinguish the
rank4 near-group alternatives or exclude generalized Haagerup parameters
m>=2.

[Bischoff's generalized-orbifold theorem](https://arxiv.org/abs/1608.00253)
describes finite-index conformal subnets through generalized symmetries;
it does not classify the possible actions on a fixed net. Thus a trivial
ordinary automorphism group would not rule out the required subnet.
Nor does finiteness of intermediate subnets in a fixed finite-index
inclusion bound all unknown subnets lying below C_B: to use that result
one must first provide a common finite-index lower subnet inside C_U.

A concrete improvement would be an actual rational conformal frame
F inside C_U whose inclusion in C_B is already known. Then U properness
would reduce to finitely many intermediate local extension algebras
between F and C_B, with an explicit index bound [C_B:F]. The rational
frame currently known inside C_B has not been shown to lie inside C_U;
using it as a common lower subnet would assume the missing step.
