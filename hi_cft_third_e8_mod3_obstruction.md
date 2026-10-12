# A mod-three obstruction for every proper abelian E8 host

Under the hypotheses of the
[proper host0 capacity theorem](hi_cft_third_e8_host0_proper_constraints.md),
the complementary binary lattice determinant satisfies

\[
 \boxed{q\equiv2\pmod3.}
\tag{1}
\]

The [final consolidated theorem](hi_cft_third_e8_proper_abelian_exclusion.md)
also observes that every L_B vector has norm divisible by six and
extends character parity to even q. Together these refinements exclude
every proper abelian host under the stated framework. The proof below
records the mod-three component separately.

This statement has no oddness or lattice-minimum assumption. Combining it
with the [odd-determinant theorem](hi_cft_third_e8_odd_determinant_constraint.md)
excludes **every proper abelian host with odd q and minimum of L_B at
least six**, not just the explicit determinant575 family.

The restricted action being proper and the unitary finite-index framework
remain essential premises. Even q, shorter commutant vectors, and
nonproper restrictions are not eliminated by the combined statement.

## 1. A common Cartan and a norm-six representative

Write E=V_E8 and B=E^alpha=V_E6 tensor V_A2. Choose a Cartan of B
containing the six-dimensional fixed current torus. Since B has full
rank eight, this is also a Cartan of E.

There is a direct representative of alpha in this Cartan. If u,v are
simple roots of the A2 factor, with u²=v²=2 and (u,v)=-1, put

\[
 h=u+2v,\qquad h^2=6.
\]

It pairs with u,v as0,3, and is orthogonal to the E6 root factor.
It pairs nontrivially modulo3 with the A2 fundamental glue weight in
the index-three E8 extension of E6 plus A2. Hence
exp(2 pi i h0/3), or its inverse, fixes B and has the required nontrivial
eigenvalues on the two E8/B glue modules. We may use this h to represent
alpha.

The fixed E6/A2 framework is the one in
[the primary Haagerup construction, Section4.3](https://arxiv.org/html/2606.05279#S4.SS3).
No assumption is made that this norm-six h already lies in the
complementary binary plane.

## 2. Primitive projection moves the cocharacter into the binary lattice

Capacity saturation gives V_K contained in W contained in B, where
K=E8 intersect the six-current plane is primitive and rootless. Let
L=K-perp intersect E8, with det(L)=det(K)=q.

Since alpha fixes V_K pointwise,

\[
 (h,K)\subset3\mathbb Z.
\]

Thus the orthogonal projection P_K(h)/3 belongs to K*.
The projection map

\[
 E8\longrightarrow K^*
\tag{2}
\]

is surjective. To see this directly, primitivity makes E8/K a free
abelian group, so every integer-valued homomorphism on K extends to
E8. Unimodularity represents that extended homomorphism by pairing
with an element of E8. Its orthogonal projection is the specified
dual vector.

Choose x in E8 whose projection is P_K(h)/3, and set

\[
 h'=h-3x.
\]

Then h' belongs to L. It represents exactly the same inner automorphism,
because (x,E8) is integral. Also

\[
 (h')^2=h^2-6(h,x)+9x^2\equiv0\pmod3.
\tag{3}
\]

Unlike the earlier short-representative family argument, this step
allows h' to have arbitrary norm and does not assume that h' is a
primitive integer vector.

## 3. The binary quadratic form over F3 is hyperbolic

Capacity also gives [L:L_B]=3. Thus the character

\[
 y\longmapsto(h',y)\pmod3
\]

on L is nonzero. The vector h' modulo3 is therefore a nonradical
isotropic vector for the symmetric bilinear form on L/3L: isotropy
is (3), and nonradicality is the nontrivial character.

A symmetric form of rank at most one in dimension two over F3 has
only radical isotropic vectors. Indeed a nonzero rank-one form is
congruent to diag(a,0), and a z²=0 forces z=0; rank zero is immediate.
Our form must therefore be nondegenerate.

Choose a basis whose first vector is h' modulo3, and write b for its
nonzero pairing with the second vector. The Gram matrix is

\[
 \begin{pmatrix}0&b\\ b&c\end{pmatrix},
 \qquad b\ne0.
\]

Its determinant is -b²=-1=2 in F3. Changes of basis multiply the
determinant by a nonzero square, which is1 over F3. Thus the actual
integer determinant q is2 modulo3, proving (1).

## 4. Combination with the low-weight theorem

For odd q and min(L_B) at least six, the parity, minimal-shell,
oscillator and exact Miura-character argument proves q=3s².
That conflicts with (1). Therefore no proper abelian-six-current
E8 fixed algebra satisfies both of those additional conditions.

This conclusion includes all primitive planes containing a norm-six
representative, but does not rely on such containment. It is strictly
stronger than that earlier family-specific corollary.

The primitive projection, binary F3 argument and their compatibility
with alpha were derived by the root agent and independently audited
by both the CFT-constraints and uniform agents. No numerical job was
needed. The exact coordinate and character certificates for the
determinant575 example remain correct; the stronger obstruction
excludes the proposed proper action on that otherwise valid lattice
embedding.
