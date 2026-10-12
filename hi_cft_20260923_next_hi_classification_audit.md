# Source audit: from the HI(Z3) fusion ring to the Haagerup center

23 September 2026. No numerical job or classification replay was run.

Conclusion: accepting Vercleyen's reported exhaustive computer-assisted
classification, a pseudounitary fusion category with the HI(Z3) ring is
tensor equivalent to H2 or H3. Hence its center is the Haagerup center.
There is no C* hypothesis missing in this route. The independent algebra
below explains why the nonpositive classes cannot intervene.

## Scope of the exhaustive result

[Vercleyen's thesis, Section 4.4 and Table 9.1]
(https://mural.maynoothuniversity.ie/id/eprint/18958/1/phd.pdf) explicitly
claims exhaustion of pivotal multiplicity-free categories through rank
seven. HI(Z3) is directly solved; the two cases treated using outside
classifications are PSU(2)12 and PSU(2)13. Table 9.1, printed page 171
(PDF index 184), lists four HI(Z3) associator classes, each with one
pivotal structure. Section 4.4.1 describes retained notebooks and logs,
available upon request; its example figures specifically concern HI(Z3).
Section 4.1.8 reports agreement between symbolic equivalence removal and
a 1000-digit numerical cross-check.

Thus the source asserts an exhaustive algebraic classification, rather
than only constructing four examples. This audit checked that assertion
and its scope, but did not obtain or replay the underlying elimination
logs. The exhaustive upper bound remains an explicitly cited external
computer-assisted result. The current [AnyonWiki table]
(https://anyonwiki.github.io/pages/Lists/losmffc.html) also lists exactly
four records FC^(6,1,2)_(8,f,0,1), f=1,2,3,4, with the first two unitary.

## An independent count-and-positivity argument

The ring in question has simples 1,a,a^2,rho,a rho,a^2 rho and

    a^3=1,  rho a=a^2 rho,
    rho^2=1+rho+a rho+a^2 rho.

It is multiplicity-free, has rank six and exactly two non-self-dual
simples, matching the HI(Z3) entry.

There is at most one pivotal structure on any categorification of this
ring. Indeed, the ratio of two pivotal structures is a monoidal natural
automorphism of the identity. Write its nonzero scalar on a simple Z
as t_Z. Each summand Z of X tensor Y has t_Z=t_X t_Y. Since both 1 and
rho occur in rho^2, t_rho^2=1=t_rho; hence t_rho=1. The other two
noninvertibles also occur there, so their scalars are one. Finally
a tensor rho=a rho and a^2 tensor rho=a^2 rho give t_a=t_(a^2)=1.
Thus the automorphism is trivial. Equivalently the universal grading
is trivial: the adjoint subcategory contains all three noninvertibles
and consequently all the invertibles.

[Evans--Gannon, Theorems 2 and 3(ii), Section 5]
(https://arxiv.org/html/1506.03546#S7.SS1) construct four inequivalent
spherical categories of this ring. Two have dimension
d_+=(3+sqrt(13))/2 and two have d_-=(3-sqrt(13))/2 on each
noninvertible. Their construction alone is not used as an exhaustion
theorem for arbitrary fusion categories. It supplies four inequivalent
examples which attain Vercleyen's upper bound. The two positive examples
are the Haagerup and Grossman--Snyder categories. The spherical dimension
calculation is explicit in Section 5, immediately before the tensor-
equivalence proof.

The negative examples cannot admit some other positive pivotal
structure: pivotal uniqueness just proved rules this out. In particular
their categorical dimension is 3(1+d_-^2), different from their
Frobenius--Perron dimension 3(1+d_+^2). They are not pseudounitary.
Therefore the only pseudounitary tensor classes are the two positive
ones. This conclusion does not use the invalid general implication
that a nonunitary category must fail to be pseudounitary.

## Morita and ribbon consequences

[Grossman--Snyder, Theorem 1.4]
(https://arxiv.org/html/1102.2631#S1) proves that H2 and H3 are distinct
rank-six categories with this fusion ring and belong to the same Morita
class as the Haagerup even part H1. Their centers are therefore braided
equivalent. Their positive spherical structures induce positive
spherical structures on the centers; uniqueness of the positive
spherical structure upgrades the braided equivalence to the required
ribbon equivalence.

For record identification, the maintained [TensorCategories.jl
documentation](https://tensorcategories.github.io/TensorCategories.jl/stable/F-symbols/Haagerup/)
labels f=1 as H3 and f=2 as H2. The unordered identification suffices
for the argument above and avoids requiring an entrywise associator
gauge comparison with the database records.

Applied to the present construction, the preceding independent ring
and indicator arguments reduce a proper U to a pseudounitary boundary
category F with this HI(Z3) ring. The classification then gives

    Rep(U) = Z(F) equivalent as a ribbon category to Z(H2)=Z(H3).

This is a category-equivalence deduction from cited classification,
not merely an equality of fusion rings or modular data. Its dependence
on the external exhaustive classification should remain visible in a
final proof. It neither proves U is proper in B nor supplies an explicit
tensor functor or independently verified classification certificate.
