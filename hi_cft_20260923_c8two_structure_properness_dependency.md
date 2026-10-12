# Final audit of the finite strong-generation implication

This is the structure agent's independent readback of the finite theorem.
The closed `hi_cft_20260923_c8two_gate4_verified.json` and
`hi_cft_20260923_c8two_gate5_verified.json` now report successful terminal
proofs of every required Gate 4 and Gate 5 family. Their underlying singlet
premise, twelve exact projected identities and charged-span replay also
passed. These statuses were independently read back at approximately
13:45 UTC on 23 September 2026. Thus the exact premises below are discharged,
and the implication proves `U1=K` and properness. No character coefficient,
assumed Haagerup category, or assumed upper dimension of U3 or U4 is used.

## Actual input spaces and required certificates

1. **Unconditional vectors and generation.** The exact construction gives
   the six-dimensional current space K and the actual 120-dimensional S2
   inside U. It includes K's normal descendants, the eight charged current
   modules, both primitive neutral fields, the original u, and omega_B.
   Thus a vertex subalgebra containing K and S2 contains the original weak
   generators of U. Every subsequently chosen field is an actual U-vector.

2. **Exact S3 and recursive provenance.** The frozen characteristic-zero
   checkpoint first constructs N3=K_-1 S2+T S2, of dimension 634, and then
   adds only S2_0 S2 vectors and current zero-mode descendants. The resulting
   S3 has exact dimension 956 and is current-stable. Consequently
   `S3 subset S2_0 S2+N3` is a statement about actual vectors, not a proposed
   character. The 322 quotient lifts need not be minimal generators.

3. **The 3,970 exact lower identities.** The complete lower-closure artifact
   provides quasiprimary primitive fields, all ten highest-field modes 0
   and 1 against S2, current modes 0 and 1 against S2, and L(1)S2 in K.
   Current covariance and the affine normal left fields extend these checks
   to all S2. For a quasiprimary primitive a,
   `a_2 b=L(1)(a_1 b)-a_1 L(1)b` belongs to K; a_3 b is scalar by ambient
   grading. Thus all S2-by-S2 singular products are controlled.

4. **Actual P4 and its direct controls.** The three source-bound projected
   weight-four fields belong to S2_0 S3+N4 and form the exact current triplet
   of highest weight (0,2). Their 18 current-zero identities and six direct
   L(1)/L(2) memberships passed. No quotient-dimension assertion about N4 is
   needed. Here N4 denotes the full differential normal span, and W4=N4+P4.

5. **Gate 4.** The final raising/singlet certificate must prove
   `S2_0 S3 subset W4`. Its exact seed relations, exact singlet premise and
   exact projected residuals establish this by the audited raising-kernel
   argument. The missing neutral family follows from total stress minus
   affine Sugawara stresses. This is an all-input containment in the stated
   finite spaces, not a modular rank estimate for an unknown space.

6. **Gate 5.** The source-bound two bottom witnesses and eight normal
   bracket identities, together with the charged-pair spanning certificate,
   establish `S2_0 P4 subset N5` by the audited Jacobi proof. Here
   `N5=K_-1 W4+T W4+S2_-1 S3` is the full normal space. The charged-pair
   positive rank argument is valid in the already exact 322-dimensional
   S3/N3. It is not a characteristic-zero upper bound extrapolated from a
   prime calculation.

## Order of the lower-mode deductions

The order matters and is noncircular.

The S3 provenance and the lower identities first give K_n S3, L(1)S3
and L(2)S3 in the expected lower spaces. They also give L(1)N4 in S3
and L(2)N4 in S2. The direct P4 controls then yield the corresponding
statements for W4, before Gate 4 is invoked.

Gate 4 and these Virasoro inclusions give every positive S2 mode on P3.
The formulas for a primitive quasiprimary a are

    2 a_1 p = L(1)(a_0 p) - a_0 L(1)p,
      a_2 p = L(1)(a_1 p) - a_1 L(1)p,
    2 a_3 p = L(2)(a_1 p) - a_1 L(2)p.

The remaining mode is scalar. Affine normal left fields follow by the
current iterate formulas. The recursive P4 provenance now gives K_1 P4
in S3, since

    k_1(a_0 p)=(k_0 a)_1 p+(k_1 a)_0 p+a_0(k_1 p).

The same statement extends over every current-zero projection used to
construct P4. Higher current modes follow from L(1), so all current modes
on the enlarged generator list are controlled before Gate 5.

These facts give L(1)N5 in W4 and L(2)N5 in S3. Gate 5 then gives every
positive S2 mode on P4 by the same Virasoro commutators. In particular
the thirty formerly prime-only A_1 P4 tests are derived exactly at this
stage; they are not an additional unproved gate. The 90 exact higher-mode
checks are useful independent controls but are not needed to fill a gap.

## Why all higher-left products follow

Take the full differential normal span of K, S2, S3 and P4, initially with
all parenthesizations. The zero mode of any a in S2 preserves that span
because it is a derivation, commutes with translation, and its value on
every generator is now in the span.

Induct on `(total weight of a generator pair, left weight)`. A left
generator of weight at least three is a sum of terms a_0 b with lower
left weight b, plus normal expressions in lower generators. The identity

    (a_0 b)_n t=a_0(b_n t)-b_n(a_0 t)

reduces the first term to lower total weight. In the second, a_0 t is a
known normal expression. A derivative or a product with at least two
positive-weight factors reduces the total weight in the Wick induction.
Only an undifferentiated single generator can retain the original total
weight, and then its left partner b has smaller weight. Thus the induction
is strict and includes all P3/P4 pairs without presuming their closure.
The normal remainders are controlled by the same filtered Wick argument.
The full normal span is consequently a vertex subalgebra.

## Properness follows without the predicted character

The normal span lies inside U because every generator is an actual U-vector.
Conversely it contains K, u and omega_B and is a vertex subalgebra, so it
contains U. They are equal. Every generator has positive integer weight,
and the only weight-one generators are the six currents. Derivatives and
normal products cannot create another weight-one vector. Hence

    U1=K,   dim U1=6.

The ambient B=V_(E6+A2) has weight-one dimension 78+8=86, so U is proper.
Only after this deduction may the separate modular-character uniqueness
proof be used to identify the 6,010-dimensional weight-four space and the
full Haagerup character vector. No such coefficient was a premise here.
