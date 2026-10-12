# Correlator derivation and audit notes

The implementation in `correlators.py` is a bounded exact-arithmetic export,
not a new lattice mode job. Its source inputs and the script itself are
hashed in the output. Root runs it serially through the permanent resource
guard with a 1 GiB address-space limit. Expected RSS is below 80 MiB; the
script additionally refuses 192 MiB RSS and imposes a 120-second timeout.
The authoring agent did not execute the exporter.

## Three-exponential generator

The transported Hermitian norm is essential. The exponential norms are
4, 40, 40, while the coefficient absolute squares are 1, 1/10, 1/10.
The three contributions to the unnormalized field norm are consequently
all 4. For each of the six charge orderings, enumerating the 81 choices
gives 15 neutral terms; each has coefficient 1/9 after normalization and
cocycle/PCT cancellation. The program retains every choice, including
the nonneutral terms, to make this small calculation inspectable.

The neutral four-point function is

`(3-4x+4x²)/(3x⁴(1-x)⁴)`.

The equal-charge function is

`x²(4-4x+3x²)/(3(1-x)⁴)`.

Polynomial crossing, all charge-conjugate orderings, and the leading
weight-six primary vector are checked. The global weight-two coefficient
14/3 consists of the total stress contribution 1 and the full Virasoro
primary contribution 11/3. This provides an independent sum rule for the
113-dimensional primary coupling tensor: the normalized lowest component
`v7_1_13` equals the adjoint of the normalized highest field `v7_0_0`
up to a phase, because its Cartan weight is unique in that primary space.
Summing their squared coefficients over every primary target must give
11/3. It does not require a separate PCT reconstruction calculation.

## Spin-three fields

Write N=c/3, b=a_(1)a, A=31-16 lambda(c+2), B=N A. The singular OPE
has coefficients N, 2T, dT, b, and (db)/2-(d³T)/12. Contracting against
the two outer a fields gives principal-part coefficients

`N², 2c, 2c, B, 2B-2c`

at pole orders 6, 4, 3, 2, 1. Equal-field crossing fixes the principal
part at 1, and the identity channel fixes the constant N² at infinity.
This proves the full meromorphic four-point function without a series
guess or new high-weight mode calculation.

The intrinsic Virasoro quasiprimary
Lambda=:TT:-(3/10)d²T has norm c(5c+22)/10. The independent weight-four
primary is b-32 Lambda/(5c+22)-(3/10)d²T. The extra unit-normalized
coupling square is zero for Potts and 60552/2365 for PF13. These are
intrinsic central charges 4/5 and 8/5, not the ambient central charge 8.

The finite-audit agent independently reviewed the pole residues, the
Lambda subtraction, and the distinction between global and Virasoro
blocks and found no correction.

## Selected nonvacuum blocks

The nine A2-lattice blocks have exponents -2/3 and -<beta_i,beta_j>.
Their branch is specified first on 0<x<1. The first relative-weight-one
coefficient splits into the U Cartan projection q_i q_j/78 and its X
complement, whose Gram eigenvalues are 0, 1, 35/39. For the extremal
triplet component the two diagonal contributions are 2/39 and 8/13.
Only three-point coefficient magnitudes are exported for the six
charge-neutral triples; their phases depend on intertwiner bases.

These restricted lattice intertwiners give genuine U chiral blocks.
They are not a complete channel basis and do not determine the lightest
scalar's diagonal-U bulk four-point function. No bulk sewing constants
are inferred by squaring one block.

## Verification boundary

All crossing identities are full rational-function identities. Global
block reconstruction and coefficient positivity are checked only through
the selected finite cutoff (default 32). Their finite checks are not a
proof of all-order positivity, which instead follows from the positive
VOA construction. The lightest-module Gram test is exact. The script
checks the saved u field and spin-three invariants, but does not replay
the authenticated lattice self-OPE source jobs. The frozen source
reports and the manuscript's explicit construction inputs remain part
of the provenance.
