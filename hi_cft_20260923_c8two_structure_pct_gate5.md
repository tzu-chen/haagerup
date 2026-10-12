# What PCT and current Weyl symmetry can reduce

23 September 2026, c=8-only continuation. Algebra and frozen-source
inspection only; no numerical job. This addresses a proposed identification
of the two weight-two families of current type (1,9).

## The two families cannot be exchanged

Let theta be the established PCT involution and let w be the product of
the two current Weyl transformations. On a highest-weight line, J=w theta
is an antilinear map back to the same current highest weight. The neutral
stress e is fixed by theta and by the current group, so J commutes with
e_1, with complex conjugation of its eigenvalue.

The exact field source gives the two (1,9) families the distinct real
e_1 eigenvalues

    operator 1: 200/1271,
    operator 2: 1512/1271.

Therefore J cannot exchange them. Each belongs to its own one-dimensional
highest-weight eigenspace. The other charged families are similarly
distinguished by their current types and real e_1 eigenvalues. The two
neutral stresses themselves are PCT-fixed current singlets.

Thus this PCT/current-Weyl operation does not remove the three grade-five
channels of either (1,9) family. It also preserves each output highest
weight, so it does not exchange the channels with right highest weights
m+2, m, and m-2. A reality relation within a single channel is not another
channel's containment certificate.

## PCT stability of the selected weight-four space has a valid proof

Before the weight-four gate is completed, one must not assume PCT
stability of N4+P4 merely from the three modular extra directions.
The chosen actual P4 copy could a priori have a PCT image involving
another ambient copy modulo N4.

After the exact weight-four gate passes, however, PCT stability follows
without using properness or the grade-five gate. The existing lower
identities and provenance give

    S3=N3+S2_0 S2,
    P4 subset N4+S2_0 S3.

The completed gate gives the reverse inclusion needed for

    W4=N4+P4=N4+S2_0 S3.

K, S2 and N3 are PCT-stable; the first equality for S3 then proves its
PCT stability. The displayed expression for W4 proves its PCT stability,
and consequently

    N5=K_(-1)W4+T W4+S2_(-1)S3

is PCT-stable as well. This is a noncircular consequence of Gate4, not an
assumption that U has already been strongly generated.

## A genuine alternative grade-five reduction

For each highest-left field a, a raw containment a_0 P4_minus in N5
would imply the other two raw P4 containments by raising covariance:
E a=0 and E P4_minus=2 P4_zero, E P4_zero=2 P4_plus.
Thus one raw lowest-right input per family suffices. This is the same
raising-kernel argument used in the new weight-four saturation certificate.

The raw lowest-right target generally contains all of the tensor-product
channels and lives in a larger Cartan block. Checking only its projection
onto the lowest output channel discards the others and does not suffice
unless those other channels have already passed. The existing projected
strategy therefore remains useful despite requiring more scalar target
certificates: its exact linear systems can be much smaller.
