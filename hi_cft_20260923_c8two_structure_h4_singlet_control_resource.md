# Exact control for reducing the final H4 block to singlets

This new consumer reads the closed original H4 seed files, the closed
118-addition directory, and the authenticated 644 exact raising-coordinate
records in the 322-dimensional S3/N3. It regenerates no lattice modes and
does not invoke a native dense solver.

For each affected highest field a, take the known exact kernel of
f_a([p])=[a_0p] modulo the full current-stable W4. The consumer closes
the authenticated known kernel vectors under both raising matrices.
Every insertion records its raw vector, prior elimination coefficients,
normalization and exact coordinates. It then reduces E_L p and E_R p
for every unfinished output-weight-zero input, with full exact residuals.
If those residuals vanish, its target class is killed by both raisings and
has Cartan weight (0,0), hence is a K singlet in the finite-dimensional
ambient quotient. This licenses singlet projection of the remaining
targets; it does not prove their singlet component vanishes.

This control does not assume Gate 4. Its quotient map is already defined
because the lower checks imply S2_0 N3 is contained in N4, by the zero-mode
derivation rule. The full N4 is current-stable from the previously exact
S2/S3 current controls, and P4 is current-stable by its exact triplet
certificate. Thus W4 is current-stable before the outstanding tests pass.

There are at most nine independent 322-dimensional closures, processed
serially, with at most 644 generated images per closure. All vectors stay
inside the original small Cartan blocks. Coefficients are exact GMP
biquadratic fields and capped at 4,096 bits. Inputs contain at most
644 raising-coordinate vectors and 2,275 seed references. The serialized
proof is capped at 32 MiB. Expected memory is below 0.3 GiB, with an
explicit 768 MiB RSS boundary and mandatory address cap at most 2 GiB.

Root alone may run the producer through the safe launcher, with the
permanent single-job, two-CPU/thread and 32 GiB host-reserve restrictions.
A first run may use 180 seconds (external 200-second timeout). All source
databases are read-only and must be closed; all outputs are fresh.
No computation was launched by the implementing agent.
