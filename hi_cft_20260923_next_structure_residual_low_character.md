# Conditional first residual character coefficients

The root-run certificate
`hi_cft_20260923_next_structure_residual_grade3.json` computes the exact
kernel of omega_AL,1 on the authenticated 58-dimensional Cartan-zero
block of the 956-dimensional S3. The kernel has dimension two and is
exactly the span of L(-1)q and L(-1)r. Its weight-three Virasoro-primary
subspace is zero. All current nonnegative modes and the redundant
positive Potts/PF13 stress modes annihilate the saved basis exactly.
The computation used Q(sqrt(13),sqrt(-3)),105.11 seconds, and about
0.085 GiB peak RSS under the root-controlled safe launcher.

Independently, the root's X3 certificate proves U3=S3 if U is proper.
The previous current-kernel certificate proves C_U2=span(q,r) under
the same hypothesis. C_U1 is zero because the actual rational core
contains the full left sl2 and the right Cartan. Thus in the proper case

    ch C_U = q^(-3/20) (1 + 2q^2 + 2q^3 + O(q^4)).

The q^3 coefficient gives no independent strong generator: both states
are translations of the two weight-two states. This supports starting
a search for any additional residual strong generator at weight four.
It does not prove generation by the two weight-two fields, finite
closure of their OPEs, properness, or the entire residual character.

The producer is `hi_cft_20260923_next_structure_residual_grade3.py`;
its certificate records all source hashes, exact kernel vectors, and
the translation basis. No new computation was launched for this note.
