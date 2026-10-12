# Gamma0: a sharper finite-only rank-three bound

15 September2026. This is a short algebraic consequence of the three
identities in [the universal current-trace note](hi_cft_third_flavoured_universal_obstruction.md).
No numerical job or change to its frozen producer is required.

Suppose the gamma0 weight-one algebra is `A1_k + U1^3`, with the
strongly regular unitary VOA and actual Haagerup modular-representation
premises of that note. The radical charge-support argument already
forces the `c1` and `d4` ground representations to be A1-neutral:
their dimensions3 and5 must realize respectively one and two independent
nonzero radical charge pairs. A nontrivial SU2 summand would consume
too much dimension to realize these ranks.

Use ordinary SU2 indices, with doublet index1 and adjoint index4.
For gamma0, `d6` has a14-dimensional ground at conformal weight8/13:
its character starts at exponent `8/13-8/24=11/39`. Thus the `t_6`
in the third identity is a ground-representation index, not a trace
with an unaccounted contribution from an earlier grade.
The positive and third modular identities are

    4 + 9 t_c + t_1 + 3 t_4 = 4k,
    t_6 + t_1 - 2 t_4 = 2k.

Setting `t_c=t_4=0` gives

    t_1 = 4(k-1),
    t_6 = 4-2k.

The finite representation on the `d6` ground has nonnegative Dynkin
index. Thus `k<=2`; positive integrality leaves only `{1,2}`. This
uses no nonvacuum module-energy inequality, no Frobenius--Schur sign,
and no new coefficient of the character vector.

As a direct check in the original three-dimensional modular-form
basis, impose `Q_c1=Q_d4=0` and normalized vacuum trace `Q_vac=4/k`.
The resulting normalized `d6` trace is exactly `4/k-2`, giving the
same bound.

This branch consequently has full-current coset central charge

    c >= 8-3-3(2)/(2+2) = 7/2.

The other allowed six-dimensional current type is `A1_k1+A1_k2`.
The already proved finite-only level-sum bound `k1+k2<=40` gives
its coset lower bound `28/11`. Therefore the universal finite-only
current-generated coset bound strengthens from `40/17` to **`28/11`**.
The weaker bound remains valid in any previously frozen certificate.

The same third identity supplies a further inexpensive necessary test
for each factor in the two-A1 branch:

    t_6 = 2k-t_1+2t_4 = 4-2k+9t_c+5t_4 >= 0.

It can be applied to each already enumerated joint ground witness
without decomposing the14-dimensional `d6` representation. A stronger
bound from this witness filter would require its separately recorded
execution; none is asserted here.

These are constraints on the stated chiral VOA/current-coset
realization. They do not determine the physical chain central charge,
and do not constrain an arbitrary non-current denominator.

ROOT independently verified the short positivity argument. The new
standalone source `hi_cft_third_gamma0_rank3_check.py` hash-binds the
executed universal and original trace records, verifies both producer
versions, reconstructs the gamma0 particular coefficients, and solves
the complete three-dimensional neutral-ground system. Its evaluations
at the formal inverse-level values0,1,2 certify the affine formula
`Q_d6=4/k-2`; uniqueness of the linear system makes this a symbolic
affine identity, not interpolation from physical samples.

No tensor is loaded. At most five128KiB input/source snapshots,
two small decoded JSON records and3-by-3 rational elimination are
retained; a64MiB process estimate fits the128MiB coordinated slot.
The source has a10second alarm and refuses existing outputs. Only
AST parsing was performed by the author. ROOT's command is

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_gamma0_rank3_refinement.md --audit-json hi_cft_third_gamma0_rank3_guard.json -- python hi_cft_third_gamma0_rank3_check.py --output hi_cft_third_gamma0_rank3_results.json

The new source is pending independent source review and ROOT execution.
