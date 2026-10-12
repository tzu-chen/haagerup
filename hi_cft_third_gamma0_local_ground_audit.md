# Locality of the retained diagonal affine extension

The separate `hi_cft_third_gamma0_local_ground_check.py` tests necessary
ground-representation support for the two quartic survivors `(1,39)` and
`(3,13)`. It leaves all executed producers unchanged. The additional
structural premise is the actual inclusion

\[
H^+=(A1_k\otimes A1_l)\oplus(J_k\otimes J_l)\subset W.
\]

The [Cartan retention proof](hi_cft_third_cartan_c2_retention.md), under
the stated actual finite-index inclusion in `E6_1 times A2_1`, supplies
this premise. It first forces the full rank-two lattice inside W.
The half-sum lattice vector has Cartan charges `(k,l)` and weight
`(k+l)/4`. Its Heisenberg energy already equals its full energy.
Every positive affine root mode would lower the full energy by at least
one while shifting one charge by two. Even the potentially smallest
new Heisenberg energy, from the lowering mode at index one, exceeds
the available energy by `1/k` or `1/l`. Thus all positive affine modes
annihilate it, as do the horizontal raising operators. It is an affine
highest vector of labels `(k,l)` with complementary weight zero.
This makes the simple-current retention explicit using only vacuum
unitarity, without positivity assumptions on nonvacuum W modules.

An ordinary W module restricts locally to H+. The monodromy is
`(-1)^(ell_left+ell_right)`, so every finite affine ground irrep `(n,m)`
satisfies **n+m even**. An odd type is forbidden individually; pairing
two copies does not restore locality. This is stronger than the earlier
symmetric-form condition on quaternionic irreps.

## Exhaustive finite support test

The reader binds the immutable quartic output and every recorded
producer source. For each of all eleven nonvacuum module grounds it
requires the dimension, both quadratic indices, mixed quartic index,
and both pure fourth moments. The source solves the left-factor
moments first. If `a_n` is the right multiplicity-space dimension:

* at level one, `a_2=T_left`, `a_1=d-2T_left`, and
  `2S_left=T_left`;
* at level three,
  `a_3+6a_4=(2S_left-T_left)/12`,
  `a_2=T_left-4a_3-10a_4`,
  `a_1=d-2a_2-3a_3-4a_4`.

Every nonnegative integral solution is retained. Locality requires
even `a_n` for even n. Each block then enumerates all right partitions
using only `m<=l+1` and `n+m` even. The n=1 block is hashed by its
right quadratic and fourth moments; these are its only remaining
contributions, so one witness per hash key is sufficient. All other
blocks are combined, and every accepted full representation is
substituted independently into all six target moments.

The default test uses no affine ground-energy bound. Optional
`--affine-energy` explicitly adds unitary nonvacuum modules, or
nonnegative affine-commutant energy, as a separate premise. Neither
mode treats a selected old d5/d6 witness as an exhaustive decomposition.
Identical a/c0 target records are reused with the module name preserved.

Each ground stops at its first support witness. A refusal exhausts
all allowed left splits and right partitions. Resource-cap exhaustion
raises an error and certifies no exclusion. Passing all grounds is
necessary support only, not VOA existence or OPE closure.

## Allocation and controls

The implementation is pure stdlib and opens no tensor checkpoints.
One ground is live at a time. Caps are one million visited DFS nodes,
ten thousand stored partitions per block, and one million combined
nontrivial block tuples. Visited nodes are not retained. At most four
blocks and their short representation partitions coexist, with one
small witness retained for each completed ground. Input is limited to
2 MiB and each source to128 KiB. The reviewed execution profile is
128 MiB address space and a sixty-second alarm; exceeding either
limit cannot produce an exclusion.

Controls include the known local d5 representation `(1,5)+(2,4)` at
both pairs and refusal of the nonlocal two-dimensional `(2,1)` ground.
Constraints independently read the complete source and passed the
left-moment reduction, partition support, hash reduction and scope.
ROOT executed the default certificate successfully at22:14:59UTC:
all eleven nonvacuum grounds have local support at both pairs, in
0.0216seconds. The output is
`hi_cft_third_gamma0_local_ground_results.json`. This adds no exclusion.
The author has not executed a numerical job.

```sh
python hi_cft_safe_run.py --limit-mib 128 -- python hi_cft_third_gamma0_local_ground_check.py --input hi_cft_third_gamma0_quartic_results.json --output hi_cft_third_gamma0_local_ground_results.json
```

## Relation to the weight-two result

The previously executed factored grade-two certificate forces exactly
two full-current commutant states at weight two for each host. All
irreps in its unique decomposition already have n+m even. Therefore
locality alone does not remove either weight-two representation or
select its two-dimensional singlet plane inside the ambient commutant.
The host125 real Griess-algebra classification leaves seven possible
unital planes. Distinguishing these requires OPE closure or an additional
representation-level action on the relevant multiplicity spaces;
finite ground moments do not supply those matrix elements.
