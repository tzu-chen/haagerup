# Property-based catalog refinement from flavoured characters

15 September2026. New source prepared; ROOT owns every guarded run.
The older10/11/12 outputs, their archived producers, and the13-host
draft remain untouched.

`hi_cft_third_e8_flavoured_grid.py` reads the original necessary
denominator catalog, the original passing full-current rows, and
the executed universal flavoured-character certificate. It checks
the latter's producer hash and records hashes for every input and
its own source.

The default filter removes a full-current host for explicit
properties, recording every applicable reason:

* Weight-one dimension19 is impossible by the gamma1 modular/Lie
  exhaustion, independently of its residual coset description.
* In gamma0 the positive trace matrices force radical rank<=3.
* An individual A1 level exceeds39 only in contradiction with
  the universal finite-dimensional index bound.
* A1_k plus three radical currents requires
  k in{1,2,3,6,15}, by the stronger radical-support and seven-dimensional
  finite-representation argument.
* Two A1 factors require their level sum<=40.

The twelve previously audited host exclusions are also retained
and recorded. Every denominator row is kept precisely when it
still has a full-current host witness. The script never treats
an individual denominator's level as the level of its host.

The default exact lower bound for a current-generated residual is
40/17. The script checks this both for retained full-current hosts
and retained denominator witnesses. The saved denominator catalog
has a bounded central-charge range; an empty output means that
range is exhausted, not that all current denominators are excluded
at every central charge. Retained full-current rows, which have
no such range restriction, are reported separately.

An explicit optional flag `--with-unitary-module-energy` further
reduces the single-A1/rank-three levels to1 and3. This requires
nonnegative module commutant energy and is not folded into the
default finite-representation result. Its corresponding universal
current-coset lower bound is28/11, from the two-A1 branch.

The analytic/source proof is
[the universal flavoured obstruction](hi_cft_third_flavoured_universal_obstruction.md),
with [an independent global audit](hi_cft_third_gamma1_independent_audit.md).
The original chain-to-current-coset map remains unproved.

## Allocation and commands

The original JSON inputs total less than0.75MiB. The helper retains
those snapshots, their decoded objects, and a filtered output;
there is no Lie enumeration, numerical linear algebra or tensor
allocation. Each input is capped at2MiB. A conservative64MiB process
estimate fits the128MiB guarded slot. The30second alarm, immutable
snapshots and refusal to overwrite outputs make each run reviewable.

Default, after the universal certificate is executed:

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_e8_flavoured_grid.md --audit-json hi_cft_third_e8_flavoured_grid_guard.json -- python hi_cft_third_e8_flavoured_grid.py --output hi_cft_third_e8_flavoured_grid_results.json

Separately, only with the additional module-energy premise:

    python hi_cft_third_window_run.py --limit-mib 128 --estimated-peak-mib 64 --estimate-note hi_cft_third_e8_flavoured_grid.md --audit-json hi_cft_third_e8_flavoured_grid_energy_guard.json -- python hi_cft_third_e8_flavoured_grid.py --with-unitary-module-energy --output hi_cft_third_e8_flavoured_grid_energy_results.json
