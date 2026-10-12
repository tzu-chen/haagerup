# Defect and boundary dataset

`defects.py` derives these tables from the printed positive Haagerup S matrix
and the gamma=0 character tops. It does not import the lattice construction
engine or infer integers by rounding. Root's guarded run passed every exact
check; the recorded runtime is in `defect_data.json`.

All labels use the fixed order

    0,b,a,c0,c1,c2,d1,d2,d3,d4,d5,d6

which corresponds to AHKZ

    1,pi1,pi2,sigma1,sigma2,sigma3,mu5,mu2,mu1,mu3,mu6,mu4.

The nontrivial final permutation is essential: AHKZ Eq30 orders its mu
twists as (2,11,5,8,6,7)/13; our EG d order is (6,11,2,5,7,8)/13.

The center object `a` must not be confused with the Haagerup invertible line
`alpha`. The full diagonal U theory has center Verlinde symmetry, whereas the
holomorphic E8 extension has a selected first-factor H3 action. The latter
tables use the specified canonical extension and its standard rational-CFT
boundary construction, not only modular covariance.

## Files and array meanings

| File | Meaning |
|---|---|
| `defect_data.json` | Master exact arrays, checks, conventions, source URLs, script SHA256 |
| `modular_S.tsv` | All144 normalized S entries |
| `fusion.tsv` | All1728 integers N[a,b,c], including zero entries |
| `line_eigenvalues.tsv` | All144 eigenvalues S[a,i]/S[0,i] on diagonal bulk sectors |
| `defect_sectors.tsv` | Character tops, conformal weights, twists, character T phases, qdims, Cardy g |
| `twisted_gaps.tsv` |12 diagonal-U twisted Hilbert spaces, their full character matrices and first gaps |
| `Cardy_annuli.tsv` |144 ordered boundary pairs and full open-channel character multiplicities |
| `H3_fusion.tsv` |216 entries for six-object H3 fusion; this ring is not commutative |
| `H3_forgetful.tsv` |6x12 matrix n[x,mu]=dim Hom_C(F(mu),x) |
| `E8_H3_tube_sectors.tsv` |12 multiplicity-space partition functions chi_mu conjugate(chi_E8) |
| `E8_H3_twisted.tsv` |6 actual H3 twisted Hilbert-space partition functions |
| `E8_U_preserving_annuli.tsv` |36 ordered pairs of elementary U-preserving boundaries in full E8 |
| `E8_U_preserving_boundaries.tsv` |Their six exact positive g values, normalized by g_unit=1 |

Each exact cyclotomic entry is an array of12 rational strings encoding
`sum(a[j]*zeta13**j,j=0..11)`, with `zeta13=exp(2*pi*i/13)` and
`1+zeta13+...+zeta13**12=0`. Decimal columns are display values only.

`fusion_N_ab_c[a][b][c]` is the multiplicity of simple c in a tensor b.
For diagonal U the twisted matrix is `N[a,i,j]`, multiplying
`chi_i * conjugate(chi_j)`. The Cardy annulus for boundaries a,b is
`sum_i N[a,b,i] chi_i`; all center objects are self-dual.

The center twist is `theta_i=exp(2*pi*i*h_i)`; the character transformation
includes `exp(-2*pi*i/3)` because c=8. Accordingly theta(d3) has exponent
2/13, but its actual lowest conformal weight is15/13. The total quantum
dimension is D=3*(2+3d), d=(3+sqrt13)/2, and the center's global dimension
is D squared. Boundary `g_i=qdim_i/sqrt(D)`; the JSON stores g squared
exactly because g itself may leave the supplied cyclotomic field.

## Gaps and multiplicities

- Scaling dimension means Delta=h+hbar; spin means h-hbar.
- A scalar has h=hbar, not merely integer spin.
- `ground_Delta` includes the vacuum when present.
- `first_nonidentity_scalar_Delta` omits the vacuum but includes Virasoro
  primary current bilinears in vacuum representations.
- The first positive boundary weight likewise includes the six U currents.
- In the E8-H3 tube table, `none` means there are no scalars at any weight,
  since the left weights are nonintegral modulo1 and right E8 weights integral.
- V_mu is the multiplicity space in Lin--Shao Eq4.1. The actual defect
  Hilbert space has n[x,mu] copies of V_mu. In particular the untwisted
  charged pi2 block has two copies, not one.
- Fractional spinning ground states in an H3-twisted Hilbert space do not
  lower its scalar gap, which is2 for all six defects.

## Exact checks and reproduction

The exporter checks S real symmetric, S squared=1, (S theta) cubed=1,
Verlinde nonnegative integrality, fusion associativity, dimension
multiplicativity, self-duality, the full forgetful based-ring map, and
extension-vector S/theta invariance. Lowest-gap extraction uses only
the supplied top dimensions and dim U1=6. These are algebraic consequences,
not a new proof of VOA construction or the Haagerup associators.

Run from the repository root under the permanent resource guard:

    python hi_cft_safe_run.py -- python c8_physics_20260927/defects.py

There is no parallelism. Reviewed estimate is under150MiB; the fixed rank
prevents dimension growth. Preserve the desktop's permanent memory and CPU
limits. The first guarded run reported roughly22MiB and less than one second.

The original third-party AHKZ PDF in this working directory is for source
inspection only and must be excluded from the release bundle. Primary source
links and plotting scope are recorded in `bootstrap_sources.md`.
