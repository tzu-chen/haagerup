# Spectrum producer: derivation, review scope, and run plan

Prepared read-only/algebraically by the finite audit agent. No producer,
numerical job, TeX build, or data export was run by that agent.

## Input and recurrence

Primary source: D. E. Evans and T. Gannon, *The exoticness and realisability
of twisted Haagerup--Izumi modular data*, arXiv:1006.1326, Sections 1.4 and
2.4, equations (1.24), (2.7): https://arxiv.org/abs/1006.1326.

The 12x12 integer characteristic matrix and rational exponent matrix in
`spectrum.py` were compared manually with the primary paper HTML. The
four printed columns are hard-coded independent low-order controls.
The formula uses `g[r]`, where r is the convolution index, derived
directly from `D Xi = Xi[f(Lambda-I)+g C]`. Some renderings of printed
(1.24) show `g[n-1]`, which is not the convolution implied by that ODE.
We do not silently implement that apparent typesetting error.

The scalar modular forms are generated from divisor sums and
Delta=(E4^3-E6^2)/1728; all scalar coefficients are integers. Xi uses
`Fraction` and retains every full 12x12 coefficient matrix. Products
Xi_n C are cached once. The input first column is gamma=0. The source
hashes also bind the earlier project transcription and low-order
recurrence, but those scripts are never imported or executed.

## Dataset scope

Default order24 means 25 coefficients (grades0 through24) for all12
characters; the vacuum needs one less Xi matrix than the nonvacuum
modules. Complete full-CFT spectra are cut at Delta24, not at the far
corner of the rectangular character-product table. A full state at
Delta<=24 cannot involve a chiral grade>24 because all h_i>=0.

Both states and Virasoro-primary components are exported, separately
for each extended sector and aggregated by exact rational Delta and
integer spin. The identity is retained once in primary arrays. At c8,
the Kac determinant implies positive-h Verma modules have no nulls;
the only vacuum primitive null is L_-1 1. This makes Euler-product
descendant subtraction exact. The primary multiplicity data are also
convolved back with the partition numbers to reconstruct all characters.

An independently generated E4/eta^8 series is checked against
chi0+chib+2chia (=chi0+chib+2chic0) at every exported grade. This is a
scalar-character check, not identification of the selected holomorphic
extension algebra. The diagonal U theory and holomorphic E8 full theory
are different full CFTs and have distinct spectra.

## Certified thermal data

The fragment proves the modular heavy-tail inequality used by the code.
With E=Delta-2/3 and all levels through D known, omitted energies exceed
E_D=D-2/3>0. For b>2pi and b'=4pi^2/b:

H(b) <= (L(b)-L(b')) / (exp[(b-b')E_D]-1).

At b=2pi use H<=L'/E_D. For high temperatures use modular invariance to
evaluate Z at b'. Moment tails at b are bounded by H(b0) times
sup_{E>=E_D} E^k exp[-(b-b0)E], k1,2, b0=.9b.

All transcendental arithmetic uses closed Decimal intervals at80digits.
Addition/multiplication/division round toward minus/plus infinity.
Decimal.exp and .ln are correctly rounded; each result is widened one
representable number outward. Pi is enclosed by its first100digits
truncated and that number plus10^-100. Output intervals for Z,logZ,
free energy, energy, heat capacity and entropy are conditional on the
full theory's positivity and modular invariance. Finite coefficients do
not prove those premises. At the selfdual temperature the energy is
set exactly to zero after checking that the independently bounded
moment interval contains zero.

## Root-only run and resource estimate

Mandatory permanent safety guard: only root runs a job, 6GiB hard AS
ceiling,8GiB process-group RSS,32GiB host reserve, two threads and CPUs;
the expired September15 exception is not used. This producer needs far
less: default24 uses roughly26x144 rational matrix entries, equally many
cached products, O(12x25^2) sector rows, and a few hundred scalar thermal
energies. No growing state bases, numerical libraries, workers, caches
from other engines, or subprocesses are loaded. Expected RSS<128MiB,
conservative AS request512MiB; expected runtime10--40seconds, with a
reviewed maximum order64. If those estimates fail, stop and inspect
rather than increase resource caps.

Root uses the permanent launcher with a512MiB address cap:

```
python hi_cft_safe_run.py --limit-mib 512 -- \
  python c8_physics_20260927/spectrum.py --order 24 --delta-cut 24 \
  --outdir c8_physics_20260927/data
```

The program refuses an unlimited or >6GiB address limit and refuses to
overwrite any dataset artifact. For a replay choose a fresh output
directory. `--skip-thermal` isolates exact formal-series controls if a
thermal implementation failure needs investigation; it is not the
intended final run.

Root's initial full run passed in0.91seconds with26144KiB peak RSS.
Subsequent source edits add readable thermal rounding and distinguish
the first-factor invariant marginal count1488 from the both-factor
count36; a final fresh run is required to bind those final sources.
The counts additionally use the canonical extension/action established
in `defects.tex`: first-factor singlets U tensor conjugate(Hprime),
both-factor singlets U tensor conjugate(U).

## Explicit claims not supplied

No OPE coefficient, beta function, exactly marginal deformation,
defect eigenbasis, complete symmetry-charge decomposition, flavored
character, Lean theorem, lattice mode, or new construction proof is
computed. The exact spectral consequences rely on the manuscript's
character identification; the thermal consequences additionally use
its unitary modular full-CFT interpretation.
