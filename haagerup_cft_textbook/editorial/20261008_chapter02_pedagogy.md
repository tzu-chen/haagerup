# Chapter 2 pedagogical revision — October 8, 2026

The user identified an undefined use of “chiral module” in Section 2.7
and requested a review of the whole chapter for similar gaps. This
revision changes `chapters/r01_cft.tex` and its companion
`solutions/r01_cft.tex`. Other chapter and solution sources, including
the October 7 Chapter 3 revision, are unchanged.

## Changes

- Sections 2.1–2.3 now introduce fields, correlators, chirality, weights,
  radial states, mode operators, primaries, descendants, levels, and
  Verma modules in order. They distinguish a formal null vector from
  its zero image in the physical quotient and explain Gram matrices.
- Section 2.4 defines the chosen chiral algebra, its modules, simple
  sectors, and its vacuum module before using them. Algebra fields and
  intertwining fields are distinguished. The first descendant OPE
  coefficient and the stress Ward identity are explained explicitly.
  The stress example is correctly scoped to the Virasoro vacuum family.
- Section 2.5 defines normal ordering, Wick contractions, current modes,
  charge, the Fock module, and oscillator descendants. It contrasts
  current and Virasoro descendants and explains momentum and winding.
  Rational radius means rational radius squared in the stated convention.
- Section 2.6 explains the cylinder geometry, velocity, Casimir energy,
  and descendant energy/momentum shifts. Euclidean time is now `t_E`,
  leaving `tau` for the torus parameter.
- Section 2.7 recalls what a module is, states the grading assumptions,
  defines its top space, and explains the graded trace and convergence.
  A new worked example counts Fock states through grade four and shows
  that opposite charges give distinct modules with equal characters.
  The full state-space decomposition motivates partition-function
  multiplicities. Modular transformations change a basis of torus
  cycles; neither fundamental torus cycle is contractible.
- Section 2.8 defines the cross-ratio, OPE channel, inverse-Gram
  projector, conformal block, reflection positivity, and sewing. It
  distinguishes global, Virasoro, and extended-algebra blocks and
  explains reduced versus unreduced normalization. A new example sums
  the weight-one global block to a logarithm.
- Section 2.9 distinguishes a dimensionful action coefficient from a
  dimensionless running coupling, defines the beta function, and solves
  its leading marginal approximation. Scalar gaps, symmetry invariance,
  and conformal manifolds now have explicit definitions.
- The exercise solutions use the same block convention, sharpen the
  positive-central-charge stress argument, and explain contact terms,
  redundant couplings, and multiplet recombination. The thermal exercise
  now states the assumptions needed for vacuum dominance.

## Review and validation

Three independent read-only reviews covered Sections 2.1–2.4, 2.5–2.7,
and 2.8–2.9. All passed after incorporating clarifications. The source
audit passes with 26 main chapters, 98 worked examples, and 151 exercises
with dedicated solutions. Three bounded pdfLaTeX/makeindex passes and
the PDF navigation audit pass. The final log has no overfull or underfull
boxes, undefined references, or duplicate labels. The two existing
environment warnings concern the requested LaTeX release and disabled
shell escape.

The revised PDF has 351 pages. Chapter 2 occupies printed pages 10–23
(physical PDF pages 29–42); Section 2.7 begins on printed page 18
(PDF page 37). Representative rendered pages covering the module
introduction, characters, the Fock example, torus geometry, blocks,
and perturbations were visually inspected. This caught an equation
reference that pointed at the cylinder momentum rather than Hamiltonian;
the label was moved and the final PDF rebuilt and re-audited.

The previous PDF, ZIP, and manifest are preserved in `editions/20261007/`.
The October 5 scientific-source snapshot and historical execution records
retain their original identities and dates. No research computation,
scientific-source update, or certificate replay was performed for this
editorial revision. Current infrastructure identities are recorded
separately in `20261008_chapter02_infrastructure.json`. The build and
navigation records bind the current sources and PDF; the source package
includes this note.
