# Chapter 3 pedagogical revision — October 7, 2026

The user identified that the opening did not say where the state–field map
`Y` lives or define `a_(n)` before using it. This revision addresses that
problem throughout Chapter 3. No other chapter or solution source changed.

The opening now introduces the algebraic state space, linear operators,
formal series, fields with pointwise lower truncation, and the linear
state–field map in that order. It distinguishes a field, a mode operator,
and a mode acting on a state. A type table, coefficient extraction,
formal residues, and a worked vacuum example make the definitions usable.
The locality discussion compares the two geometric-series expansions of
a pole. The OPE is explicitly field-valued, and the conformal grading
explains the difference between VOA indexing and the physics zero mode.

Later additions define the normal-order prescription; Fock creation modes
and the mode-label variable; lattice momentum basis vectors, the vacuum,
and zero-mode action; and the oscillator–exponential commutator needed to
calculate products on excited states. Module maps, tops, grades, ordinary
intertwiners, graded duals, and self-contragredience receive explicit types
or definitions. The parafermion algebra is introduced before its exercise.
The chapter also distinguishes arbitrary cocycle rescaling from an actual
VOA automorphism and explains the quotient's Poisson bracket.

The affine discussion now defines the current basis, level, dual basis,
simple integrable quotient, and Casimir normalization. With long roots of
squared length two, the displayed Casimir has spin-j eigenvalue 2j(j+1);
the denominator 2(k+2) gives the unchanged conformal-weight formula.

## Review and validation

- `scope_construction` independently reviewed the revised opening and
  confirmed the formal-space types, truncation, locality, OPE, and mode
  conventions. Its suggestion to distinguish the vector space of formal
  distributions from a ring of arbitrary same-variable products was added.
- `scope_foundations` reviewed the later additions, identified the Casimir
  wording mismatch, and proposed the lattice-rescaling and integrability
  clarifications. These changes were incorporated.
- Three bounded pdfLaTeX/makeindex passes succeeded. The final log has no
  overfull or underfull boxes, undefined references, or duplicate labels.
  The two pre-existing environment warnings concern the requested LaTeX
  release and disabled shell escape.
- Source and PDF navigation audits pass: 26 main chapters, 96 worked
  examples, 151 exercises with solution anchors, and 343 PDF pages.
  Chapter 3 occupies printed pages 17–32 (PDF pages 36–51).
- The opening's type table, formulas, and worked example were visually
  inspected. Only the pedagogical exposition changed; the exact research
  checkers were not rerun.

The previous PDF, source ZIP, and manifest are preserved in
`editions/20261005/`. Their ZIP contains the original chapter and
verification records. Earlier editorial records retain their original
dates and source/PDF identities; they do not assert checks of this revision.
The scientific-source snapshot remains the October 5 inventory. This
revision does not update the research construction or chain results.

The current build and navigation records identify the revised PDF.
The packaging helper now includes Markdown and Org editorial records as
well as historical text records, following the user's October 7 format
preference. The new source ZIP includes this note.
