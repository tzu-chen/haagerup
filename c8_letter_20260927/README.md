# Physics letter: Haagerup CFTs at c = 8

A short PRL-style preprint about the c = 8 construction. It is modeled
on `reference/Numerical-Evidence-for-a-Haagerup-Conformal-Field-Theory.pdf`.
It gives the explicit construction, the physical data, context and
outlook, and leaves the complete proof to the companion manuscript
`../hi_cft_c8_proof.tex`.

| File | Contents |
|---|---|
| `haagerup_c8_letter.tex` / `.pdf` | The letter (RevTeX 4.2, `aps,prl,twocolumn`; 5 pages) |
| `make_figures.py` | Regenerates `figures/spectrum.pdf` (Fig. 2) from `../c8_physics_20260927/data/` |
| `figures/spectrum_summary.json` | Plotted levels and multiplicities, for checking the figure |
| `texmf/` | RevTeX 4.2 class files from CTAN (the system TeX Live lacks them) |

Fig. 1 (the Dynkin diagram) is TikZ, inline in the source.

## Build

```sh
cd c8_letter_20260927
export TEXINPUTS=.:./texmf/tex/latex/revtex//:
pdflatex haagerup_c8_letter.tex && pdflatex haagerup_c8_letter.tex
```

The bibliography is a hand-written `thebibliography`, so BibTeX is not
needed. For arXiv, upload the `.tex` and `figures/spectrum.pdf`; arXiv
provides RevTeX 4.2 itself.

To regenerate Fig. 2 (it takes seconds and needs little memory):

```sh
python hi_cft_safe_run.py --limit-mib 2048 -- timeout 300s python c8_letter_20260927/make_figures.py
```

## Placeholders to fill

- The affiliation is `[Affiliation]`.
- The acknowledgments read `[To be added.]`.
- The companion paper is cited as "to be published". Its title is taken
  from the current manuscript.
- The last paragraph says the exact data "accompany this preprint".
  That assumes the physics bundle (or part of it) is attached as arXiv
  ancillary files. Otherwise, change the sentence.

## Scope of the claims

The letter states the main results (Rep U ≅ Z(H3), rationality,
unitarity, the H3 ⊠ H3^op lines of (E8)_1) as results, and points to the
companion paper for proofs. It notes that the finite part is exact
computer algebra. Two statements go beyond the manuscript:

- The outlook paragraph "Conformal manifolds with Haagerup symmetry" is
  new. It argues that the first-factor H3 lines survive the 16 exactly
  marginal deformations J_U^a J̄^b of (E8)_1. It also argues that the
  Z(H3) Verlinde lines survive the 4 deformations J_U J̄_U of the
  diagonal theory. Both points are phrased as expectations ("suggest",
  "should"). The manuscript itself says this needs a separate argument.
- The remark that the Z3-neutral ρ̂ eigenvalues (3 ± √13)/2 match the
  anyon-chain observation. It is a comparison, not a claim about the
  continuum limit of the chain.

The footnote on H2 versus H3 repeats the manuscript's caveat. The
lattice-inherited extension U ⊂ V_E8 is identified only up to H2 and
H3. The letter uses the transported extension H', which realizes H3.
