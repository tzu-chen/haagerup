# Published bootstrap comparisons: precise scope

Primary Haagerup source: Jan Albert, Yamato Honda, Justin Kaidi, Yunqin Zheng,
*Haagerup Symmetry in (E8)1?*, Phys. Rev. Lett. 136, 091603 (2026),
DOI 10.1103/6tzz-tvp7, arXiv:2512.08225v2.

- Full primary HTML: https://arxiv.org/html/2512.08225v2
- Original PDF saved unchanged as `ahkz_2512.08225v2.pdf` for local source
  inspection only. Exclude that third-party paper from the distributed
  dataset and release bundle; distribute source links and our own points.
- Figure 2 is physical PDF page 4 (zero-based page 3).
- Figure 3 is physical PDF page 5 (zero-based page 4).
- The plots include the tick c=8. The vertical variable is scalar scaling
  dimension Delta=h+hbar; c means c_L=c_R, not c_L+c_R.
- Figure 2 bounds the lightest nonidentity scalar in the invariant tube
  multiplicity space V_1. Figure 3 bounds the union V_pi2 union V_sigma1.
- Both compare to the selected first-factor H3 symmetry of the full E8
  extension at (c,Delta)=(8,2), using the sector derivation in defects.tex.
- The diagonal U theory instead has the Verlinde symmetry Z(H3); its
  unrestricted scalar gap is 2/3 and its full-Verlinde-invariant gap is 2.
  Its diagonal spectrum is not itself the 12-component H3 bootstrap vector.
- Appendix C states derivative order Lambda=21, precision=320,
  s_max=16 with actual spin truncation |s|<=s_max/2=8. These are published
  numerical bounds, not newly rerun or independently certified all-spin
  functional exclusions.
- Root and structure independently inspected the original rendered panels:
  (8,2) lies visibly below both curves, inside the blue allowed regions.
  It is not a kink or saturation point in either Haagerup plot. No numerical
  curve height is claimed and no curve values have been digitized.
- A low-gap point being below an upper bound is a consistency check, not
  evidence that the bound uniquely identifies this CFT.

Earlier Lin--Shao reference [29] in AHKZ is arXiv:2302.13900,
*Bootstrapping Non-Invertible Symmetries*, PRD 107,125025 (2023).
Its figures study Fibonacci, Ising, and su(2)_2. It explicitly presents
Haagerup as future work. Its Eq(4.1) is nevertheless the appropriate
definition of V_mu used here: H_x=sum_mu W_x^mu tensor V_mu, with
W_x^mu=Hom_C(F(mu),x). V_mu does not include this finite tube-irrep factor.

LOST arXiv:2208.05495 Eq(4.49) supplies the full H3 forgetful table and
Eq(4.50) its untwisted symmetry action. Its results concern asymptotic
densities, not the numerical exclusion plots above. Huang--Lin
arXiv:2102.05664 constructs Haagerup-symmetric topological field theories;
it is not a c=8 modular-bootstrap exclusion plot.

For ordinary scalar-gap comparison root is handling Collier--Lin--Yin,
arXiv:1608.06241, with the convention permitting chiral conserved
currents. The diagonal U point is (8,2/3); the full E8 point is (8,2).
Use the actual published curve, clearly distinguish scalar gap from the
gap to all nonvacuum states, and retain the two different full theories.

The APS primary article page independently confirms the journal citation,
publication date2March2026, DOI, and CC-BY4.0 license for the article and
its components. `bootstrap_overlay.py` clips the two original vector panels,
adds our model points calibrated from their axis ticks, and supplies full
attribution plus metadata. It does not refit or digitize the curves.

No numerical jobs or rendering were run by the structure agent. Root
performed the original PDF rendering and owns all exporter/plot runs.
Download of the original 664KiB PDF used curl only. Only the attributed
figure excerpts, not the complete downloaded paper, belong in the release.
