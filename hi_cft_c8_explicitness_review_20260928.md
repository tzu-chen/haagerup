# c=8 draft: what to simplify or make explicit for readers without the scripts

Reviewed on 28 September 2026: `hi_cft_c8_proof.tex` (27 Sept draft, 78 pp.) together with its structure and analytic appendices and the five physics sections. The review follows the node structure of `hi_cft_c8_dependency_flowchart.pdf`.

Line references are to the current sources. Items marked **[checked]** were recomputed or re-derived for this review. The small computations ran under `hi_cft_safe_run.py` (≤1 GiB address cap, ≤11 MiB peak RSS); the rest are hand arithmetic. Everything else is reading.

The draft has 102 `\artifact{...}` pointers (45 main file, 26 structure appendix, 6 analytic appendix, 25 physics sections). None of them resolves for a reader.

---

## 1. Summary: the seven changes that matter most

1. **The theorem hypotheses currently name files.**
   - Prop. 1.1 (proof.tex:204–205) says "Accept the exact lattice identities and provenance recorded in Section M".
   - Thm. 1.3 (proof.tex:246–247) and Thm. 1.4 (proof.tex:270) are phrased the same way.
   - For a reader, this makes the hypothesis a list of filenames.
   - Fix: add one appendix listing the finite inputs as numbered mathematical statements. The flowchart already has exactly these nodes: ambient lattice; initial spaces; lower identities and P₄; Gate 4; Gate 5; embedded factors; core and tops. The theorems then cite that list. Hashes and paths go to a data-availability paragraph.

2. **Much of the missing explicit content is already written, in the companion guide rather than the draft.**
   - Sources: `hi_cft_c8_verification_guide.tex`, `c8_reviewability_20260927/finite_inputs.tex`, and `c8_reviewability_20260927/structural_inputs.tex`.
   - They contain:
     - the Potts field formula;
     - the full PF₁₃ singular rows;
     - the definition of the lattice core T;
     - the four-column check of the positive-stress identity;
     - the Gate 5 scalars;
     - the mod-p reduction map;
     - the irreducibility criterion;
     - the termwise highest-weight check for u.
   - Port the mathematics. Drop the file names, checker names, runtimes and RSS figures. See §2 for where each piece goes.

3. **Gate 4 has a much smaller statement than the draft gives.** **[checked]**
   - From the saved exact weight multiplicities, P = S₃/N₃ has exactly **28** irreducible sl₂⊕sl₂ constituents:
     - 3(1,3) + (1,5) + 5(1,7) + 2(1,9) + 3(1,11) + (1,13) + 2(1,15) + (1,19)
     - \+ (2,2) + (2,4) + 2(2,6) + 2(2,8) + 2(2,10) + (2,12) + (2,14).
   - So dim(E_L P + E_R P) = 322 − 28 = 294 follows from the decomposition. The "644 images of rank 294" is not a separate input.
   - Gate 4 is then equivalent to **9 × 28 = 252** memberships a₀ℓ ∈ W₄, with ℓ running over lowest-weight vectors. The draft instead speaks of 2,898 identities plus saturation.
   - The spanning check splits by Cartan weight into blocks of size at most 5. It is not a 322 × 322 minor.
   - The twelve "singlet" targets are exactly the pairs (charged field a, a constituent of P of the same type as a): 1+2+2+1+1+2+2+1 = 12.
   - The 28 charged seeds in the charged-span certificate are the same count seen from the highest-weight side.

4. **Gate 5's inputs can be printed in full.**
   - Seven of the eight brackets are literally zero vectors, and the eighth is a two-term identity.
   - c₃ and c₆ are explicit elements of ℚ(√13,√−3).
   - The draft instead says "exact combinations of the lower relations establish…" (proof.tex:995) and names vectors by record ID: `r3_000910`, `r3_000899` (proof.tex:992–993).

5. **Several objects are never defined in the draft.**
   - **The lattice–Potts core T.** The only pointer is "described in `hi_cft_20260923_proof_report.md`, Section 4" (structure.tex:50–51).
   - **The Potts and PF₁₃ fields.**
   - **The eight charged highest vectors and e, f.** Without them, the basis and phases of the §4 coupling table cannot be reproduced.
   - **Why u has its coefficients.** **[checked]** The Cartan-weight-(1,13) subspace of B₂ is exactly span{e^a, e^b, e^c}:
     - exactly three norm-4 lattice vectors have this weight, and no root does;
     - each exponential is highest on its own (termwise, as the verification guide shows);
     - the torus elements commuting with K are only t(α₅) = ±1, an overall sign.
     - So u is a genuine choice of a point in P²(ℂ). The sentence "there is no remaining continuous parameter" (proof.tex:491–492) is true of u once it is fixed, but reads as if the highest-weight condition forced it.
     - Say what singles out this point: how it was found, and what is known about other points.

6. **Delete the machine and audit material.**
   - Resource limits (6 GiB / 8 GiB / 32 GiB, proof.tex:1293–1301).
   - `hi_cft_safe_run.py` commands (proof.tex:1221–1223, spectrum.tex:381–385) and `safe_lean.py` commands (proof.tex:1341–1351).
   - Hash and bundle talk.
   - Audit labels a reader cannot decode: "formerly marked F2", "earlier obligations A2 and A3", R1/R2/F1 boxes, "unfinished final block in this historical directory".
   - Collapse Apps. M, N, O into one page (§4 below).

7. **State plainly what stays computational** (§3).
   - Those steps cannot be made hand-checkable. The paper should state each claim precisely, describe the arithmetic model and algorithm, print one worked instance, and give sizes.
   - If the paper is meant to be verifiable without trust, the small standalone checkers already exist and could be released as ancillary files, since they don't import the research engine.
   - Caveat: they recheck saved vector identities, not the mode products. An independent lattice mode engine is the remaining gap.

---

## 2. Node by node

### Page 2 of the flowchart: finite construction (Apps. A–E)

**FINITE INPUT — ambient lattice VOA (App. A).** This part is already explicit. Improvements:
- **The highest-weight check for u.** proof.tex:483–485 says "Substitution in the lattice formula verifies…". Replace it with the verification guide's table (Gα, norms 4, pairings 1 and 13 with ℓ and r), which shows every raising pairing is ≥ 0 termwise.
- **The choice of u.** Add the remark from item 5 of §1.
- **Gauge.** Lead with the unitary-basis form g⁻¹u = e^a + ζe^b + ζ̄e^c, ζ = (√13+3i√3)/√40, |ζ| = 1 (already at proof.tex:486–490). Relegate the torus gauge and the transported PCT (proof.tex:438–480) to a sentence saying computations use a conjugated gauge to keep coefficients in ℚ(√13,√−3). At present the reader meets the gauge before the field.

**FINITE INPUT — initial spaces (Input A.2).**
- **Print S₂.** The eight charged highest vectors have 61, 32, 32, 9, 42, 32, 22 and 3 lattice monomials (233 in total); e has 70. The companion's `grade2_fields.tsv` has all 337 monomials of u, ω_B, ω_L, ω_R, e, f, p, z. That fits in a 3–4 page appendix table.
- **A canonical description, cheap and clarifying.**
  - The charged fields span the affine-primary joint highest vectors of U₂.
  - Each is unique up to scale given its weight, except the two (1,9) fields, which are separated by e₁ = 200/1271 versus 1512/1271.
  - e is the unique conformal vector of central charge 2400/1271 in (U₂)^K ⊖ span(ω_{A1,1}, ω_{A1,39}).
  - State the normalization rule used for the saved vectors. couplings.tex:23–24 says only "normalization inherited from its saved lattice vector".
- **S₃ structure.** **[checked, from the saved checkpoint]** Print the current decompositions:
  - S₃: 956-dimensional, 87 constituents.
  - N₃: 634-dimensional, 59 constituents.
  - P: 322-dimensional, 28 constituents (list in §1).
  - The build history also shows that P is generated as a current module by u₀S₂, (a₃)₀S₂ and (a₆)₀S₂. u₀S₂ alone gives 290 of the 322 dimensions.
- **A consistency check a reader can do by hand.** **[checked]**
  - θ_{E₆}θ_{A₂}/η⁸ gives dim B_n = 1, 86, 1370, 11586.
  - This equals dim U_n + dim X_n, using U = 1, 6, 120, 956 and X from the Evans–Gannon b-row 80, 1250, 10630.
  - The check needs only the theta series (E₆: 1, 72, 270, 720; A₂: 1, 6, 0, 6).
  - It is not a proof, but it ties 120 and 956 to the character theorem without any script.

**FINITE INPUT — lower identities and P₄ (Input B.6).**
- **Say what the 3,970 identities are.** Certificate B.6 says only "3,970 completed exact identities" (proof.tex:739). The producer's task list is:
  - 10 quasiprimarity checks L(1)a = 0;
  - (a)₀b ∈ S₃ and (a)₁b ∈ S₂ for the 10 primitive fields a and all 120 basis vectors b (2,400 identities);
  - k₀b ∈ S₂ and k₁b ∈ K for the six currents (1,440);
  - L(1)b ∈ K (120).
- **Only some of these carry mathematical content.** The (a)₀b identities are coordinate expressions, true by the definition of S₃. The content is:
  - S₂ is closed under a·b = a₁b, the Griess algebra of U;
  - S₂ is current-stable;
  - L(1)S₂ ⊂ K.

  Saying this is short and much more readable.
- **P₄.** State the recipe. P₄ is the (1,3)-isotypic projection of (a₀)₀p, followed by lowering. Here a₀ is the charged (1,5) field and p is a weight-(0,−2) vector of S₃ obtained by lowering from u₀S₂. Fix the normalization of q₋. The draft says "obtained from an actual a₀p by current-zero-mode projectors" (proof.tex:705).
- **Cut** "A computational solver may use a proper subset of actual words" (proof.tex:702–703).

**FINITE INPUT — Gate 4 (App. C).** Restructure. proof.tex:782–827 interleaves provenance with logic: "2,145 … 130 further … 118 … twelve", "prime search selects 21 columns", "final verifier repeats…". Proposed order:
1. The table of the 28 constituents of P.
2. Lemma: for joint-highest a, the map [p] ↦ [a₀p] is raising-equivariant. So it vanishes iff it vanishes on a set spanning the 28-dimensional space P/(E_LP+E_RP).
   - That quotient is graded by the lowest weights (0,−2)×3, (0,−4), (0,−6)×5, (0,−8)×2, (0,−10)×3, (0,−12), (0,−14)×2, (0,−18), (−1,−1), (−1,−3), (−1,−5)×2, (−1,−7)×2, (−1,−9)×2, (−1,−11) and (−1,−13).
   - This lemma is Lemma C.1, stated so that the finite content is visible.
3. Finite input: for each a ∈ {a₀,…,a₇, e}, a set Σ_a ⊂ S₃ with a₀Σ_a ⊂ W₄ whose image spans that quotient (weight blocks of size at most 5).
4. The twelve same-type pairs are handled by the singlet projector (Lemma C.2). Print the companion's four sample entries of target 11 to show the format.
5. **The mod-p lemma, made exact.** proof.tex:784–788 says "a nonzero minor at the good split prime" without the map. **[checked]** State it:
   - the reduction ℤ[D⁻¹, s, t] → 𝔽_p with p = 1,000,003, s ↦ 231543, t ↦ 1000 (231543² ≡ 13 and 1000² ≡ −3 mod p);
   - p must not divide the denominators;
   - it gives rank lower bounds only.
   - This is four lines in `finite_inputs.tex`.

**ARGUMENTS C.3, D.1, D.2.** These are self-contained. One gap: proof.tex:885–886, "The affine normal and derivative part of S₂ is handled by the current iterate identities", deserves a displayed formula.

**FINITE INPUT — Gate 5 (App. D).** Port the Gate 5 subsection of `finite_inputs.tex`, minus file names:
- **The zero brackets.** (a₀)₀a₃ = (a₁)₀a₃ = (a₂)₀a₃ = (a₃)₀a₆ = (a₅)₀a₃ = (a₆)₀a₃ = (a₇)₀a₃ = 0 as vectors.
- **The one nonzero bracket.**
  - 554600 (a₄)₀a₆ = (−216348s + 83596t)R₁ + (34265s + 103895t)R₂.
  - R₁ = ((1+4st)/25)(E_L)₋₁a₁ and R₂ = ((81−15st)/71)((E_L)₋₁a₂ − ((−7+3st)/20)R₁), both in N₃.
  - These replace the table at proof.tex:995–1011.
- **The bottom scalars.** c₃ = (−593619 + 1349829s + 1399567t − 1072149st)/9831968 and c₆ = −57967/42018 + (22295/798342)st, both visibly nonzero.
- **Replace the record IDs by the properties actually used.**
  - p₃ ∈ S₃ has weight (0,−14) and p₆ has weight (−1,−9), with (a₃)₀p₃ ≡ c₃q₋ and (a₆)₀p₆ ≡ c₆q₋ mod N₄.
  - In the checkpoint both come from u₀S₂ by eight to nine lowering steps with elimination. The argument uses only their weights and the nonzero coefficients.
- **Charged span.** Note that its 28 seeds are one per constituent of P (highest-weight side).

**ARGUMENT — all-weight theorem (B.2, B.3) and CONCLUSION — properness.** These are self-contained. Remove the `.md` pointer at proof.tex:681–682; see §5 for the helper agent's check of that note. Fold the F1 box (proof.tex:1098–1109) into the computations appendix. Delete "The 30 earlier prime-only a₁P₄ tests … are not an omitted gate" (proof.tex:1074–1075) and "formerly marked F2" (proof.tex:691).

### Page 3 of the flowchart: rationality, branching, characters (Apps. F–H)

**FINITE INPUT — embedded structural data (Certificate F.1).** At present this is a list of 14 file names (structure.tex:19–61). Port from `structural_inputs.tex` and the guide:
- **Potts.**
  - p = (h_α(−1)² + h_β(−1)² + h_α(−1)h_β(−1))/15 · 𝟏 + Σ p_δ e^δ, with α = (0,0,0,1,1,0,−1,−1), β = (1,1,0,−1,−1,0,0,0) and the six-entry p_δ table.
  - The w_P formula.
  - The worked checks p₃p = (2/5)𝟏 and θp = p.
  - About 15 lines.
- **PF₁₃.** Print the complete singular rows: the self-row, the a_n b row, the third row, R = a₁d as a normal polynomial, and a₀d, with the normalization σ² = −(7+3st)/9223500. About one page.
  - These are exactly the hypotheses of Prop. F.2. The draft currently only describes them ("agree with the parafermion rows at c = 8/5, λ = 14/473", structure.tex:35–36).
- **Positive-stress identity.**
  - Port the four-column table: norms N = (1/2, 117/82, 1200/1271, 35/31) and the overlaps ⟨w_i,p⟩ = (0, 13/205, 108/1271, 39/155) and ⟨w_i,z⟩ = (0, 21/205, 780/1271, 13/155).
  - Port the four one-line coefficient checks.
  - Equation (positive-stress) then becomes hand-checkable given p and z.
- **Membership of p, w_P, z, w in S₂ and S₃.** State these as memberships witnessed by 33-word and 42-word expressions. They are not printable; describe them.
- **Cut** the second sentence of R1 (structure.tex:98–105) once the formulas are in.

**FINITE INPUT — core and finite tops.**
- **Define T in the draft.** structure.tex:421–441 uses it without definition. **[checked]**
  - The lattice is L_T = ℤα_L + ℤt, with t = (1,1,0,1,1,−3,1,1) = (3/2)α_L + ½h_R. Its Gram matrix is [[2,3],[3,24]], with discriminant ℤ/39. So L_T is the part of the E₆⊕A₂ lattice lying in the Cartan plane of K; say this, it motivates everything.
  - Put ρ = t/3 = α_L/2 + h_R/6. u lies in V_{L_T+ρ} ⊗ ψ, where ψ is a Potts simple current: p₁u = (2/3)u, with Heisenberg weight 4/3.
  - u₋₅(u₋₃u) = −(3/5)e^t, so V_{L_T} ⊂ U.
  - T = (V_{L_T}⊗P₀) ⊕ (V_{L_T+ρ}⊗ψ) ⊕ (V_{L_T+2ρ}⊗ψ²).
  - ω_T = ¼h_{α_L}(−1)² + (1/156)h_R(−1)² + p, so c_T = 14/5. The draft uses this implicitly in the row check "Z = h_{A_L}d − L − Q/156 − P".
  - Rep T ≃ Fib ⊠ C(ℤ/13, q).
  - Derive eq. (core-charge-minimum) from the discriminant form. At present nothing derives it, not even the source note.
  - **Convention clash:** the source record uses q(j) = 3j²/13, the draft uses −j²/13. They agree under j_draft = 6·j_record, which is never stated.
  - The certificate is `hi_cft_20260923_proof_rational_core.json`, which the draft never cites. `core_extension.json`, which the draft does cite, covers only the six witnesses.
  - **Notation:** the companion calls the lattice basis ℓ, v and writes r = H. Here ℓ clashes with the parafermion λ = 14/473 and v with the witness vectors. Use α_L, t, h_R instead.
- **The six order-13 witnesses.**
  - Port the eigenvalue table: q₁ = 0, z₁ = 12/13, p₁ = 2/3 and (ω_T)₁ = 14/13 at weights (±1,±5) and (0,±8).
  - Print at least one of the six 21-term vectors.
  - Port the arithmetic showing that only the two inverse simple currents start at 12/13. The draft only asserts this (structure.tex:440–441).
- **The 80-dimensional current complement** (structure.tex:588–594).
  - State the irreducibility criterion (unique joint eigenline, cyclic, *-closed ⇒ irreducible). The draft states it only for the 81-dimensional tops (structure.tex:600–604).
  - Give the K-decomposition **[checked by hand]**: (1,3) + 2(1,5) + (1,7) + (1,9) + (1,11) + (2,4) + (2,6) + (2,10) = 80. It comes from E₆ ⊃ A₁×A₅, the principal sl₂ in A₅ and A₂, and Λ³ of the 6-dimensional irrep = 10 + 6 + 4.
  - The distinguished eigenline is the (0,10) top of (1,11), with seed e^{(1,1,1,1,1,0,0,0)}.
  - *Optional upgrade:* replace the 80-row cyclic transcript by a spanning tree of 8–9 nonzero reduced matrix elements between K-constituents, plus a 2×2 check on the doubled (1,5). Each entry is a root-state computation using the companion's elementary zero-mode rules. This needs a small new computation.
- **The 81-dimensional tops.** Print the Cartan multiplicity rows (1,2,3,3,3,3,2,1 and 1,2,4,5,7,7,7,5,4,2,1) and the table of seed momenta 3β₆₈.
- **Fold R2** (structure.tex:575–586) into the input statement.

**ARGUMENT nodes G.2–G.5 and H.** These are pure mathematics with citations. Remove the `.md` pointers (structure.tex:409, 463–464, 1157–1161, 1383–1385, 1566) after the completeness check in §5. Also delete "removes the formerly used pointwise stabilizer calculation" (structure.tex:1162–1163).

### Page 4 of the flowchart: analytic realization (Apps. I–K)

This part does not depend on certificates. Remove the `.md` pointers (analytic.tex:224–226, 366–367, 986–990). The review box (analytic.tex:35–45) uses "the earlier obligations A2 and A3" and "resolves A1". Either define A1–A3 once, since the flowchart uses them, or use descriptive names.

### Page 5 of the flowchart: physics (§§2–7)

- **§2 (spectrum)** is self-contained given EG's Λ and χ. Cut the producer and replay paragraphs (spectrum.tex:360–389) to "tables supplied as ancillary data". Move the Lean paragraph (spectrum.tex:291–301) out of the physics section.
- **§3 (correlators)** has explicit formulas. Cut correlators.tex:324–354 to one sentence.
- **§4 (couplings).** The 113³ tensor cannot be printed, but it can be reduced. **[checked, counting]**
  - sl₂⊕sl₂ covariance plus multiplicity-free Clebsch–Gordan reduces it to reduced couplings on at most **429** allowed ordered multiplet triples, or **256** using the i↔j symmetry of the primary projection.
  - That is a printable Wigner–Eckart table (about 3 pages) with a stated CG convention.
  - It is also the Griess algebra of U restricted to primaries. That is the same product as the lower-closure statement (a)₁S₂ ⊂ S₂. One sentence linking §4 to App. B would help both.
  - It requires the normalization rule from App. A.
- **§§5–6** are explicit. Cut defects.tex:395–411 to a sentence.

### Apps. M, N, O

- **App. M (ledger).** Replace it with about half a page covering:
  - the arithmetic model: ℚ(√13,√−3) in the basis 1, s, t, st, sparse Fock vectors, and the lattice mode formula (A.3);
  - which steps use mod-p reduction (rank lower bounds only);
  - data sizes;
  - where the data lives.

  Drop the 640 hashes, the filenames, the "supplemented ledger" discussion, the replay commands and the desktop resource policy.
- **App. N (Lean).** The files are also inaccessible to readers. Reduce this to one sentence or release them.
- **App. O (compilation).** Delete.
- **§1.2 ("How the qualifications are used") and its table.** Condense. Once the finite inputs are listed, most of it is redundant.

---

## 3. What stays computational

These cannot be printed in full. For each, the draft should state the precise claim, print one worked instance, and give its size.

| Finite input | Size | What to print |
|---|---|---|
| Minimal generation of S₂ | 120-step queue; 644 candidate insertions | the queue algorithm (already sketched at proof.tex:532–540) |
| Lower identities | 3,970 tasks; 224,480 input sparse terms | the task list (§2) and one example |
| Gate 4 seeds | 2,145 + 118 memberships in W₄ | the 28-constituent formulation and one example |
| Gate 4 singlet identities | 12 relations with 21 columns; 66,610 sparse terms (≈2.45 MB compressed) | the format and four sample coefficients |
| Rank witnesses | 9 augmented ranks, plus the charged span | the weight-block structure (blocks of size ≤ 5) |
| PF₁₃ nonlinear products | a₀b has 25,045 terms; R has 28,342 | the polynomial rows (short) |
| Factor membership | w_P: 33 words; w: 42 words | a few coefficients, as the companion does |
| 80 and 4 × 81 cyclic spans | 80 plus 4 × 81 recipe rows | the criterion, the eigenline and the first step |
| §4 tensor | 1,137 lattice products; 3,512 projections | the Wigner–Eckart table (optional) |

---

## 4. Suggested order of work

1. Replace file-based hypotheses by a numbered finite-inputs appendix and cite it in Prop. 1.1 and Thms. 1.3–1.4.
2. Port from the companion: Potts, PF₁₃ rows, T, the positive-stress table, the Gate 5 scalars, the u check and the mod-p lemma. This is mostly copy-editing.
3. Rewrite App. C around the 28-constituent table. Add the S₃, N₃ and P decompositions and the dim B_n consistency check.
4. Generate the S₂ appendix table from `grade2_fields.tsv` / `hi_cft_20260923_c8_exact_fields.json`.
5. Cut Apps. M, N, O, the resource details and the audit language.
6. Optional: the Wigner–Eckart table for §4; a spanning-tree certificate for the 80; a paragraph on how u was chosen.

---

## 5. Cited research notes: check against the draft

A read-only helper agent compared each of the 16 cited `.md` notes with the passage that cites it. I spot-checked its T-lattice claims (above).

| Note (cited at) | Verdict | Port or fix |
|---|---|---|
| recursive_strong_certificate (proof.tex:682) | Draft is complete: same induction, same ordering | Drop the pointer |
| proof_report §4 (structure.tex:50) | **Draft is missing T entirely** | See the "Define T" bullet in §2 |
| rationality (structure.tex:409) | Complete | State the two Etingof–Penneys hypotheses explicitly: 𝟏 is a summand of Y⊗X, and dim End(X^{⊗n}) < n! |
| order13_core (structure.tex:463) | Complete, with small gaps | Add that 12/13 < 1, so the witness is not a parafermion descendant. Add the "only (13,1) and (13,12) have weight 12/13" arithmetic. Add the check dim ker q₁ on S₂ = 25 = dim (A_L)₂. |
| m3/m6 universal data and character obstructions (structure.tex:1158–1161) | Complete but compressed | For m=3, the moment values S₁ = (−√21+i√3)/2 and division by P's twist sums. For m=6, the Gauss-sum step (Dim F/d = 4√3) and the two STS equations. Why A = 8 for the A_{2,9} reference model: its 8-dimensional top is at 1/4. Why the polar coefficient is halved, and why −w/3 is the unique shortest vector. The notes still say "conditional"; the draft rightly does not. |
| rank6_indicators, rank6_root_audit (structure.tex:1384) | Complete | State Larson's Thm 1.3 (N ≥ \|B\|φ(2D)). Give the mod-4 argument that m and t are even when D = 10. Say D = 2 is excluded by D ≡ 1 (mod 3). Show the unsimplified indicator equation. |
| conditional_characters (structure.tex:1566) | Complete | Optionally cite EG eq. (1.24) |
| rank46, rank6_center (analytic.tex:224–226) | Complete | The notes rely on Aut(B/U) = 1 and cite a different source for m ∈ {0,2,3,6}. The draft's no-sign-extension route supersedes both. **Double-check the theorem number cited from Larson 1401.1879**: the draft says Thm 1.1, the 25 Sept audit recorded Thm 4.11. |
| m3_unitarity_scope (analytic.tex:367) | Draft is more detailed than the note | Drop the pointer |
| c8two_final_theorem, certificate_audit (analytic.tex:987) | Complete | Port the 23+1 Gate 5 channel count: min(m,2)+1 per charged field, giving 3+3+3+3+2+3+3+3. The notes use generators K, S₂, P₃, P₄ where the draft uses K, S₂, S₃, P₄; these are equivalent. |

The upshot is that the notes contain no argument the draft needs except T. All other `.md` pointers can be deleted once the small completions above are made. The biggest gap is T, followed by the compressed computations in G.3.
