module

public import HaagerupIzumi.C8.Theta.M3First
public import HaagerupIzumi.C8.Theta.M3Reverse
public import HaagerupIzumi.C8.Theta.M6First
public import HaagerupIzumi.C8.Theta.M6Reverse

@[expose] public section

/-!
# Theta-coefficient tables of the near-group current obstructions (umbrella)

Proof of Proposition `prop:near-group-current-obstructions` (lines 3614–3777 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): the four coefficient tables,
kernel-checked by exact lattice enumeration, and the linear algebra turning
them into `dim U₁ = 15 + A + 10B`, `14 + 42A` (`m = 3`) and `8 + A`, `5 + 12P`
(`m = 6`).

* `HaagerupIzumi.C8.Theta.Basic`: Gram forms, shells, theta coefficients,
  the box method (`shell_eq_of_box`), `-6 D₂` on coefficients.
* `M3First` (Table 1, `L₇ ⊕ A₂`), `M3Reverse` (Table 2, `G₇⁻`),
  `M6First` (Table 3, `A₁ ⊕ A₁ ⊕ A₂`), `M6Reverse` (Table 4, `G₆⁻`).

The modular part (Weil representations, finite image, pole cancellation) is
external and enters only as the hypothesis `hcancel` of the four obstruction
theorems, together with the printed character values.
-/

#print axioms HaagerupIzumi.C8.Theta.m3First_table
#print axioms HaagerupIzumi.C8.Theta.m3Reverse_table
#print axioms HaagerupIzumi.C8.Theta.m6First_table
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_table
#print axioms HaagerupIzumi.C8.Theta.m3_first_obstruction
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_obstruction
#print axioms HaagerupIzumi.C8.Theta.m6_first_obstruction
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_obstruction
#print axioms HaagerupIzumi.C8.Theta.near_group_formulas_ne_six
