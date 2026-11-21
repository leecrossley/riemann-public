/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.BlackBoxes
import WeilRH.ContentXiK

/-!
# The Hadamard product of `ξ_K` (round 68)

`latex/notes.tex`, `thm:imp-stirling` (ii)–(iii) and the function `G_K` built from them
(`eq:G-K`): `ξ_K` is entire of order one, so its zeros `ρ` (with multiplicity) satisfy
`∑ |ρ|^{-2} < ∞` and `ξ_K(s) = e^{a+bs} ∏_ρ (1 - s/ρ) e^{s/ρ}` (no factor `s^k`, since
`ξ_K(0) ≠ 0`).

CONDITIONAL on two black boxes (`WeilRH/BlackBoxes.lean`): `HeckePackage K` (B1: `ξ_K` entire with
`log ‖ξ_K(s)‖ ≤ C ‖s‖ log ‖s‖`) and `HadamardOrderOne` (B3). The comparison
`‖s‖ log ‖s‖ ≤ 2 ‖s‖^{3/2}` puts B1's growth into B3's hypothesis.
-/

open Complex

namespace WeilRH.Hecke

variable {K : Type} [Field K] [NumberField K] (hB : HeckePackage K)

/-- The zeros of `ξ_K` listed with multiplicity: a zero `z` of order `m` gives the indices
`(z, 0), …, (z, m - 1)`. -/
def ZeroIdx : Type :=
  {p : ℂ × ℕ // hB.simplePoles.ξ p.1 = 0 ∧ p.2 < analyticOrderNatAt hB.simplePoles.ξ p.1}

/-- The zero attached to an index. -/
def zero (i : ZeroIdx hB) : ℂ := i.1.1

lemma growth_three_halves :
    ∃ C : ℝ, ∀ z : ℂ, 2 ≤ ‖z‖ →
      Real.log ‖hB.simplePoles.ξ z‖ ≤ C * ‖z‖ ^ (1 + (1 : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hB.growth
  refine ⟨2 * |C|, fun z hz => ?_⟩
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  have hlog0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have hlog : Real.log ‖z‖ ≤ 2 * ‖z‖ ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_rpow_div hn (ε := 1 / 2) (by norm_num)
    linarith
  calc Real.log ‖hB.simplePoles.ξ z‖ ≤ C * ‖z‖ * Real.log ‖z‖ := hC z hz
    _ = C * (‖z‖ * Real.log ‖z‖) := by ring
    _ ≤ |C| * (‖z‖ * Real.log ‖z‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hn hlog0)
    _ ≤ |C| * (‖z‖ * (2 * ‖z‖ ^ ((1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hn) (abs_nonneg C)
    _ = 2 * |C| * ‖z‖ ^ (1 + (1 : ℝ) / 2) := by
        rw [Real.rpow_one_add' hn (by norm_num)]; ring

/-- The fiber of `zero` over `z` has `ord_z ξ_K` elements. -/
noncomputable def fiberEquiv (z : ℂ) :
    {i : ZeroIdx hB // zero hB i = z} ≃ Fin (analyticOrderNatAt hB.simplePoles.ξ z) where
  toFun i := ⟨i.1.1.2, by
    obtain ⟨⟨⟨w, k⟩, h⟩, hw⟩ := i
    simp only [zero] at hw
    subst hw
    exact h.2⟩
  invFun k := ⟨⟨(z, k), (SymEntire.mult_pos_iff hB.simplePoles.differentiable
      hB.simplePoles.xi_one_ne_zero z).1 (Nat.zero_lt_of_lt k.2), k.2⟩, rfl⟩
  left_inv i := by
    obtain ⟨⟨⟨w, k⟩, h⟩, rfl⟩ := i
    rfl
  right_inv _ := rfl

/-- **The Hadamard product of `ξ_K`** (`thm:imp-stirling` (ii)–(iii) applied to `ξ_K`):
`∑_ρ |ρ|^{-2} < ∞` over the zeros with multiplicity, and
`ξ_K(s) = e^{a+bs} ∏_ρ (1 - s/ρ) e^{s/ρ}` with the product converging unconditionally.
CONDITIONAL on `HeckePackage K` and `HadamardOrderOne`. -/
theorem xi_hadamard (hH : HadamardOrderOne) :
    Summable (fun i : ZeroIdx hB => ‖zero hB i‖⁻¹ ^ 2) ∧
      ∃ (a b : ℂ) (g : ℂ → ℂ), ∀ s : ℂ,
        HasProd (fun i : ZeroIdx hB => (1 - s / zero hB i) * exp (s / zero hB i)) (g s) ∧
        hB.simplePoles.ξ s = exp (a + b * s) * g s := by
  set P := hB.simplePoles
  have hpos := SymEntire.mult_pos_iff P.differentiable P.xi_one_ne_zero
  have h0 : analyticOrderNatAt P.ξ 0 = 0 := by
    by_contra h
    exact P.xi_zero_ne_zero ((hpos 0).1 (Nat.pos_of_ne_zero h))
  obtain ⟨hsum, a, b, g, hg⟩ := hH P.ξ P.differentiable ⟨1, P.xi_one_ne_zero⟩
    (growth_three_halves hB) (zero hB)
    (fun i hi => P.xi_zero_ne_zero (by
      have := i.2.1; simp only [zero] at hi; rwa [hi] at this))
    (fun z hz => ⟨fun hfz => ⟨⟨(z, 0), hfz, (hpos z).2 hfz⟩, rfl⟩,
      fun ⟨i, hi⟩ => by
        have := i.2.1; simp only [zero] at hi; rwa [hi] at this⟩)
    (fun z _ => by rw [Nat.card_congr (fiberEquiv hB z), Nat.card_fin])
  refine ⟨hsum, a, b, g, fun s => ⟨(hg s).1, ?_⟩⟩
  rw [(hg s).2, h0, pow_zero, mul_one]

end WeilRH.Hecke
