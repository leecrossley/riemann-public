/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# The entire function `P` of `prop:beta`

`latex/notes.tex`, `prop:beta`, uses `P(w) = sin(πw)/(π(1 - w))` and asserts that `P` is entire
(the singularity at `w = 1` is removable) with `P(1) = 1`. Here `P` is defined through the
derivative-slope `dslope` of `w ↦ sin(πw)` at `1`, so that it is entire by construction:

* `differentiable_P`: `P` is entire;
* `P_eq`: `P(w) = sin(πw)/(π(1 - w))` for `w ≠ 1`;
* `P_one`: `P(1) = 1`.

The Beta-integral identity `a^{-w} = P(w) ∫_0^∞ x^{1-w}(x + a)^{-2} dx` and the expansion
`(2π)^w P(w) = w + (1 + log 2π)w² + O(w³)` are in `WeilRH.BetaIntegral` (round 79).
-/

namespace WeilRH

namespace BetaP

open Complex Real

noncomputable section

/-- `w ↦ sin(πw)`. -/
def sinPi (w : ℂ) : ℂ := Complex.sin (π * w)

/-- `P(w) = sin(πw)/(π(1 - w))`, extended across `w = 1` by the derivative. -/
def P (w : ℂ) : ℂ := -(1 / (π : ℂ)) * dslope sinPi 1 w

lemma hasDerivAt_sinPi (w : ℂ) : HasDerivAt sinPi (π * Complex.cos (π * w)) w := by
  have := (Complex.hasDerivAt_sin (π * w)).comp w ((hasDerivAt_id w).const_mul (π : ℂ))
  simp only [mul_one] at this
  exact (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv
    (mul_comm _ _)

/-- **`prop:beta`: `P` is entire.** -/
theorem differentiable_P : Differentiable ℂ P := by
  have hs : Differentiable ℂ sinPi := fun w => (hasDerivAt_sinPi w).differentiableAt
  have hd : DifferentiableOn ℂ (dslope sinPi 1) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).2 hs.differentiableOn
  exact (differentiable_const _).mul (differentiableOn_univ.1 hd)

/-- **`prop:beta`: the formula off `w = 1`.** `P(w) = sin(πw)/(π(1 - w))`. -/
theorem P_eq {w : ℂ} (hw : w ≠ 1) : P w = Complex.sin (π * w) / (π * (1 - w)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : w - 1 ≠ 0 := sub_ne_zero.2 hw
  have h2 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  rw [P, dslope_of_ne _ hw, slope_def_field, sinPi, sinPi, mul_one, Complex.sin_pi, sub_zero]
  field_simp
  ring

/-- **`prop:beta`: `P(1) = 1`.** -/
theorem P_one : P 1 = 1 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [P, dslope_same, (hasDerivAt_sinPi 1).deriv, mul_one, Complex.cos_pi]
  field_simp

end

end BetaP

end WeilRH
