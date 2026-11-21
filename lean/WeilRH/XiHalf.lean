/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Completed

/-!
# `prop:F0`: `F(0) = ξ(1/2)`, reduced to the sign of `ζ(1/2)`

Source: `latex/notes.tex`, `def:zeta` (d) (`F(z) = Ξ(z) = ξ(1/2 - iz)`) and `prop:F0`
(`F(0) = ξ(1/2) > 0`).

The manuscript's proof has two steps: (a) `ζ(s) < 0` for real `0 < s < 1`, via the alternating
series `η(s) = Σ (-1)^{n-1} n^{-s} > 0` and the identity `η(s) = (1 - 2^{1-s}) ζ(s)` continued to
`Re s > 0`; (b) `Γ(1/4) > 0`, so `Λ(1/2) < 0` and `ξ(1/2) = -Λ(1/2)/8 > 0`.

Step (b) is formalized here unconditionally: `ξ(1/2)` is the real number
`-(π^{-1/4} Γ(1/4) / 8) · ζ(1/2)`, with `ζ(1/2)` real (`riemannZeta_conj`), so
`0 < ξ(1/2) ↔ ζ(1/2) < 0` (`completedXi_half_pos_iff`). Step (a) is **not** in Mathlib at the
pinned version: Mathlib has no Dirichlet eta function, no continuation of the alternating series to
`Re s > 0`, and no sign or zero-free statement for `ζ` on `(0, 1)`. So `prop:F0` itself is proved
here only under the hypothesis `ζ(1/2) < 0` (`F_zero_pos_of_zeta_half_neg`).
-/

open Complex
open scoped ComplexConjugate

namespace WeilRH

/-- The Riemann `Ξ`-function `F(z) = ξ(1/2 - iz)` (`def:zeta` (d)). -/
noncomputable def riemannXiUpper (z : ℂ) : ℂ := completedXi (1 / 2 - I * z)

/-- `F(0) = ξ(1/2)`. -/
@[simp] theorem riemannXiUpper_zero : riemannXiUpper 0 = completedXi (1 / 2) := by
  simp [riemannXiUpper]

/-- `π^{-1/4} Γ(1/4)`, the value `Γ_ℝ(1/2)` as a real number. -/
noncomputable def gammaRHalf : ℝ := Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)

theorem gammaRHalf_pos : 0 < gammaRHalf :=
  mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by norm_num))

theorem Gammaℝ_half : Gammaℝ (1 / 2) = (gammaRHalf : ℂ) := by
  rw [Gammaℝ_def, gammaRHalf, ofReal_mul, ← Complex.Gamma_ofReal,
    ofReal_cpow Real.pi_pos.le]
  push_cast
  congr 2 <;> ring

/-- `ζ(1/2)` is real. -/
theorem riemannZeta_half_im : (riemannZeta (1 / 2)).im = 0 := by
  have h := riemannZeta_conj (1 / 2)
  have hc : conj (1 / 2 : ℂ) = 1 / 2 := by simp [map_ofNat]
  rw [hc] at h
  exact Complex.conj_eq_iff_im.1 h.symm

/-- `ξ(1/2) = -(π^{-1/4} Γ(1/4)/8) ζ(1/2)`, a real number. -/
theorem completedXi_half :
    completedXi (1 / 2) = ((-(gammaRHalf / 8) * (riemannZeta (1 / 2)).re : ℝ) : ℂ) := by
  have hz : riemannZeta (1 / 2) = ((riemannZeta (1 / 2)).re : ℂ) :=
    (Complex.ext rfl (by rw [ofReal_im]; exact riemannZeta_half_im))
  have hΛ : completedRiemannZeta (1 / 2) = Gammaℝ (1 / 2) * riemannZeta (1 / 2) := by
    rw [riemannZeta_def_of_ne_zero (by norm_num), mul_div_cancel₀]
    rw [Gammaℝ_half, ofReal_ne_zero]; exact gammaRHalf_pos.ne'
  rw [completedXi_eq (by norm_num) (by norm_num), hΛ, Gammaℝ_half, hz, ofReal_re]
  push_cast
  ring

/-- `ξ(1/2) > 0` iff `ζ(1/2) < 0`. -/
theorem completedXi_half_pos_iff :
    0 < (completedXi (1 / 2)).re ↔ (riemannZeta (1 / 2)).re < 0 := by
  rw [completedXi_half, ofReal_re]
  have := gammaRHalf_pos
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **`prop:F0`, conditional on `ζ(1/2) < 0`.** `F(0) = ξ(1/2)`, a real number, and it is
positive. The hypothesis is step (a) of the manuscript's proof, not available in Mathlib. -/
theorem F_zero_pos_of_zeta_half_neg (h : (riemannZeta (1 / 2)).re < 0) :
    riemannXiUpper 0 = completedXi (1 / 2) ∧ (completedXi (1 / 2)).im = 0 ∧
      0 < (completedXi (1 / 2)).re :=
  ⟨riemannXiUpper_zero, by rw [completedXi_half, ofReal_im], completedXi_half_pos_iff.2 h⟩

end WeilRH
