/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Purity

/-!
# Abstract positive definite Hermitian forms

The purity lemmas of `WeilRH.Purity` are stated for a complex `InnerProductSpace`. The Q1/Q2
research dumps (`ai/2026-09-25-zeta-class-axioms/report.md`, Lemma 4.2;
`ai/2026-09-25-finite-field-calibration/report.md`, Theorem 1′) produce positive definite
Hermitian forms *by a formula* (`h(u, v) = tr(u ∪ *v)`, `⟨a, b⟩ = τ(a b†)`) on a plain complex
vector space. This file packages such a form as `WeilRH.PosHermForm` (report convention: linear
in the **first** argument) and transports the purity lemmas to it, by equipping the space with the
inner product `⟪x, y⟫ := h(y, x)` *locally inside the proofs* (no global instance is created, so
the underlying `Module ℂ V` is untouched and every conclusion is about the original `Θ`/`F`).

## Main results

* `WeilRH.PosHermForm`: a positive definite Hermitian form, linear in the first argument.
* `PosHermForm.re_eq_half` / `PosHermForm.isSemisimple`: (P) of weight `κ` ⇒ `Re ρ = κ/2` and,
  in finite dimension, semisimplicity (C-PUR for an abstract form).
* `PosHermForm.norm_eq_rpow` / `PosHermForm.isSemisimple_of_weil`: `h(Fu, Fv) = q^j h(u, v)` ⇒
  `‖α‖ = q^{j/2}` and semisimplicity (C-WEIL for an abstract form).
-/

open scoped InnerProductSpace ComplexConjugate

namespace WeilRH

/-- A positive definite Hermitian form on a complex vector space, in the report convention:
additive and linear in the **first** argument, `conj (h u v) = h v u`, and `0 < Re h(u, u)` for
`u ≠ 0`. (Conjugate-linearity in the second argument follows from Hermitian symmetry.) -/
structure PosHermForm (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The form `h(u, v)`. -/
  toFun : V → V → ℂ
  /-- Additivity in the first argument. -/
  add_left : ∀ u u' v, toFun (u + u') v = toFun u v + toFun u' v
  /-- Linearity in the first argument. -/
  smul_left : ∀ (c : ℂ) u v, toFun (c • u) v = c * toFun u v
  /-- Hermitian symmetry. -/
  conj_symm : ∀ u v, conj (toFun u v) = toFun v u
  /-- Positive definiteness. -/
  re_pos : ∀ u, u ≠ 0 → 0 < (toFun u u).re

namespace PosHermForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : PosHermForm V)

lemma zero_left (v : V) : h.toFun 0 v = 0 := by
  have := h.smul_left 0 0 v
  simpa using this

/-- Additivity in the second argument. -/
lemma add_right (u v v' : V) : h.toFun u (v + v') = h.toFun u v + h.toFun u v' := by
  rw [← h.conj_symm (v + v'), h.add_left, map_add, h.conj_symm, h.conj_symm]

/-- Conjugate-linearity in the second argument. -/
lemma smul_right (c : ℂ) (u v : V) : h.toFun u (c • v) = conj c * h.toFun u v := by
  rw [← h.conj_symm (c • v), h.smul_left, map_mul, h.conj_symm]

lemma zero_right (u : V) : h.toFun u 0 = 0 := by
  have := h.smul_right 0 u 0
  simpa using this

/-- The inner-product core `⟪x, y⟫ := h(y, x)` (Mathlib convention: conjugate-linear in the first
slot). Used only locally inside proofs. -/
noncomputable abbrev core : InnerProductSpace.Core ℂ V where
  inner x y := h.toFun y x
  conj_inner_symm x y := h.conj_symm x y
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · subst hx; simp [h.zero_left]
    · exact (h.re_pos x hx).le
  add_left x y z := h.add_right z x y
  smul_left x y r := h.smul_right r y x
  definite x hx := by
    by_contra hne
    have := h.re_pos x hne
    change h.toFun x x = 0 at hx
    rw [hx] at this
    simp at this

/-- **C-PUR for an abstract form.** If `h(Θu, v) + h(u, Θv) = κ h(u, v)` for a positive definite
Hermitian `h`, every eigenvalue of `Θ` has real part `κ / 2`. -/
theorem re_eq_half (Θ : Module.End ℂ V) (κ : ℝ)
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = (κ : ℂ) * h.toFun u v)
    {ρ : ℂ} (hρ : Θ.HasEigenvalue ρ) : ρ.re = κ / 2 := by
  let _ : NormedAddCommGroup V := h.core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore h.core.toCore
  exact WeilRH.re_eq_half_of_hasEigenvalue Θ κ hP hρ

/-- **C-PUR, semisimplicity, for an abstract form.** In finite dimension `Θ` is semisimple. -/
theorem isSemisimple [FiniteDimensional ℂ V] (Θ : Module.End ℂ V) (κ : ℝ)
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = (κ : ℂ) * h.toFun u v) :
    Θ.IsSemisimple := by
  let _ : NormedAddCommGroup V := h.core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore h.core.toCore
  exact WeilRH.isSemisimple_of_additive Θ κ hP

/-- **C-WEIL for an abstract form.** If `h(Fu, Fv) = q^j h(u, v)` with `q > 0`, every eigenvalue
`α` of `F` satisfies `‖α‖ = q^{j/2}`. -/
theorem norm_eq_rpow (F : Module.End ℂ V) (q j : ℝ) (hq : 0 < q)
    (hW : ∀ u v, h.toFun (F u) (F v) = ((q ^ j : ℝ) : ℂ) * h.toFun u v)
    {α : ℂ} (hα : F.HasEigenvalue α) : ‖α‖ = q ^ (j / 2) := by
  let _ : NormedAddCommGroup V := h.core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore h.core.toCore
  exact WeilRH.norm_eq_rpow_of_weil F q j hq hW hα

/-- **C-WEIL, semisimplicity, for an abstract form.** In finite dimension `F` is semisimple. -/
theorem isSemisimple_of_weil [FiniteDimensional ℂ V] (F : Module.End ℂ V) (q j : ℝ) (hq : 0 < q)
    (hW : ∀ u v, h.toFun (F u) (F v) = ((q ^ j : ℝ) : ℂ) * h.toFun u v) :
    F.IsSemisimple := by
  let _ : NormedAddCommGroup V := h.core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore h.core.toCore
  exact WeilRH.isSemisimple_of_weil F q j hq hW

end PosHermForm

end WeilRH
