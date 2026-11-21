/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Purity from a positive compatible form (claims C-PUR and C-WEIL)

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §4.3 (identity (P)) and §5
(Proposition 1 and its proof); §7.1 for the finite-field (multiplicative) form.

## Conventions

The report's Hermitian forms are *linear in the first argument*. Mathlib's inner product
`⟪x, y⟫_ℂ` is conjugate-linear in the first argument. We therefore define the report-convention
form `hForm u v := ⟪v, u⟫_ℂ`, which is linear in `u`, conjugate-linear in `v`, Hermitian and
positive definite; every hypothesis below is stated with `hForm`, verbatim from the report.
`hForm_add_iff_inner` shows that for real `j` the additive identity (P) reads the same in
either convention.

## Main results

* `WeilRH.re_eq_half_of_hasEigenvalue` (C-PUR, eigenvalues): (P) with weight `j` forces every
  eigenvalue `ρ` of `Θ` to satisfy `ρ.re = j / 2`. No finite-dimensionality is needed.
* `WeilRH.isSemisimple_of_additive` (C-PUR, semisimplicity): in finite dimension `Θ` is
  semisimple (`Module.End.IsSemisimple`).
* `WeilRH.maxGenEigenspace_eq_eigenspace_of_additive`: generalized eigenspaces are eigenspaces.
* `WeilRH.norm_eq_of_hasEigenvalue_mul` / `WeilRH.isSemisimple_of_mul`: multiplicative version,
  `h(Fu, Fv) = c • h(u, v)` with `c > 0` forces `‖α‖ = √c` and semisimplicity.
* `WeilRH.norm_eq_rpow_of_weil` (C-WEIL): `c = q ^ j`, `q > 0` gives `‖α‖ = q ^ (j / 2)`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace WeilRH

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The report's Hermitian form: linear in the first argument, conjugate-linear in the second,
positive definite. It is Mathlib's inner product with the arguments swapped. -/
noncomputable def hForm (u v : E) : ℂ := ⟪v, u⟫_ℂ

omit [InnerProductSpace ℂ E] in
lemma hForm_def [InnerProductSpace ℂ E] (u v : E) : hForm u v = ⟪v, u⟫_ℂ := rfl

/-- `hForm` is linear in its first argument. -/
lemma hForm_smul_left (c : ℂ) (u v : E) : hForm (c • u) v = c * hForm u v := by
  simp [hForm]

/-- `hForm` is conjugate-linear in its second argument. -/
lemma hForm_smul_right (c : ℂ) (u v : E) : hForm u (c • v) = conj c * hForm u v := by
  simp [hForm, mul_comm]

/-- `hForm` is Hermitian. -/
lemma hForm_conj (u v : E) : conj (hForm u v) = hForm v u := by
  simp [hForm]

/-- `hForm` is positive definite. -/
lemma hForm_self_re_pos {v : E} (hv : v ≠ 0) : 0 < (hForm v v).re := by
  simpa [hForm] using (re_inner_self_pos (𝕜 := ℂ)).2 hv

/-- For real `j`, the report-convention identity (P) is equivalent to the same identity for
Mathlib's inner product. -/
lemma hForm_add_iff_inner (Θ : Module.End ℂ E) (j : ℝ) :
    (∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) ↔
      (∀ u v, ⟪Θ u, v⟫_ℂ + ⟪u, Θ v⟫_ℂ = (j : ℂ) * ⟪u, v⟫_ℂ) := by
  constructor
  · intro h u v
    have := congrArg conj (h u v)
    simp only [hForm, map_add, map_mul, inner_conj_symm, Complex.conj_ofReal] at this
    linear_combination this
  · intro h u v
    have := h v u
    simp only [hForm]
    linear_combination this

/-! ### The additive (infinitesimal) form: C-PUR -/

section Additive

variable (Θ : Module.End ℂ E) (j : ℝ)
  (hP : ∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v)
include hP

/-- **C-PUR, eigenvalues.** If `h(Θu, v) + h(u, Θv) = j · h(u, v)` for a positive definite
Hermitian `h`, every eigenvalue of `Θ` has real part `j / 2`. Any (possibly
infinite-dimensional, possibly incomplete) complex inner product space. -/
theorem re_eq_half_of_hasEigenvalue {ρ : ℂ} (hρ : Module.End.HasEigenvalue Θ ρ) :
    ρ.re = j / 2 := by
  obtain ⟨v, hv⟩ := hρ.exists_hasEigenvector
  have hΘv : Θ v = ρ • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have key := hP v v
  rw [hΘv, hForm_smul_left, hForm_smul_right] at key
  -- key : ρ * h + conj ρ * h = j * h, with h = hForm v v
  have hpos := hForm_self_re_pos hv0
  have hreal : (hForm v v).im = 0 := by
    have := hForm_conj v v
    have h2 := congrArg Complex.im this
    simp only [Complex.conj_im] at h2
    linarith
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, hreal,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  have : (2 * ρ.re - j) * (hForm v v).re = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hpos.ne'

/-- The orthogonal complement of a `Θ`-invariant submodule is `Θ`-invariant. -/
lemma orthogonal_mem_invtSubmodule {W : Submodule ℂ E} (hW : W ∈ Module.End.invtSubmodule Θ) :
    Wᗮ ∈ Module.End.invtSubmodule Θ := by
  rw [Module.End.mem_invtSubmodule]
  intro v hv
  rw [Submodule.mem_comap, Submodule.mem_orthogonal]
  intro w hw
  have hΘw : Θ w ∈ W := (Module.End.mem_invtSubmodule Θ).1 hW hw
  have h1 : ⟪w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal W v).1 hv w hw
  have h2 : ⟪Θ w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal W v).1 hv (Θ w) hΘw
  have := ((hForm_add_iff_inner Θ j).1 hP) w v
  rw [h1, h2, mul_zero, zero_add] at this
  exact this

/-- **C-PUR, semisimplicity.** In finite dimension, `Θ` is semisimple: every invariant subspace
has an invariant complement (its orthogonal complement). -/
theorem isSemisimple_of_additive [FiniteDimensional ℂ E] : Θ.IsSemisimple := by
  rw [Module.End.isSemisimple_iff]
  intro W hW
  exact ⟨Wᗮ, orthogonal_mem_invtSubmodule Θ j hP hW, W.isCompl_orthogonal⟩

/-- **C-PUR, no Jordan blocks.** In finite dimension every generalized eigenspace of `Θ` equals
the corresponding eigenspace. -/
theorem maxGenEigenspace_eq_eigenspace_of_additive [FiniteDimensional ℂ E] (ρ : ℂ) :
    Θ.maxGenEigenspace ρ = Θ.eigenspace ρ :=
  (isSemisimple_of_additive Θ j hP).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace ρ

end Additive

/-! ### The multiplicative form: C-WEIL -/

section Multiplicative

variable (F : Module.End ℂ E) (c : ℝ) (hc : 0 < c)
  (hM : ∀ u v, hForm (F u) (F v) = (c : ℂ) * hForm u v)

omit hc in
include hM in
/-- Multiplicative purity: if `h(Fu, Fv) = c · h(u, v)` then every eigenvalue satisfies
`‖α‖ ^ 2 = c`. -/
theorem norm_sq_eq_of_hasEigenvalue_mul {α : ℂ} (hα : Module.End.HasEigenvalue F α) :
    ‖α‖ ^ 2 = c := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hFv : F v = α • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have key := hM v v
  rw [hFv, hForm_smul_left, hForm_smul_right, ← mul_assoc, Complex.mul_conj] at key
  have hpos := hForm_self_re_pos hv0
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq] at hre
  have : (‖α‖ ^ 2 - c) * (hForm v v).re = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hpos.ne'

include hM in
/-- Multiplicative purity: `‖α‖ = √c`. -/
theorem norm_eq_of_hasEigenvalue_mul {α : ℂ} (hα : Module.End.HasEigenvalue F α) :
    ‖α‖ = Real.sqrt c := by
  rw [← norm_sq_eq_of_hasEigenvalue_mul F c hM hα, Real.sqrt_sq (norm_nonneg _)]

include hc hM in
/-- `F` is injective (it is `√c` times an isometry). -/
lemma injective_of_mul : Function.Injective F := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  by_contra hv0
  have key := hM v v
  rw [hv, hForm, inner_zero_left] at key
  have hpos := hForm_self_re_pos hv0
  have := congrArg Complex.re key
  rw [Complex.zero_re, Complex.re_ofReal_mul] at this
  have : c * (hForm v v).re > 0 := mul_pos hc hpos
  linarith

include hc hM in
/-- **C-WEIL, semisimplicity (multiplicative form).** In finite dimension, `F` is semisimple. -/
theorem isSemisimple_of_mul [FiniteDimensional ℂ E] : F.IsSemisimple := by
  rw [Module.End.isSemisimple_iff]
  intro W hW
  refine ⟨Wᗮ, ?_, W.isCompl_orthogonal⟩
  -- `F` restricts to a bijection of `W`, so every `w ∈ W` is `F w'` with `w' ∈ W`.
  let G : W →ₗ[ℂ] W := F.restrict (p := W) (q := W) (fun x hx => hW hx)
  have hG : ∀ x : W, (G x : E) = F x := fun x => rfl
  have hsurj : Function.Surjective G := by
    rw [← LinearMap.injective_iff_surjective]
    intro x y hxy
    apply Subtype.ext
    apply injective_of_mul F c hc hM
    rw [← hG, ← hG, hxy]
  rw [Module.End.mem_invtSubmodule]
  intro v hv
  rw [Submodule.mem_comap, Submodule.mem_orthogonal]
  intro w hw
  obtain ⟨⟨w', hw'⟩, hw'eq⟩ := hsurj ⟨w, hw⟩
  have hFw' : F w' = w := by have := hG ⟨w', hw'⟩; rw [hw'eq] at this; exact this.symm
  rw [← hFw']
  have key := hM v w'
  have h0 : ⟪w', v⟫_ℂ = 0 := (Submodule.mem_orthogonal W v).1 hv w' hw'
  simp only [hForm] at key
  rw [h0, mul_zero] at key
  exact key

include hc hM in
/-- Generalized eigenspaces of `F` are eigenspaces. -/
theorem maxGenEigenspace_eq_eigenspace_of_mul [FiniteDimensional ℂ E] (α : ℂ) :
    F.maxGenEigenspace α = F.eigenspace α :=
  (isSemisimple_of_mul F c hc hM).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace α

end Multiplicative

section Weil

variable (F : Module.End ℂ E) (q j : ℝ) (hq : 0 < q)
  (hW : ∀ u v, hForm (F u) (F v) = ((q ^ j : ℝ) : ℂ) * hForm u v)
include hq hW

/-- **C-WEIL.** If `h(Fu, Fv) = q ^ j · h(u, v)` with `q > 0` and `h` positive definite, every
eigenvalue `α` of `F` satisfies `‖α‖ = q ^ (j / 2)`. -/
theorem norm_eq_rpow_of_weil {α : ℂ} (hα : Module.End.HasEigenvalue F α) :
    ‖α‖ = q ^ (j / 2) := by
  rw [norm_eq_of_hasEigenvalue_mul F (q ^ j) hW hα,
    Real.sqrt_eq_iff_mul_self_eq (Real.rpow_nonneg hq.le _) (Real.rpow_nonneg hq.le _),
    ← Real.rpow_add hq]
  ring_nf

/-- **C-WEIL, semisimplicity.** In finite dimension `F` is semisimple. -/
theorem isSemisimple_of_weil [FiniteDimensional ℂ E] : F.IsSemisimple :=
  isSemisimple_of_mul F (q ^ j) (Real.rpow_pos_of_pos hq j) hW

end Weil

end WeilRH
