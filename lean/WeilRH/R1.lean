/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# `prop:R1`: indefinite forms satisfying the infinitesimal polarization identity

Source: `latex/notes.tex`, `def:R1-forms` and `prop:R1` (claim R1). On `V = ℂ²` with standard
basis `e₁, e₂` (indices `0, 1`) and `j ∈ ℝ`:

* the *dual pair* `Θ^dual_ρ = diag(ρ, j - ρ̄)` with `h^dual(u, v) = u₁ v̄₂ + u₂ v̄₁`;
* the *split pair* `Θ^split = diag(j/2 + iτ₁, j/2 + iτ₂)` (`τ₁ ≠ τ₂` real) with
  `h^split(u, v) = u₁ v̄₁ - u₂ v̄₂`.

`prop:R1` (i): `h^dual` is a nondegenerate Hermitian form satisfying `eq:inf-pol`
`h(Θu, v) + h(u, Θv) = j h(u, v)` for `Θ^dual_ρ`, and `ρ` is an eigenvalue, for *every* `ρ ∈ ℂ`
(so `Re ρ ≠ j/2` is possible). (ii): `h^split` is a nondegenerate Hermitian form satisfying
`eq:inf-pol` for `Θ^split`, positive definite on the eigenline `ker(Θ^split - j/2 - iτ₁)`, and
`h^split(e₂, e₂) = -1`.

Conventions: forms are functions `(Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ`, linear in the first argument;
`Θ` acts by `Matrix.mulVec`.
-/

open Matrix Complex
open scoped ComplexConjugate

namespace WeilRH.R1

variable (j : ℝ)

/-- `Θ^dual_ρ = diag(ρ, j - ρ̄)`. -/
noncomputable def thetaDual (ρ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![ρ, j - conj ρ]

/-- `h^dual(u, v) = u₁ v̄₂ + u₂ v̄₁`. -/
def hDual (u v : Fin 2 → ℂ) : ℂ := u 0 * conj (v 1) + u 1 * conj (v 0)

/-- `Θ^split = diag(j/2 + iτ₁, j/2 + iτ₂)`. -/
noncomputable def thetaSplit (τ₁ τ₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![(j / 2 : ℝ) + τ₁ * I, (j / 2 : ℝ) + τ₂ * I]

/-- `h^split(u, v) = u₁ v̄₁ - u₂ v̄₂`. -/
def hSplit (u v : Fin 2 → ℂ) : ℂ := u 0 * conj (v 0) - u 1 * conj (v 1)

/-- A form `h` is Hermitian and nondegenerate. -/
def IsHermNondeg (h : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ) : Prop :=
  (∀ u v, conj (h u v) = h v u) ∧ ∀ u, (∀ v, h u v = 0) → u = 0

/-- Identity `eq:inf-pol` of weight `j` for `Θ`. -/
def InfPol (h : (Fin 2 → ℂ) → (Fin 2 → ℂ) → ℂ) (Θ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ u v, h (Θ *ᵥ u) v + h u (Θ *ᵥ v) = (j : ℂ) * h u v

lemma hDual_isHermNondeg : IsHermNondeg hDual := by
  refine ⟨fun u v => by simp [hDual]; ring, fun u hu => ?_⟩
  have h0 := hu ![0, 1]
  have h1 := hu ![1, 0]
  simp [hDual] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

lemma hSplit_isHermNondeg : IsHermNondeg hSplit := by
  refine ⟨fun u v => by simp [hSplit]; ring, fun u hu => ?_⟩
  have h0 := hu ![1, 0]
  have h1 := hu ![0, 1]
  simp [hSplit] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

lemma infPol_dual (ρ : ℂ) : InfPol j hDual (thetaDual j ρ) := by
  intro u v
  simp only [hDual, thetaDual, mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_mul, map_sub, Complex.conj_ofReal, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

lemma infPol_split (τ₁ τ₂ : ℝ) : InfPol j hSplit (thetaSplit j τ₁ τ₂) := by
  intro u v
  simp only [hSplit, thetaSplit, mulVec_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `ρ` is an eigenvalue of `Θ^dual_ρ`, with eigenvector `e₁`. -/
lemma hasEigenvalue_dual (ρ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' (thetaDual j ρ)) ρ := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0]) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i; fin_cases i <;> simp [thetaDual]
  · intro h; simpa using congrFun h 0

/-- **`prop:R1` (i).** For every `ρ ∈ ℂ`: `h^dual` is Hermitian, nondegenerate, satisfies
`eq:inf-pol` for `Θ^dual_ρ`, and `ρ` is an eigenvalue of `Θ^dual_ρ`. -/
theorem dual (ρ : ℂ) :
    IsHermNondeg hDual ∧ InfPol j hDual (thetaDual j ρ) ∧
      Module.End.HasEigenvalue (Matrix.toLin' (thetaDual j ρ)) ρ :=
  ⟨hDual_isHermNondeg, infPol_dual j ρ, hasEigenvalue_dual j ρ⟩

/-- In `prop:R1` (i) `Re ρ ≠ j/2` is possible: take `ρ = j/2 + 1`. -/
theorem dual_off_line :
    ∃ ρ : ℂ, ρ.re ≠ j / 2 ∧ IsHermNondeg hDual ∧ InfPol j hDual (thetaDual j ρ) ∧
      Module.End.HasEigenvalue (Matrix.toLin' (thetaDual j ρ)) ρ :=
  ⟨((j / 2 + 1 : ℝ) : ℂ), by simp, dual j _⟩

/-- The eigenline `ker(Θ^split - j/2 - iτ₁)` is `ℂ e₁` when `τ₁ ≠ τ₂`. -/
lemma mem_ker_split_iff {τ₁ τ₂ : ℝ} (hτ : τ₁ ≠ τ₂) (v : Fin 2 → ℂ) :
    thetaSplit j τ₁ τ₂ *ᵥ v = ((j / 2 : ℝ) + τ₁ * I) • v ↔ v 1 = 0 := by
  constructor
  · intro h
    have h1 := congrFun h 1
    simp only [thetaSplit, mulVec_diagonal, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.smul_apply, smul_eq_mul] at h1
    have : ((τ₂ : ℂ) - τ₁) * I * v 1 = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd (by exact_mod_cast (sub_eq_zero.1 h).symm) hτ
      · exact absurd h I_ne_zero
    · exact h
  · intro h
    ext i; fin_cases i <;> simp [thetaSplit, h]

/-- **`prop:R1` (ii).** For real `τ₁ ≠ τ₂`: `h^split` is Hermitian, nondegenerate, satisfies
`eq:inf-pol` for `Θ^split`, is positive definite on the eigenline
`ker(Θ^split - j/2 - iτ₁)`, and `h^split(e₂, e₂) = -1`. -/
theorem split {τ₁ τ₂ : ℝ} (hτ : τ₁ ≠ τ₂) :
    IsHermNondeg hSplit ∧ InfPol j hSplit (thetaSplit j τ₁ τ₂) ∧
      (∀ v : Fin 2 → ℂ, thetaSplit j τ₁ τ₂ *ᵥ v = ((j / 2 : ℝ) + τ₁ * I) • v → v ≠ 0 →
        0 < (hSplit v v).re) ∧
      hSplit ![0, 1] ![0, 1] = -1 := by
  refine ⟨hSplit_isHermNondeg, infPol_split j τ₁ τ₂, fun v hv hv0 => ?_, by simp [hSplit]⟩
  have h1 := (mem_ker_split_iff j hτ v).1 hv
  have h0 : v 0 ≠ 0 := by
    intro h0; apply hv0; ext i; fin_cases i <;> simp [h0, h1]
  simp only [hSplit, h1, zero_mul, sub_zero, Complex.mul_conj]
  exact_mod_cast Complex.normSq_pos.2 h0

end WeilRH.R1
