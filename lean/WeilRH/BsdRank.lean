/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.WeightedAlgebra

/-!
# The conditional rank-BSD argument and the Picard gap

Source: `latex/notes.tex`, `prop:bsd-spectral-rank` (conditional rank BSD, the finite-dimensional
form of Deninger 2010, p. 8 and Example 5, p. 10) and the algebraic part of `prop:bsd-picard-gap`.

## `prop:bsd-spectral-rank`

The hypotheses are encoded as follows.
* `L, g : ℂ → ℂ`, `L` meromorphic at `1`, `g` analytic and nonzero at `1`; `Λ_E = g · L`.
* The spectral block `V_{E,(1)}` is a finite-dimensional space `V` with an operator `Θ` such that
  `Θ - 1` is nilpotent (the generalized `1`-eigenspace is the whole block).
* The positive Hermitian form with `Θ + Θ* = 2` is a `PosHermForm` `h` on `V` with
  `h(Θu, v) + h(u, Θv) = 2 h(u, v)`.
* The exact order identity is `meromorphicOrderAt (g * L) 1 = dim V`.
* `E(K) ⊗_ℤ ℂ` is a complex vector space `M` and the arithmetic Abel–Jacobi isomorphism is a linear
  equivalence `M ≃ ker(Θ - 1)`; `rank E(K) = dim_ℂ M`.

The conclusion is `meromorphicOrderAt L 1 = dim_ℂ M`.

## `prop:bsd-picard-gap`, algebraic part

The geometric inputs are hypotheses: the degree map `deg : Pic(E) → ℤ`, its splitting
`n ↦ O_E(nO)`, the Abel–Jacobi identification `E(K) ≅ ker deg`, and "`c₁` records only the degree"
(`c₁` factors through `deg ⊗ R`). The algebra proved: `Pic(E) ≅ ℤ × ker deg`, and the kernel of
`c₁` contains `E(K) ⊗ R`, which injects into `Pic(E) ⊗ R`, for any commutative ring `R`
(the source's case is `R = ℚ_ℓ`).
-/

open Module

namespace WeilRH.BsdRank

/-! ### The spectral block -/

section Block

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On the generalized `1`-block, a positive form with `Θ + Θ* = 2` forces `Θ = 1`: `Θ - 1` is
nilpotent and skew-Hermitian, hence diagonalizable, hence zero. -/
theorem ker_sub_one_eq_top (h : PosHermForm V) (Θ : Module.End ℂ V)
    (hnil : IsNilpotent (Θ - 1))
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = ((2 : ℝ) : ℂ) * h.toFun u v) :
    LinearMap.ker (Θ - 1) = ⊤ := by
  have hgen : Θ.maxGenEigenspace 1 = ⊤ := by
    obtain ⟨n, hn⟩ := hnil
    refine eq_top_iff.2 fun v _ => (Θ.mem_maxGenEigenspace 1 v).2 ⟨n, ?_⟩
    rw [one_smul, hn, LinearMap.zero_apply]
  have h1 := h.maxGenEigenspace_eq_eigenspace Θ 2 hP 1
  rw [hgen, Module.End.eigenspace_def, one_smul] at h1
  exact h1.symm

/-- `dim V_{E,(1)} = dim ker(Θ - 1)` on the block. -/
theorem finrank_ker_eq (h : PosHermForm V) (Θ : Module.End ℂ V) (hnil : IsNilpotent (Θ - 1))
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = ((2 : ℝ) : ℂ) * h.toFun u v) :
    finrank ℂ (LinearMap.ker (Θ - 1)) = finrank ℂ V := by
  rw [ker_sub_one_eq_top h Θ hnil hP, finrank_top]

end Block

/-! ### `prop:bsd-spectral-rank` -/

/-- **`prop:bsd-spectral-rank` (conditional rank BSD).** Suppose `L` is meromorphic at `1`, `g` is
analytic and nonzero at `1`, the spectral block `V` (with `Θ - 1` nilpotent) carries a positive
Hermitian form with `Θ + Θ* = 2`, the order identity `ord_{s=1}(g L) = dim V` holds, and the
Abel–Jacobi map is an isomorphism `M ≅ ker(Θ - 1)` with `M = E(K) ⊗ ℂ`. Then
`ord_{s=1} L = dim M = rank E(K)`. -/
theorem bsd_spectral_rank {V M : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup M] [Module ℂ M]
    (L g : ℂ → ℂ) (hL : MeromorphicAt L 1) (hg : AnalyticAt ℂ g 1) (hg1 : g 1 ≠ 0)
    (h : PosHermForm V) (Θ : Module.End ℂ V) (hnil : IsNilpotent (Θ - 1))
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = ((2 : ℝ) : ℂ) * h.toFun u v)
    (horder : meromorphicOrderAt (g * L) 1 = ((finrank ℂ V : ℤ) : WithTop ℤ))
    (AJ : M ≃ₗ[ℂ] LinearMap.ker (Θ - 1)) :
    meromorphicOrderAt L 1 = ((finrank ℂ M : ℤ) : WithTop ℤ) := by
  have hg0 : meromorphicOrderAt g 1 = 0 := by
    rw [hg.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr hg1)]
    rfl
  rw [meromorphicOrderAt_mul hg.meromorphicAt hL, hg0, zero_add] at horder
  rw [horder, AJ.finrank_eq, finrank_ker_eq h Θ hnil hP]

/-! ### `prop:bsd-picard-gap`, algebraic part -/

section Picard

variable {P : Type*} [AddCommGroup P] (deg : P →ₗ[ℤ] ℤ) (s : ℤ →ₗ[ℤ] P)

/-- The splitting `p ↦ (deg p, p - s(deg p))` of `Pic(E)` by the degree and the section
`n ↦ O_E(nO)`. -/
def splitEquiv (hs : ∀ n, deg (s n) = n) : P ≃ₗ[ℤ] ℤ × LinearMap.ker deg where
  toFun p := (deg p, ⟨p - s (deg p), by simp [hs]⟩)
  invFun x := s x.1 + x.2
  left_inv p := by simp
  right_inv x := by
    obtain ⟨n, k, hk⟩ := x
    rw [LinearMap.mem_ker] at hk
    ext <;> simp [hs, hk]
  map_add' p q := by ext <;> simp; abel
  map_smul' c p := by
    ext
    · simp
    · simp only [map_smul, smul_eq_mul, RingHom.id_apply, Prod.smul_snd, SetLike.mk_smul_mk]
      rw [smul_sub, ← smul_eq_mul, map_smul]

/-- The retraction `p ↦ p - s(deg p)` onto `ker deg`. -/
def retract (hs : ∀ n, deg (s n) = n) : P →ₗ[ℤ] LinearMap.ker deg :=
  (LinearMap.snd ℤ ℤ (LinearMap.ker deg)).comp (splitEquiv deg s hs).toLinearMap

theorem retract_comp_subtype (hs : ∀ n, deg (s n) = n) :
    (retract deg s hs).comp (LinearMap.ker deg).subtype = LinearMap.id := by
  ext ⟨k, hk⟩
  rw [LinearMap.mem_ker] at hk
  simp [retract, splitEquiv, hk]

variable (R : Type*) [CommRing R]

/-- `ker deg ⊗ R → Pic(E) ⊗ R` is injective: the inclusion is split. -/
theorem baseChange_subtype_injective (hs : ∀ n, deg (s n) = n) :
    Function.Injective ((LinearMap.ker deg).subtype.baseChange R) := by
  have h : ((retract deg s hs).baseChange R).comp ((LinearMap.ker deg).subtype.baseChange R) =
      LinearMap.id := by
    rw [← LinearMap.baseChange_comp, retract_comp_subtype, LinearMap.baseChange_id]
  exact Function.LeftInverse.injective (g := (retract deg s hs).baseChange R)
    fun x => by simpa using LinearMap.congr_fun h x

/-- **`prop:bsd-picard-gap`, algebraic part.** Let `E(K) ≅ ker deg` (Abel–Jacobi) and let
`c₁ : Pic(E) ⊗ R → A` record only the degree, `c₁ = φ ∘ (deg ⊗ R)`. Then `E(K) ⊗ R` injects into
`Pic(E) ⊗ R` and lies in the kernel of `c₁`. -/
theorem picard_gap {G A : Type*} [AddCommGroup G] [AddCommGroup A] [Module R A]
    (hs : ∀ n, deg (s n) = n) (AJ : G ≃ₗ[ℤ] LinearMap.ker deg)
    (c₁ : TensorProduct ℤ R P →ₗ[R] A) (φ : TensorProduct ℤ R ℤ →ₗ[R] A)
    (hc : c₁ = φ ∘ₗ deg.baseChange R) :
    Function.Injective (((LinearMap.ker deg).subtype ∘ₗ AJ.toLinearMap).baseChange R) ∧
      LinearMap.range (((LinearMap.ker deg).subtype ∘ₗ AJ.toLinearMap).baseChange R) ≤
        LinearMap.ker c₁ := by
  rw [LinearMap.baseChange_comp]
  refine ⟨(baseChange_subtype_injective deg s R hs).comp
    (LinearEquiv.baseChange ℤ R G (LinearMap.ker deg) AJ).injective, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hc, LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply
      (deg.baseChange R), ← LinearMap.baseChange_comp]
    have : deg ∘ₗ (LinearMap.ker deg).subtype = 0 := by
      ext ⟨k, hk⟩; exact hk
    rw [this, LinearMap.baseChange_zero, LinearMap.zero_apply, map_zero]

end Picard

end WeilRH.BsdRank
