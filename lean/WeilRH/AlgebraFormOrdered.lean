/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.AlgebraForm

/-!
# The algebra form over `ℚ` and `ℝ`: separability (`prop:algebra-form` (i), first half)

`latex/notes.tex`, `def:pos-involution` and `prop:algebra-form` (i), for `k ∈ {ℚ, ℝ}`. The `k = ℂ`
case is `WeilRH.AlgebraForm` (round 3 and round 39).

## Design

For `k ≠ ℂ` the definition asks for a `k`-linear trace `τ : A → k` and a `k`-linear anti-involution
`†` with `τ(a a†) > 0` for `a ≠ 0`. We state this over any linearly ordered field `K`, which covers
`K = ℚ` and `K = ℝ` at once (`PositiveTraceOrd`).

## Main results

* `isSemisimple_of_similitude`: over any field, an endomorphism that scales an anisotropic
  bilinear form by a nonzero constant is semisimple. The invariant complement of an invariant
  subspace `W` is its orthogonal `{v | B(v, W) = 0}`.
* `PositiveTraceOrd.symForm_mulLeft`: if `g g† = c` with `c ≠ 0`, the symmetrized form
  `S(a, b) = τ(a b†) + τ(b a†)` satisfies `S(g a, g b) = c S(a, b)`, and `S(a, a) > 0` for `a ≠ 0`.
* `PositiveTraceOrd.minpoly_separable` (**`prop:algebra-form` (i), separability over `k`**): the
  minimal polynomial of `g` over `K` is separable.

## Not formalized here

The second half of (i) for `k ∈ {ℚ, ℝ}` (every complex root of the minimal polynomial has modulus
`q^{j/2}`) and (ii) for `k ∈ {ℚ, ℝ}` both go through `A ⊗_k ℂ`. Mathlib has no lemma that the
minimal polynomial of an endomorphism is unchanged by field extension, and the positivity of the
extended Hermitian form needs `ℚ`-positivity to pass to `ℝ`. Both remain open (README obligation 22).
-/

open Polynomial

namespace WeilRH

section Similitude

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over any field, an endomorphism `f` with `B (f a) (f b) = c * B a b` (`c ≠ 0`) for an
anisotropic bilinear form `B` is semisimple: the left orthogonal of an `f`-invariant subspace is an
`f`-invariant complement. -/
theorem isSemisimple_of_similitude (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ v, B v v = 0 → v = 0)
    (f : Module.End K V) {c : K} (hc : c ≠ 0) (hf : ∀ a b, B (f a) (f b) = c * B a b) :
    f.IsSemisimple := by
  rw [Module.End.isSemisimple_iff]
  intro p hp
  rw [Module.End.mem_invtSubmodule] at hp
  set φ : V →ₗ[K] p →ₗ[K] K := B.compl₂ p.subtype
  refine ⟨LinearMap.ker φ, ?_, ?_⟩
  · -- invariance of the orthogonal
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      apply hB
      have h := hf v v
      rw [LinearMap.mem_ker.1 hv, map_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hc
    have hres : Function.Surjective (f.restrict hp) := by
      have : Function.Injective (f.restrict hp) := by
        intro x y hxy
        apply Subtype.ext
        exact hinj (congrArg Subtype.val hxy)
      exact LinearMap.injective_iff_surjective.1 this
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    ext w
    obtain ⟨w', hw'⟩ := hres w
    have hw : (w : V) = f w' := by rw [← hw']; rfl
    simp only [φ, LinearMap.compl₂_apply, Submodule.subtype_apply, LinearMap.zero_apply]
    rw [hw, hf]
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hv) w'
    simp only [φ, LinearMap.compl₂_apply, Submodule.subtype_apply, LinearMap.zero_apply] at this
    rw [this, mul_zero]
  · -- complement
    have hdis : Disjoint p (LinearMap.ker φ) := by
      rw [Submodule.disjoint_def]
      intro v hvp hvq
      apply hB
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 hvq) ⟨v, hvp⟩
      simpa [φ] using this
    refine ⟨hdis, ?_⟩
    rw [codisjoint_iff]
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank K (LinearMap.range φ) ≤ Module.finrank K p := by
      calc Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (p →ₗ[K] K) :=
            Submodule.finrank_le _
        _ = Module.finrank K p := Subspace.dual_finrank_eq
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq p (LinearMap.ker φ)
    rw [disjoint_iff.1 hdis, finrank_bot] at h3
    have h4 := Submodule.finrank_le (p ⊔ LinearMap.ker φ)
    omega

end Similitude

/-- A **positive trace involution** over an ordered field `K` (`def:pos-involution`, `k ≠ ℂ`):
a `K`-linear trace `τ` and a `K`-linear anti-involution `†` with `τ(a a†) > 0` for `a ≠ 0`. -/
structure PositiveTraceOrd (K A : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Ring A] [Algebra K A] where
  /-- The trace functional `τ`. -/
  τ : A →ₗ[K] K
  /-- `τ(ab) = τ(ba)`. -/
  τ_comm : ∀ a b, τ (a * b) = τ (b * a)
  /-- The involution `†`, `K`-linear. -/
  dag : A →ₗ[K] A
  /-- `(ab)† = b† a†`. -/
  dag_mul : ∀ a b, dag (a * b) = dag b * dag a
  /-- `a†† = a`. -/
  dag_dag : ∀ a, dag (dag a) = a
  /-- Positivity: `τ(a a†) > 0` for `a ≠ 0`. -/
  τ_pos : ∀ a, a ≠ 0 → 0 < τ (a * dag a)

namespace PositiveTraceOrd

variable {K A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Ring A] [Algebra K A]
  (P : PositiveTraceOrd K A)

/-- The symmetrized form `S(a, b) = τ(a b†) + τ(b a†)` of the proof of `prop:algebra-form` (i)
(the source uses half of it). -/
def symForm : A →ₗ[K] A →ₗ[K] K :=
  LinearMap.mk₂ K (fun a b => P.τ (a * P.dag b) + P.τ (b * P.dag a))
    (fun a a' b => by simp [add_mul, mul_add, map_add]; ring)
    (fun c a b => by simp [map_smul]; ring)
    (fun a b b' => by simp [mul_add, add_mul, map_add]; ring)
    (fun c a b => by simp [map_smul]; ring)

theorem symForm_apply (a b : A) : P.symForm a b = P.τ (a * P.dag b) + P.τ (b * P.dag a) := rfl

/-- `S(a, a) = 2 τ(a a†) > 0` for `a ≠ 0`. -/
theorem symForm_self_pos {a : A} (ha : a ≠ 0) : 0 < P.symForm a a := by
  rw [symForm_apply]
  have := P.τ_pos a ha
  linarith

/-- In finite dimension, `g g† = c` with `c ≠ 0` forces `g† g = c`. -/
theorem dag_mul_self_eq [FiniteDimensional K A] {g : A} {c : K} (hc : c ≠ 0)
    (hg : g * P.dag g = c • (1 : A)) : P.dag g * g = c • (1 : A) := by
  have h1 : Algebra.lmul K A g * Algebra.lmul K A (c⁻¹ • P.dag g) = 1 := by
    rw [← map_mul, mul_smul_comm, hg, smul_smul, inv_mul_cancel₀ hc, one_smul, map_one]
  have h2 := (mul_eq_one_comm (M := Module.End K A)).1 h1
  rw [← map_mul] at h2
  have h3 : c⁻¹ • (P.dag g * g) = 1 := by
    have := congrArg (fun f : Module.End K A => f 1) h2
    simpa [Algebra.coe_lmul_eq_mul, smul_mul_assoc] using this
  calc P.dag g * g = c • (c⁻¹ • (P.dag g * g)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • (1 : A) := by rw [h3]

/-- **Similitude.** If `g g† = c` (`c ≠ 0`) then `S(g a, g b) = c S(a, b)`. -/
theorem symForm_mulLeft [FiniteDimensional K A] {g : A} {c : K} (hc : c ≠ 0)
    (hg : g * P.dag g = c • (1 : A)) (a b : A) :
    P.symForm (g * a) (g * b) = c * P.symForm a b := by
  have h' := P.dag_mul_self_eq hc hg
  have key : ∀ x y : A, P.τ (g * x * P.dag (g * y)) = c * P.τ (x * P.dag y) := by
    intro x y
    rw [P.dag_mul, mul_assoc, P.τ_comm, mul_assoc, mul_assoc, h', mul_smul_comm, mul_one,
      mul_smul_comm, map_smul, smul_eq_mul]
  simp only [symForm_apply]
  rw [key, key, mul_add]

/-- **`prop:algebra-form` (i), separability, for `k ∈ {ℚ, ℝ}`.** If `g g† = c` with `c ≠ 0`
(in the source `c = q^j`), the minimal polynomial of `g` over `K` is separable. -/
theorem minpoly_separable [FiniteDimensional K A] {g : A} {c : K} (hc : c ≠ 0)
    (hg : g * P.dag g = c • (1 : A)) : (minpoly K g).Separable := by
  have hs : (Algebra.lmul K A g).IsSemisimple := by
    refine isSemisimple_of_similitude P.symForm (fun v hv => ?_) _ hc ?_
    · by_contra hne
      exact (P.symForm_self_pos hne).ne' hv
    · intro a b
      simpa [Algebra.coe_lmul_eq_mul] using P.symForm_mulLeft hc hg a b
  have hsq := hs.minpoly_squarefree
  have hmin : minpoly K (Algebra.lmul K A g) = minpoly K g := by
    refine minpoly.algHom_eq _ (fun x y hxy => ?_) g
    simpa [Algebra.coe_lmul_eq_mul] using congrArg (fun f : Module.End K A => f 1) hxy
  rw [hmin] at hsq
  exact PerfectField.separable_iff_squarefree.2 hsq

end PositiveTraceOrd

/-- Nonvacuity: `K` itself, with `τ = id` and `† = id`, is a positive trace involution. -/
def PositiveTraceOrd.self (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    PositiveTraceOrd K K where
  τ := LinearMap.id
  τ_comm a b := by simp [mul_comm]
  dag := LinearMap.id
  dag_mul a b := by simp [mul_comm]
  dag_dag _ := rfl
  τ_pos a ha := by simpa using mul_self_pos.2 ha

end WeilRH
