/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.AW5Contains

/-!
# The Hilbert completion of a polarized spectral core (`prop:hilbert`, first part)

`prop:hilbert` takes a spectral core `(V, Θ)` with a positive infinitesimal polarization `h` of
weight `j`, and the Hilbert-space completion `𝓗` of `(V, h)`. It asserts an orthonormal basis
`(e_k)` of `𝓗` contained in `V` with `Θ e_k = (j/2 + i τ_k) e_k`, `τ_k ∈ ℝ`, and that the diagonal
operator `T = diag(τ_k)` is self-adjoint, satisfies `Θ = j/2 + iT` on `V`, and has pure point
spectrum `{τ_k}` with finite multiplicities and no finite accumulation.

## Main results

* `Hilbert.Completion h`: the completion of `(V, ⟪u, v⟫ = h(v, u))`, a complex Hilbert space.
* `Hilbert.inner_eq_zero_of_ne`: distinct eigenspaces are `h`-orthogonal.
* `Hilbert.exists_hilbertBasis`: **`prop:hilbert`, the basis clause.** There is a Hilbert basis of
  `𝓗` whose vectors are the images of eigenvectors `e_k ∈ V` with `Θ e_k = (j/2 + i τ_k) e_k`.
* `Hilbert.T`, `Hilbert.theta_eq`, `Hilbert.T_symm`: `T = -i(Θ - j/2)` on `V`, so `Θ = j/2 + iT` on
  `V`, and `T` is symmetric for `h`.

Self-adjointness of the closure of `T` on `𝓗` and the spectral statement are not formalized
(obligation 18).
-/

open Module Complex WeilRH.AW4Forms
open scoped ComplexConjugate

namespace WeilRH.Hilbert

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The Hilbert-space completion `𝓗` of `(V, h)` (`prop:hilbert`). -/
abbrev Completion (h : PosHermForm V) : Type u := UniformSpace.Completion (HSpace h)

/-- Distinct eigenspaces of `Θ` are `h`-orthogonal when `h` is a positive infinitesimal
polarization of weight `j` on a spectral core. -/
theorem inner_eq_zero_of_ne {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hpol : Suspension.IsInfPol h Θ j) {ρ σ : ℂ} (hne : ρ ≠ σ)
    {u v : V} (hu : u ∈ Θ.eigenspace ρ) (hv : v ∈ Θ.eigenspace σ) : h.toFun u v = 0 := by
  have hE := aw4E_of_aw4V hS ⟨h, hpol⟩
  have hu' := Module.End.mem_eigenspace_iff.1 hu
  have hv' := Module.End.mem_eigenspace_iff.1 hv
  have e := hpol u v
  rw [hu', hv', h.smul_left, h.smul_right] at e
  by_cases hu0 : u = 0
  · subst hu0; simpa using h.smul_left 0 0 v
  by_cases hv0 : v = 0
  · subst hv0; simpa using h.smul_right 0 u 0
  have hρ : ρ.re = j / 2 := re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hu, hu0⟩)
  have hσ : σ.re = j / 2 := re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
  have hc : ρ + (starRingEnd ℂ) σ - (j : ℂ) ≠ 0 := by
    intro h0
    apply hne
    have him := congrArg Complex.im h0
    simp at him
    apply Complex.ext
    · rw [hρ, hσ]
    · linarith
  have : (ρ + (starRingEnd ℂ) σ - (j : ℂ)) * h.toFun u v = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_left hc

/-- **`prop:hilbert`, the basis clause.** If `(V, Θ)` is a spectral core and `h` a positive
infinitesimal polarization of weight `j`, the completion `𝓗` of `(V, h)` has a Hilbert basis
`(b_k)` with `b_k` the image of some `e_k ∈ V` satisfying `Θ e_k = (j/2 + i τ_k) e_k`, `τ_k ∈ ℝ`. -/
theorem exists_hilbertBasis {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hpol : Suspension.IsInfPol h Θ j) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ),
      (∀ k, b k = ((show HSpace h from e k : HSpace h) : Completion h)) ∧
      ∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k := by
  have hE := aw4E_of_aw4V hS ⟨h, hpol⟩
  let Θ' : Module.End ℂ (HSpace h) := Θ
  let E : ℂ → Submodule ℂ (HSpace h) := fun ρ => Θ'.eigenspace ρ
  have hfd : ∀ ρ, FiniteDimensional ℂ (E ρ) := fun ρ =>
    haveI : FiniteDimensional ℂ (Θ'.maxGenEigenspace ρ) := hS.finiteDimensional ρ
    Submodule.finiteDimensional_of_le (S₂ := Θ'.maxGenEigenspace ρ)
      (fun x hx => Θ'.eigenspace_le_maxGenEigenspace hx)
  let n : ℂ → ℕ := fun ρ => finrank ℂ (E ρ)
  let ob : ∀ ρ, OrthonormalBasis (Fin (n ρ)) ℂ (E ρ) := fun ρ =>
    haveI := hfd ρ; stdOrthonormalBasis ℂ (E ρ)
  let ι : Type u := ULift.{u} (Σ ρ : ℂ, Fin (n ρ))
  let v : ι → HSpace h := fun k => (ob k.down.1 k.down.2 : HSpace h)
  have hmem : ∀ k : ι, v k ∈ E k.down.1 := fun k => (ob k.down.1 k.down.2).2
  -- orthonormality in `HSpace h`
  have horth : OrthogonalFamily ℂ (fun ρ => E ρ) fun ρ => (E ρ).subtypeₗᵢ := by
    rw [orthogonalFamily_iff_pairwise]
    intro ρ σ hne
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    rw [HSpace.inner_eq]
    exact inner_eq_zero_of_ne hS hpol (Ne.symm hne) hy hx
  have hon' : Orthonormal ℂ (fun k : Σ ρ : ℂ, Fin (n ρ) => (ob k.1 k.2 : HSpace h)) :=
    horth.orthonormal_sigma_orthonormal fun ρ => (ob ρ).orthonormal
  have hon : Orthonormal ℂ v := hon'.comp _ Equiv.ulift.injective
  -- the family spans `V`
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (AW4Forms.iSup_eigenspace_eq_top hE : ⨆ ρ, Θ'.eigenspace ρ = ⊤), iSup_le_iff]
    intro ρ x hx
    have hx' : (⟨x, hx⟩ : E ρ) ∈ Submodule.span ℂ (Set.range (ob ρ)) := by
      simpa using (ob ρ).toBasis.mem_span (⟨x, hx⟩ : E ρ)
    have := Submodule.apply_mem_span_image_iff_mem_span (f := (E ρ).subtype)
      Subtype.val_injective |>.2 hx'
    refine Submodule.span_mono ?_ (by simpa [← Set.range_comp] using this)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨⟨ρ, i⟩⟩, rfl⟩
  let c : HSpace h →ₗᵢ[ℂ] Completion h := UniformSpace.Completion.toComplₗᵢ
  have hcon : Orthonormal ℂ (c ∘ v) := hon.comp_linearIsometry c
  have hdense : ⊤ ≤ (Submodule.span ℂ (Set.range (c ∘ v))).topologicalClosure := by
    have hcoe : (⇑c : HSpace h → Completion h) = ⇑c.toLinearMap := rfl
    rw [Set.range_comp, hcoe, Submodule.span_image c.toLinearMap, hspan, Submodule.map_top,
      top_le_iff, ← Submodule.dense_iff_topologicalClosure_eq_top]
    have hd : DenseRange ((↑) : HSpace h → Completion h) := UniformSpace.Completion.denseRange_coe
    simpa [c, LinearMap.coe_range, DenseRange] using hd
  refine ⟨ι, HilbertBasis.mk hcon hdense, fun k => v k, fun k => (k.down.1).im, ?_, ?_⟩
  · intro k; simp [HilbertBasis.coe_mk, c]
  · intro k
    have hk := Module.End.mem_eigenspace_iff.1 (hmem k)
    have hne : v k ≠ 0 := hon.ne_zero k
    have hre : (k.down.1).re = j / 2 :=
      re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem k, hne⟩)
    have : k.down.1 = (j / 2 : ℂ) + I * ((k.down.1).im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [← this]; exact hk

/-- The operator `T = -i(Θ - j/2)` on `V`, so that `Θ = j/2 + iT` (`prop:hilbert`). -/
noncomputable def T (Θ : Module.End ℂ V) (j : ℝ) : Module.End ℂ V :=
  (-I) • (Θ - ((j / 2 : ℝ) : ℂ) • 1)

/-- `Θ = j/2 + iT` on `V` (`prop:hilbert`). -/
theorem theta_eq (Θ : Module.End ℂ V) (j : ℝ) : Θ = ((j / 2 : ℝ) : ℂ) • 1 + I • T Θ j := by
  ext x
  have hI : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  simp only [T, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, smul_smul, hI, one_smul]
  abel

/-- `T` acts on `e_k` by the real number `τ_k`: if `Θ e = (j/2 + iτ) e` then `T e = τ e`. -/
theorem T_apply_of_eq {Θ : Module.End ℂ V} {j τ : ℝ} {e : V}
    (he : Θ e = ((j / 2 : ℂ) + I * (τ : ℂ)) • e) : T Θ j e = (τ : ℂ) • e := by
  simp only [T, LinearMap.smul_apply, LinearMap.sub_apply, he, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [← sub_smul, smul_smul]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- **`prop:hilbert`, symmetry.** `T` is symmetric for `h`: `h(Tu, v) = h(u, Tv)`. -/
theorem T_symm {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hpol : Suspension.IsInfPol h Θ j) (u v : V) :
    h.toFun (T Θ j u) v = h.toFun u (T Θ j v) := by
  have e := hpol u v
  simp only [T, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply]
  rw [h.smul_left, h.smul_right, sub_eq_add_neg, sub_eq_add_neg, h.add_left, h.add_right,
    ← neg_smul, ← neg_smul, h.smul_left, h.smul_right]
  simp only [map_neg, conj_I, neg_neg, Complex.conj_ofReal]
  linear_combination (norm := (push_cast; ring)) (-I) * e

end WeilRH.Hilbert
