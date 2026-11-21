/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ZetaZerosRvM
import WeilRH.Multiplicities

/-!
# `prop:kun-over-Z` (round 74)

Source: `latex/notes.tex`, Proposition `prop:kun-over-Z`. For a Weil datum of type `(1, 0)` on
`X̄_ℚ` satisfying AW1 for `U = 𝟙` and AW2 for `(Λ, 𝟙)`, there is no isomorphism of flow modules
between `V¹` and the degree-one part `V⁰ ⊗ V¹ ⊕ V¹ ⊗ V⁰` of its tensor square.

## Encoding

* The degree-one datum is `ArithmeticWeilCohomologyQMult` (AW1 local finiteness, finite
  eigenspaces, `dim V¹_{Θ=ρ} = ord_ρ ξ`), as in `prop:converse`.
* AW1 gives `V⁰ = ℂ` with `Θ₀ = 0`, so the degree-one part of the tensor square is `V¹ ⊕ V¹`
  with `Θ ⊕ Θ` (the manuscript's first step); we state the conclusion for `V¹ × V¹` directly.
  The identification `V⁰ ⊗ V¹ ≅ V¹` is not re-derived here.
* The existence of a zero of `ξ` uses the black box B6 (`RiemannVonMangoldt`), as an explicit
  hypothesis; the manuscript takes it from the proof of `prop:P1Z`.
-/

namespace WeilRH.KunOverZ

open Module

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `φ : V ≃ V × V` intertwines `Θ` with `Θ ⊕ Θ`, every eigenspace of `Θ` with finite
dimension is zero. -/
lemma finrank_eigenspace_eq_zero (Θ : Module.End ℂ V) (φ : V ≃ₗ[ℂ] V × V)
    (hφ : ∀ v, φ (Θ v) = (Θ.prodMap Θ) (φ v)) (ρ : ℂ)
    [FiniteDimensional ℂ (Θ.eigenspace ρ)] : finrank ℂ (Θ.eigenspace ρ) = 0 := by
  set E := Θ.eigenspace ρ
  set P : Module.End ℂ (V × V) := Θ.prodMap Θ
  set Ep := P.eigenspace ρ
  have hsymm : ∀ w, φ.symm (P w) = Θ (φ.symm w) := fun w => by
    apply φ.injective; rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
  -- `φ⁻¹` maps `Ep` injectively into `E`
  let α : Ep →ₗ[ℂ] E := ((φ.symm : V × V →ₗ[ℂ] V).comp Ep.subtype).codRestrict E (fun w => by
    have hw := Module.End.mem_eigenspace_iff.1 w.2
    exact Module.End.mem_eigenspace_iff.2 (by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
      rw [← hsymm, hw, map_smul]))
  have hα : Function.Injective α := fun x y hxy => by
    apply Subtype.ext; apply φ.symm.injective
    exact congrArg Subtype.val hxy
  have hfin : FiniteDimensional ℂ Ep := Module.Finite.of_injective α hα
  have h1 : finrank ℂ Ep ≤ finrank ℂ E := LinearMap.finrank_le_finrank_of_injective hα
  -- `E × E` embeds in `Ep`
  let β : (E × E) →ₗ[ℂ] Ep := (E.subtype.prodMap E.subtype).codRestrict Ep (fun x => by
    refine Module.End.mem_eigenspace_iff.2 ?_
    have h₁ := Module.End.mem_eigenspace_iff.1 x.1.2
    have h₂ := Module.End.mem_eigenspace_iff.1 x.2.2
    simp only [LinearMap.prodMap_apply, Submodule.subtype_apply, P, Prod.smul_mk, h₁, h₂])
  have hβ : Function.Injective β := fun x y hxy => by
    have := congrArg Subtype.val hxy
    simp only [β, LinearMap.codRestrict_apply, LinearMap.prodMap_apply, Prod.mk.injEq] at this
    exact Prod.ext (Subtype.ext this.1) (Subtype.ext this.2)
  have h2 : finrank ℂ (E × E) ≤ finrank ℂ Ep := LinearMap.finrank_le_finrank_of_injective hβ
  rw [Module.finrank_prod] at h2
  omega

/-- **`prop:kun-over-Z`** (conditional on B6). For the degree-one datum of an arithmetic Weil
cohomology on `X̄_ℚ` with multiplicities, there is no isomorphism of flow modules
`V¹ ≅ V¹ ⊕ V¹` (the degree-one part of the tensor square, using `V⁰ = ℂ`, `Θ₀ = 0`). -/
theorem kun_over_Z (hB : RiemannVonMangoldt) (H : ArithmeticWeilCohomologyQMult) :
    ¬ ∃ φ : H.V ≃ₗ[ℂ] H.V × H.V, ∀ v, φ (H.Θ v) = (H.Θ.prodMap H.Θ) (φ v) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨ρ, h0, h1, h2⟩ := RvM.exists_nontrivial_zero hB
  have hnt : IsNontrivialZetaZero ρ := by
    refine ⟨h0, ?_, ?_⟩
    · rintro ⟨n, rfl⟩
      simp at h1
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · rintro rfl; simp at h2
  have hpos := (analyticOrderNatAt_completedXi_pos_iff ρ).2 hnt
  have := H.finiteDimensional_eigenspace ρ
  have hz := finrank_eigenspace_eq_zero H.Θ φ hφ ρ
  rw [H.finrank_eigenspace ρ] at hz
  omega

end WeilRH.KunOverZ
