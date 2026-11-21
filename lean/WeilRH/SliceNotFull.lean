import Mathlib

/-!
# Schemes over `𝒪_K` form a non-full subcategory (`prop:slice-not-full`)

`latex/notes.tex`, `prop:slice-not-full`. For a number field `K`, the forgetful functor from
schemes over `Spec 𝒪_K` to schemes is faithful; it is not full when `Aut(K) ≠ 1`; the automorphisms
of `Spec 𝒪_K` over itself are trivial, while its scheme automorphisms are exactly the `Spec σ` for
`σ ∈ Aut(K)`.

* `faithful`: `Over.forget (Spec 𝒪_K)` is faithful.
* `over_endo_eq_id`: every endomorphism of `Spec 𝒪_K` over `Spec 𝒪_K` (structure map the identity)
  is the identity; in particular its automorphism group over the base is trivial.
* `specAut`, `specAut_injective`, `exists_of_iso`: `σ ↦ Spec(σ|_{𝒪_K})` is injective on `Aut(K)`,
  and every scheme automorphism of `Spec 𝒪_K` is of this form. This is the bijection
  `Aut(K) ≅ Aut_{Sch}(Spec 𝒪_K)` of the source as a bijection of sets; `specAut` reverses
  composition, as `Spec` is contravariant, so as groups it is an anti-isomorphism, which does not
  change the group up to isomorphism.
* `not_full`: if some `σ ≠ id` exists, the forgetful functor is not full.

The proofs follow the source: `Spec` is fully faithful on rings, and a ring automorphism of `𝒪_K`
extends uniquely to `K = Frac 𝒪_K`.
-/

set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory NumberField

namespace WeilRH.SliceNotFull

variable (K : Type) [Field K] [NumberField K]

/-- `Spec 𝒪_K`. -/
noncomputable abbrev X : Scheme := Spec (CommRingCat.of (𝓞 K))

/-- `Spec 𝒪_K` as an object over itself. -/
noncomputable abbrev Xo : Over (X K) := Over.mk (𝟙 (X K))

/-- The scheme endomorphism `Spec σ` of `Spec 𝒪_K` induced by a field automorphism `σ`. -/
noncomputable def specAut (σ : K ≃+* K) : X K ⟶ X K :=
  Spec.map (CommRingCat.ofHom (RingOfIntegers.mapRingEquiv σ).toRingHom)

/-- The forgetful functor from schemes over `Spec 𝒪_K` is faithful. -/
theorem faithful : (Over.forget (X K)).Faithful := inferInstance

/-- **`prop:slice-not-full`.** Endomorphisms of `Spec 𝒪_K` over itself are trivial. -/
theorem over_endo_eq_id (f : Xo K ⟶ Xo K) : f = 𝟙 _ := by
  ext
  have := Over.w f
  simpa using this

/-- A field automorphism of `K` is determined by its restriction to `𝒪_K`. -/
theorem eq_of_restrict_eq (σ τ : K ≃+* K)
    (h : (RingOfIntegers.mapRingEquiv σ).toRingHom = (RingOfIntegers.mapRingEquiv τ).toRingHom) :
    σ = τ := by
  have : (σ : K →+* K) = τ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
    ext x
    have := congrArg (fun g : 𝓞 K →+* 𝓞 K => (g x : K)) h
    simpa using this
  exact RingEquiv.ext (fun x => congrArg (fun g : K →+* K => g x) this)

/-- Distinct field automorphisms give distinct scheme automorphisms of `Spec 𝒪_K`. -/
theorem specAut_injective : Function.Injective (specAut K) := by
  intro σ τ h
  apply eq_of_restrict_eq
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

/-- `Spec` of the identity. -/
theorem specAut_refl : specAut K (RingEquiv.refl K) = 𝟙 _ := by
  have : (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)).toRingHom = RingHom.id (𝓞 K) := by
    ext x; rfl
  simp only [specAut, this]
  exact Spec.map_id _

/-- **`prop:slice-not-full`.** If `Aut(K) ≠ 1`, the forgetful functor is not full. -/
theorem not_full (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K) : ¬ (Over.forget (X K)).Full := by
  intro hfull
  obtain ⟨f, hf⟩ := (Over.forget (X K)).map_surjective (X := Xo K) (Y := Xo K) (specAut K σ)
  rw [over_endo_eq_id K f] at hf
  apply hσ
  apply specAut_injective
  rw [specAut_refl, ← hf]
  simp

/-- **`prop:slice-not-full`.** Every scheme automorphism of `Spec 𝒪_K` is `Spec σ` for some
`σ ∈ Aut(K)`. -/
theorem exists_of_iso (g : X K ≅ X K) : ∃ σ : K ≃+* K, g.hom = specAut K σ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g.hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective g.inv
  have h1 : φ ≫ ψ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hφ, hψ, Spec.map_id]; exact g.inv_hom_id)
  have h2 : ψ ≫ φ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hφ, hψ, Spec.map_id]; exact g.hom_inv_id)
  let e : 𝓞 K ≃+* 𝓞 K :=
    { toFun := φ.hom, invFun := ψ.hom,
      left_inv := fun x => by
        have := congrArg (fun f => CommRingCat.Hom.hom f x) h1; simpa using this,
      right_inv := fun x => by
        have := congrArg (fun f => CommRingCat.Hom.hom f x) h2; simpa using this,
      map_mul' := φ.hom.map_mul, map_add' := φ.hom.map_add }
  refine ⟨IsFractionRing.ringEquivOfRingEquiv e, ?_⟩
  rw [← hφ, specAut]
  congr 1
  ext x
  simp [e, RingOfIntegers.mapRingEquiv, RingOfIntegers.mapRingHom,
]
  rfl

end WeilRH.SliceNotFull
