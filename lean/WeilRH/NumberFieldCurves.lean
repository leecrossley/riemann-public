import WeilRH.CompactifiedScheme

/-!
# Morphisms of arithmetic curves and `prop:A1-number-fields` (roadmap D2)

Round 47 of `lean/ROADMAP-arakelov.md`. Source: `latex/notes.tex`, `prop:A1-number-fields`
(Number fields and arithmetic curves):

> Let `𝒩` be the category of number fields with field homomorphisms as morphisms. The
> assignment `K ↦ X̄_K`, `(α : K → L) ↦ Spec(α|_{𝓞_K})`, is an equivalence from `𝒩^op` onto
> the full subcategory of connected objects of `\Schbar_1`.

and the remark after it: the morphisms `X̄_L → X̄_K` are exactly those induced by field
embeddings `K ↪ L`, and the automorphisms of `X̄_K` form `Aut(K)`.

## What is formalized

* `ringHom_injective`: every ring map `𝓞_K → 𝓞_L` is injective (its kernel meets `ℤ` in `0`
  because `𝓞_L` has characteristic zero, and a nonzero ideal of the integral extension
  `ℤ → 𝓞_K` meets `ℤ` nontrivially).
* `ringHomEquiv : (K →+* L) ≃ (𝓞_K →+* 𝓞_L)`: restriction `α ↦ α|_{𝓞_K}`
  (`NumberField.RingOfIntegers.mapRingHom`), with inverse the extension to fraction fields
  (`IsFractionRing.lift`). This is the first equality in the notes' proof.
* `specHomEquiv : (Spec B ⟶ Spec A) ≃ (A →+* B)` (Spec is fully faithful on commutative rings).
* `homEquiv : (X̄_L ⟶ X̄_K) ≃ (K →+* L)` in `\Schbar`: **D2**, the morphisms of arithmetic curves
  are exactly the field embeddings. `endEquiv`: `End(X̄_K) ≃ (K →+* K)`; every endomorphism of a
  number field is an automorphism, so this is `Aut(K)` as a set.
* `NumberFieldCat`: the category `𝒩` (number fields in `Type`, ring homomorphisms).
  `arith : 𝒩ᵒᵖ ⥤ \Schbar`, `K ↦ X̄_K`, `α ↦ Spec(α|_{𝓞_K})`, with `arith_fullyFaithful`.
* `arithEquiv : 𝒩ᵒᵖ ≌ arith.EssImageSubcategory`: **`prop:A1-number-fields` on connected
  objects**, stated as an equivalence onto the essential image (the objects isomorphic to some
  `X̄_K`).

## Divergence (recorded in `lean/README.md`)

`\Schbar_1` (finite disjoint unions of the `X̄_K`) is not built, so "the full subcategory of
connected objects of `\Schbar_1`" is replaced by the essential image of `arith`. The notes'
last proof step, "every connected object of `\Schbar_1` is some `X̄_K`", is true by definition
there and is not a separate theorem here. Coproducts are deliberately left out: no functor into
the Deninger category sends disjoint unions to products (refutation N12 of
`ai/2026-10-31-conditional-dynamical-cohomology/report.md`), so the connected objects are the
ones a Deninger theory is stated on.
-/

open AlgebraicGeometry CategoryTheory NumberField

noncomputable section

namespace WeilRH.Arakelov

namespace NumberFieldCurves

variable {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M]

omit [NumberField K] in
/-- Every ring homomorphism `𝓞_K → 𝓞_L` is injective. -/
lemma ringHom_injective (ψ : 𝓞 K →+* 𝓞 L) : Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have hmem : x ∈ RingHom.ker ψ := hx
  have hne := Ideal.under_ne_bot_of_algebraic_mem (R := ℤ) h0 hmem
    (Algebra.IsIntegral.isIntegral x).isAlgebraic
  apply hne
  have hcomap : (RingHom.ker ψ).under ℤ = RingHom.ker (ψ.comp (algebraMap ℤ (𝓞 K))) :=
    RingHom.comap_ker ψ (algebraMap ℤ (𝓞 K))
  rw [hcomap, RingHom.ext_int (ψ.comp (algebraMap ℤ (𝓞 K))) (Int.castRingHom (𝓞 L))]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (Int.castRingHom (𝓞 L)).injective_int

/-- **Restriction to the rings of integers is a bijection** `(K →+* L) ≃ (𝓞_K →+* 𝓞_L)`
(`prop:A1-number-fields`, first step of the proof). -/
noncomputable def ringHomEquiv : (K →+* L) ≃ (𝓞 K →+* 𝓞 L) where
  toFun α := RingOfIntegers.mapRingHom α
  invFun ψ := IsFractionRing.lift (A := 𝓞 K) (g := (algebraMap (𝓞 L) L).comp ψ)
    (hg := (FaithfulSMul.algebraMap_injective (𝓞 L) L).comp (ringHom_injective ψ))
  left_inv α := by
    apply RingHom.ext; intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    rfl
  right_inv ψ := by
    apply RingHom.ext; intro x
    apply RingOfIntegers.ext
    simp only [RingOfIntegers.mapRingHom_apply]
    exact IsFractionRing.lift_algebraMap (A := 𝓞 K) _ x

@[simp] lemma ringHomEquiv_apply (α : K →+* L) :
    ringHomEquiv α = RingOfIntegers.mapRingHom α := rfl

/-- `Spec` is fully faithful: `(Spec B ⟶ Spec A) ≃ (A →+* B)`. -/
noncomputable def specHomEquiv (A B : Type) [CommRing A] [CommRing B] :
    (Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) ≃ (A →+* B) where
  toFun f := (Spec.preimage f).hom
  invFun φ := Spec.map (CommRingCat.ofHom φ)
  left_inv f := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage f).hom) = f
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  right_inv φ := by
    show (Spec.preimage (Spec.map (CommRingCat.ofHom φ))).hom = φ
    rw [Spec.preimage_map, CommRingCat.hom_ofHom]

/-- `X̄_K` as an object of `\Schbar`. -/
abbrev xbar (K : Type) [Field K] [NumberField K] : Schbar := Xbar.obj K

variable (K L)

/-- **D2: morphisms of arithmetic curves are field embeddings.** In `\Schbar`,
`(X̄_L ⟶ X̄_K) ≃ (K →+* L)` (`prop:A1-number-fields` and the remark after it). -/
noncomputable def homEquiv :
    (xbar L ⟶ xbar K) ≃ (K →+* L) :=
  Schbar.forgetFullyFaithful.homEquiv.trans
    ((specHomEquiv (𝓞 K) (𝓞 L)).trans ringHomEquiv.symm)

/-- `End(X̄_K) ≃ (K →+* K)`; every field endomorphism of a number field is bijective, so these
are the automorphisms of `K` (remark after `prop:A1-number-fields`). -/
noncomputable def endEquiv : (xbar K ⟶ xbar K) ≃ (K →+* K) :=
  homEquiv K K

variable {K L}

/-- The morphism `X̄_L → X̄_K` induced by `α : K → L`: `Spec(α|_{𝓞_K})`. -/
noncomputable def ofRingHom (α : K →+* L) :
    xbar L ⟶ xbar K :=
  Schbar.forgetFullyFaithful.preimage
    (Spec.map (CommRingCat.ofHom (RingOfIntegers.mapRingHom α)))

lemma homEquiv_ofRingHom (α : K →+* L) : homEquiv K L (ofRingHom α) = α := by
  have h1 : Schbar.forget.map (ofRingHom α) =
      Spec.map (CommRingCat.ofHom (RingOfIntegers.mapRingHom α)) :=
    Schbar.forgetFullyFaithful.map_preimage (X := xbar L) (Y := xbar K) _
  have h2 : (specHomEquiv (𝓞 K) (𝓞 L)) (Spec.map (CommRingCat.ofHom (RingOfIntegers.mapRingHom α)))
      = ringHomEquiv α := (specHomEquiv (𝓞 K) (𝓞 L)).right_inv _
  show ringHomEquiv.symm ((specHomEquiv (𝓞 K) (𝓞 L)) (Schbar.forget.map (ofRingHom α))) = α
  rw [h1, h2, Equiv.symm_apply_apply]

lemma ofRingHom_id : ofRingHom (RingHom.id K) = 𝟙 (xbar K) := by
  unfold ofRingHom
  have : RingOfIntegers.mapRingHom (RingHom.id K) = RingHom.id (𝓞 K) := by
    apply RingHom.ext; intro x; rfl
  rw [this]
  exact (congrArg Schbar.forgetFullyFaithful.preimage (Spec.map_id _)).trans
    Schbar.forgetFullyFaithful.preimage_id

lemma ofRingHom_comp (α : K →+* L) (β : L →+* M) :
    ofRingHom (β.comp α) = ofRingHom β ≫ ofRingHom α := by
  unfold ofRingHom
  have : RingOfIntegers.mapRingHom (β.comp α) =
      (RingOfIntegers.mapRingHom β).comp (RingOfIntegers.mapRingHom α) := by
    apply RingHom.ext; intro x; rfl
  rw [this, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Schbar.forgetFullyFaithful.preimage_comp (X := xbar M) (Y := xbar L) (Z := xbar K) _ _

end NumberFieldCurves

/-- **The category `𝒩` of number fields** (`prop:A1-number-fields`): number fields in `Type`,
with ring (equivalently, field) homomorphisms. -/
structure NumberFieldCat where
  /-- The underlying field. -/
  carrier : Type
  [field : Field carrier]
  [numberField : NumberField carrier]

attribute [instance] NumberFieldCat.field NumberFieldCat.numberField

namespace NumberFieldCat

instance : Category NumberFieldCat where
  Hom K L := K.carrier →+* L.carrier
  id K := RingHom.id K.carrier
  comp f g := g.comp f

open NumberFieldCurves

/-- **`K ↦ X̄_K`, `(α : K → L) ↦ Spec(α|_{𝓞_K})`** as a functor `𝒩ᵒᵖ ⥤ \Schbar`. -/
noncomputable def arith : NumberFieldCatᵒᵖ ⥤ Schbar where
  obj K := xbar K.unop.carrier
  map {K L} f := ofRingHom (K := L.unop.carrier) (L := K.unop.carrier) f.unop
  map_id _ := ofRingHom_id
  map_comp {K L M} f g := ofRingHom_comp (K := M.unop.carrier) (L := L.unop.carrier)
    (M := K.unop.carrier) g.unop f.unop

lemma homEquiv_arith_map {K L : NumberFieldCatᵒᵖ} (f : K ⟶ L) :
    homEquiv L.unop.carrier K.unop.carrier (arith.map f) = f.unop :=
  homEquiv_ofRingHom _

/-- **`prop:A1-number-fields`, fully faithful part**: `K ↦ X̄_K` is fully faithful, i.e.
`Hom_𝒩(K, L) = Hom(X̄_L, X̄_K)`. -/
noncomputable def arith_fullyFaithful : arith.FullyFaithful where
  preimage {K L} h := Quiver.Hom.op (homEquiv L.unop.carrier K.unop.carrier h)
  map_preimage {K L} h := by
    apply (homEquiv L.unop.carrier K.unop.carrier).injective
    rw [homEquiv_arith_map]; rfl
  preimage_map {K L} f := by
    apply Quiver.Hom.unop_inj
    show homEquiv L.unop.carrier K.unop.carrier (arith.map f) = f.unop
    exact homEquiv_arith_map f

instance : arith.Full := arith_fullyFaithful.full
instance : arith.Faithful := arith_fullyFaithful.faithful

/-- **`prop:A1-number-fields`** (on connected objects): `𝒩ᵒᵖ` is equivalent to the full
subcategory of `\Schbar` of objects isomorphic to some `X̄_K`. -/
noncomputable def arithEquiv : NumberFieldCatᵒᵖ ≌ arith.EssImageSubcategory :=
  Functor.asEquivalence arith.toEssImage

end NumberFieldCat

end WeilRH.Arakelov

end
