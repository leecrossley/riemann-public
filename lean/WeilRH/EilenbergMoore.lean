/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Thick-subcategory induction: the abstract core of `prop:EM` / `prop:EM-criterion`

Source: `latex/notes.tex`, Definition `def:EM-setting`(a), Proposition `prop:EM` and
Proposition `prop:EM-criterion` (Eilenberg–Moore dump, Theorem B and Corollary B.1).

## Design (lean-design-definitions)

The notes work in `D(S_et, Λ)`, `Λ = 𝔽_ℓ`, with `⟨Λ_S⟩` the smallest strictly full triangulated
subcategory containing `Λ_S` and closed under direct summands, and prove (`prop:EM`) that the
natural transformation `μ_S(-, L')` of exact functors is an isomorphism on `⟨Λ_S⟩` because it is
one at `Λ_S`. Étale derived categories, cochain enhancements, proper base change and the
projection formula are **not** available in Mathlib; they are inputs, not formalized. What is
formalized is the category-theoretic core, for an arbitrary pretriangulated category `C`
(Mathlib's `Pretriangulated`), triangulated functors `F G : C ⥤ D` (`Functor.IsTriangulated`,
commuting with the shift) and a natural transformation `κ : F ⟶ G` compatible with the shift
(`NatTrans.CommShift κ ℤ`) — the notes' "natural transformation of exact functors".

* `ThickClosure P` is the **inductively defined** thick closure of a class `P` of objects:
  the least class containing `P` and the zero objects, closed under all shifts `X ↦ X⟦n⟧`
  (`n : ℤ`), under the middle term of a distinguished triangle whose outer terms lie in it, and
  under retracts (direct summands). Retract-closure gives closure under isomorphisms (strictly
  full), and rotation gives the other two 2-out-of-3 properties (`ThickClosure.ext₁`,
  `ThickClosure.ext₃`). `thickClosure_le` proves it is the **smallest** such class: it is the
  notes' `⟨P⟩` (Definition `def:EM-setting`(a) with `P = {Λ_S}`).
* `isoLocus κ` is the class of `X` with `κ.app X` an isomorphism; it is triangulated (five lemma
  `Pretriangulated.isIso₂_of_isIso₁₃` applied to the morphism of distinguished triangles
  `NatTrans.mapTriangleHom κ T : F.mapTriangle T ⟶ G.mapTriangle T`), stable under shifts and
  retracts.

## Main results

* `isIso_app_of_mem_thickClosure` (**`prop:EM`, abstract core**): if `κ.app X` is an iso for every
  `X` in `P` (e.g. `P = {Λ_S}`), it is an iso on every object of `ThickClosure P`.
* `isIso_comp_of_mem_thickClosure`: the same for a composite `e₁ ≫ κ.app X ≫ e₂` with `e₁`, `e₂`
  isomorphisms (the shape of the Eilenberg–Moore map `κ` of Definition `def:EM-kappa`, all of whose
  factors except `μ_S` are isomorphisms).
* `ThickClosure.biprod`, `ThickClosure.ext₁`, `ThickClosure.ext₃`, `ThickClosure.shift`,
  `ThickClosure.of_iso` (**`prop:EM-criterion`, abstract core**): the closure operations used in
  the notes' induction on filtrations and on truncation triangles.
-/

namespace WeilRH

open CategoryTheory Category Limits Pretriangulated
open scoped ZeroObject

namespace EM

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The **thick closure** `⟨P⟩` of a class `P` of objects of a pretriangulated category
(`def:EM-setting`(a)): the least class containing `P` and the zero objects, closed under
shifts, under extensions (the middle vertex of a distinguished triangle whose outer vertices lie
in it) and under retracts. -/
inductive ThickClosure (P : ObjectProperty C) : ObjectProperty C
  | of_mem {X : C} : P X → ThickClosure P X
  | zero {X : C} : IsZero X → ThickClosure P X
  | shift {X : C} (n : ℤ) : ThickClosure P X → ThickClosure P (X⟦n⟧)
  | ext₂ (T : Triangle C) : T ∈ distTriang C → ThickClosure P T.obj₁ → ThickClosure P T.obj₃ →
      ThickClosure P T.obj₂
  | retract {X Y : C} : Retract X Y → ThickClosure P Y → ThickClosure P X

namespace ThickClosure

variable {P : ObjectProperty C}

lemma le : P ≤ ThickClosure P := fun _ h => of_mem h

/-- The thick closure is closed under isomorphisms (it is strictly full). -/
lemma of_iso {X Y : C} (e : X ≅ Y) (h : ThickClosure P X) : ThickClosure P Y :=
  retract e.symm.retract h

instance : (ThickClosure P).IsStableUnderRetracts where
  of_retract h hY := retract h hY

instance : (ThickClosure P).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ h => shift n h⟩

instance : (ThickClosure P).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, zero (isZero_zero C)⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ (ext₂ T hT h₁ h₃)

/-- Closure under the third vertex of a distinguished triangle. -/
lemma ext₃ (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : ThickClosure P T.obj₁)
    (h₂ : ThickClosure P T.obj₂) : ThickClosure P T.obj₃ := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := (ThickClosure P).ext_of_isTriangulatedClosed₃' T hT h₁ h₂
  exact of_iso e.symm hY

/-- Closure under the first vertex of a distinguished triangle. -/
lemma ext₁ (T : Triangle C) (hT : T ∈ distTriang C) (h₂ : ThickClosure P T.obj₂)
    (h₃ : ThickClosure P T.obj₃) : ThickClosure P T.obj₁ := by
  obtain ⟨Y, hY, ⟨e⟩⟩ := (ThickClosure P).ext_of_isTriangulatedClosed₁' T hT h₂ h₃
  exact of_iso e.symm hY

/-- Closure under binary direct sums (split triangles are distinguished). -/
lemma biprod {X Y : C} (hX : ThickClosure P X) (hY : ThickClosure P Y) :
    ThickClosure P (X ⊞ Y) :=
  ext₂ _ (binaryBiproductTriangle_distinguished X Y) hX hY

/-- Closure under finite direct sums of copies `X^{⊕ n}`, built as iterated binary sums. -/
lemma pow {X : C} (hX : ThickClosure P X) : ∀ n : ℕ, ThickClosure P (Nat.rec (0 : C)
    (fun _ Y => X ⊞ Y) n)
  | 0 => zero (isZero_zero C)
  | n + 1 => biprod hX (pow hX n)

end ThickClosure

/-- **`⟨P⟩` is the smallest thick subcategory containing `P`.** Any class of objects that
contains `P`, is triangulated and is stable under retracts contains `ThickClosure P`. -/
theorem thickClosure_le {P Q : ObjectProperty C} [Q.IsTriangulated] [Q.IsStableUnderRetracts]
    (hPQ : P ≤ Q) : ThickClosure P ≤ Q := by
  intro X hX
  induction hX with
  | of_mem h => exact hPQ _ h
  | zero h => exact Q.prop_of_isZero h
  | shift n _ ih => exact Q.le_shift n _ ih
  | ext₂ T hT _ _ ih₁ ih₃ =>
      obtain ⟨Y, hY, ⟨e⟩⟩ := Q.ext_of_isTriangulatedClosed₂' T hT ih₁ ih₃
      exact Q.prop_of_retract e.retract hY
  | retract h _ ih => exact Q.prop_of_retract h ih

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section NatTrans

variable {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (κ : F ⟶ G) [NatTrans.CommShift κ ℤ]

/-- A shift-compatible natural transformation `κ : F ⟶ G` gives a morphism of triangles
`F.mapTriangle T ⟶ G.mapTriangle T` with components `κ.app`. -/
@[simps]
def mapTriangleHom (T : Triangle C) : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := κ.app T.obj₁
  hom₂ := κ.app T.obj₂
  hom₃ := κ.app T.obj₃
  comm₁ := by simp
  comm₂ := by simp
  comm₃ := by
    dsimp
    simp only [assoc, NatTrans.shift_app_comm κ (1 : ℤ) T.obj₁, NatTrans.naturality_assoc]

/-- The **iso locus** of `κ`: objects `X` with `κ.app X` an isomorphism. -/
def isoLocus : ObjectProperty C := fun X => IsIso (κ.app X)

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
lemma isoLocus_shift {X : C} (n : ℤ) (h : isoLocus κ X) : isoLocus κ (X⟦n⟧) := by
  have : IsIso (κ.app X) := h
  change IsIso (κ.app (X⟦n⟧))
  rw [NatTrans.app_shift κ n X]
  infer_instance

instance : (isoLocus κ).IsStableUnderRetracts where
  of_retract h hY :=
    MorphismProperty.IsStableUnderRetracts.of_retract (P := MorphismProperty.isomorphisms D)
      (NatTrans.retractArrowApp κ h) hY

variable [F.IsTriangulated] [G.IsTriangulated]

instance : (isoLocus κ).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, by
    change IsIso (κ.app 0)
    exact ⟨⟨(G.map_isZero (isZero_zero C)).to_ (F.obj 0),
      (F.map_isZero (isZero_zero C)).eq_of_src _ _,
      (G.map_isZero (isZero_zero C)).eq_of_src _ _⟩⟩⟩
  isStableUnderShiftBy n := ⟨fun _ h => isoLocus_shift κ n h⟩
  ext₂' T hT h₁ h₃ := by
    refine ObjectProperty.le_isoClosure _ _ ?_
    have : IsIso (mapTriangleHom κ T).hom₁ := h₁
    have : IsIso (mapTriangleHom κ T).hom₃ := h₃
    exact isIso₂_of_isIso₁₃ (mapTriangleHom κ T) (F.map_distinguished T hT)
      (G.map_distinguished T hT) inferInstance inferInstance

/-- **`prop:EM`, abstract core (thick-subcategory induction).** Let `F G : C ⥤ D` be triangulated
functors between pretriangulated categories and `κ : F ⟶ G` a natural transformation compatible
with the shifts. If `κ.app X` is an isomorphism for every `X` in `P`, then `κ.app X` is an
isomorphism for every `X` in the thick closure `⟨P⟩`. -/
theorem isIso_app_of_mem_thickClosure {P : ObjectProperty C} (hP : ∀ X, P X → IsIso (κ.app X))
    {X : C} (hX : ThickClosure P X) : IsIso (κ.app X) :=
  thickClosure_le (Q := isoLocus κ) hP X hX

/-- **`prop:EM`, the Eilenberg–Moore map.** If a morphism `k` factors as `e₁ ≫ κ.app X ≫ e₂`
with `e₁`, `e₂` isomorphisms (in the notes, the identifications `C•(Y) ≅ RΓ_S(Rf_*Λ)`, … around
`μ_S`), and `X` lies in the thick closure of a class on which `κ` is an isomorphism, then `k` is an
isomorphism. -/
theorem isIso_comp_of_mem_thickClosure {P : ObjectProperty C} (hP : ∀ X, P X → IsIso (κ.app X))
    {X : C} (hX : ThickClosure P X) {A B : D} (e₁ : A ⟶ F.obj X) (e₂ : G.obj X ⟶ B) [IsIso e₁]
    [IsIso e₂] : IsIso (e₁ ≫ κ.app X ≫ e₂) := by
  have := isIso_app_of_mem_thickClosure κ hP hX
  infer_instance

end NatTrans

end EM

end WeilRH
