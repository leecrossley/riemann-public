import WeilRH.ComplexPoints

/-!
# Arakelov varieties (Gillet–Soulé 1990, 5.1.1)

Roadmap target A3 of `lean/ROADMAP-arakelov.md`, started in round 45. Source: Gillet–Soulé,
*Arithmetic intersection theory*, Publ. Math. IHÉS 72 (1990), 5.1.1 (p. 154); local copy
`refs/arakelov/gillet-soule-1990-arithmetic-intersection-theory.pdf`.

GS 5.1.1: "Fix an arithmetic ring `A = (A, S, F_∞)`. An **Arakelov variety** `X = (X, ω)` is a pair
consisting of an arithmetic variety `X` over `A`, regular with projective generic fibre, and a
Kähler form `ω` on `X_∞` satisfying `F_∞^* ω = −ω` (this is equivalent to requiring that the
corresponding Kähler metric is invariant under `F_∞`)." This is the notes' `def:arakelov-pair`
(over `A = ℤ`, following Flach–Morin 2020, pp. 520–521).

* `IsRegularScheme X`: every stalk of `X` is a regular local ring (Stacks 00KU via Mathlib's
  `IsRegularLocalRing`). `isRegularScheme_spec`: `Spec A` is regular when `A` is a regular ring.
* `KahlerInterface P F`: the **analytic interface** of roadmap decision D2. It provides a real
  vector space of real `(1,1)`-forms on `X_∞`, the pullback `F_∞^*`, and the Kähler predicate.
* `ArakelovVariety R`: an arithmetic variety over `R`, regular, with proper generic fibre, together
  with a `KahlerInterface` on its complex points and a Kähler form `ω` with `F_∞^* ω = −ω`.
  `ArakelovVariety.toArithmeticVariety` is the forgetful map.
* `ArakelovVariety.ofRing R`: `Spec A` for an arithmetic ring `A`. Its `X_∞ ≃ S` is a finite set
  (a 0-dimensional complex manifold), on which the only real `(1,1)`-form is `0`, which is
  Kähler. In particular `Spec 𝓞 K` is an Arakelov variety for every number field `K`
  (`ArakelovVariety.ringOfIntegers K`).

## Divergences from Gillet–Soulé (recorded in `lean/README.md`)

1. **Kähler datum as an interface** (roadmap D2). Mathlib has no analytification of schemes, no
   `(p,q)`-forms on complex manifolds and no Kähler forms, so `ω` is a point of an abstract real
   vector space with an abstract predicate `IsKahler`. `KahlerInterface` records only what GS 5.1.1
   uses: real `(1,1)`-forms, `F_∞^*`, and which forms are Kähler. It is a placeholder for Tier B
   (B1–B3) and makes no claim that the predicate is the true Kähler condition.
2. **Projective → proper.** Mathlib has no projective morphisms, so "projective generic fibre" is
   weakened to "proper generic fibre" (`IsProper`). For the `Spec A` instances the generic fibre
   is `Spec (Frac A)`, which is projective, so nothing is lost there.
3. The base ring is in `Type` (universe 0), as in `WeilRH.ComplexPoints`.
-/

open AlgebraicGeometry CategoryTheory Limits

namespace WeilRH.Arakelov

/-- A scheme is **regular** if all its stalks are regular local rings. -/
def IsRegularScheme (X : Scheme) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- `Spec A` is regular when `A` is a regular ring: its stalks are the localizations `A_𝔭`. -/
lemma isRegularScheme_spec (A : Type) [CommRing A] [IsRegularRing A] :
    IsRegularScheme (Spec (CommRingCat.of A)) := fun x =>
  IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv.symm

/-- **Analytic interface for a Kähler datum on `X_∞`** (roadmap decision D2; GS 5.1.1). `Forms` is
the real vector space of real `(1,1)`-forms on the complex manifold `X_∞` (with underlying set
`P` and involution `F`), `pullback` is `F_∞^*`, an involution, and `IsKahler` singles out the
Kähler forms. This is a placeholder for the analytic theory, which Mathlib does not have. -/
structure KahlerInterface (P : Type) (F : P → P) where
  /-- Real `(1,1)`-forms on `X_∞`. -/
  Forms : Type
  [addCommGroup : AddCommGroup Forms]
  [module : Module ℝ Forms]
  /-- The pullback `F_∞^*`. -/
  pullback : Forms →ₗ[ℝ] Forms
  pullback_pullback : ∀ ω, pullback (pullback ω) = ω
  /-- Which real `(1,1)`-forms are Kähler forms. -/
  IsKahler : Forms → Prop

attribute [instance] KahlerInterface.addCommGroup KahlerInterface.module

namespace KahlerInterface

/-- The interface on a **finite** (0-dimensional) `X_∞`: the only real `(1,1)`-form is `0`, and it
is a Kähler form, since the positivity condition is vacuous on the zero tangent spaces. -/
def zeroDim (P : Type) (F : P → P) : KahlerInterface P F where
  Forms := PUnit
  pullback := 0
  pullback_pullback _ := rfl
  IsKahler _ := True

end KahlerInterface

variable {A : Type} [CommRing A] [IsDomain A] [IsRegularRing A]

/-- **Arakelov variety** (Gillet–Soulé 1990, 5.1.1): an arithmetic variety `X` over the arithmetic
ring `R`, regular with proper (GS: projective) generic fibre, with a Kähler form `ω` on `X_∞`
satisfying `F_∞^* ω = −ω`. The Kähler datum is given through `KahlerInterface` (see the module
docstring). -/
structure ArakelovVariety (R : ArithmeticRing A) where
  /-- The underlying arithmetic variety. -/
  toArithmeticVariety : ArithmeticVariety R
  regular : IsRegularScheme toArithmeticVariety.X
  /-- The generic fibre is proper (GS require projective). -/
  proper_generic : IsProper (pullback.snd toArithmeticVariety.π (genericPoint A))
  /-- The analytic interface on `X_∞ = X_S(ℂ)` with its involution `F_∞`. -/
  kahler : KahlerInterface toArithmeticVariety.complexPoints toArithmeticVariety.Finf
  /-- The Kähler form `ω`. -/
  ω : kahler.Forms
  ω_kahler : kahler.IsKahler ω
  /-- `F_∞^* ω = −ω`. -/
  F_ω : kahler.pullback ω = -ω

namespace ArakelovVariety

/-- **`Spec A` as an Arakelov variety**: `X_∞ ≃ S` is finite, so it carries the zero Kähler
form. -/
noncomputable def ofRing (R : ArithmeticRing A) : ArakelovVariety R where
  toArithmeticVariety := ArithmeticVariety.base R
  regular := isRegularScheme_spec A
  proper_generic := by
    have : IsIso (pullback.snd (ArithmeticVariety.base R).π (genericPoint A)) := by
      dsimp [ArithmeticVariety.base]; infer_instance
    first
      | exact MorphismProperty.IsMultiplicative.toContainsIdentities.of_isIso _
      | exact (MorphismProperty.of_isIso (P := @IsProper) _)
      | infer_instance
  kahler := KahlerInterface.zeroDim _ _
  ω := PUnit.unit
  ω_kahler := trivial
  F_ω := rfl

/-- The complex points of `ofRing R` are nonempty (nonvacuity: `X_∞ ≃ S ≠ ∅`). -/
instance (R : ArithmeticRing A) : Nonempty (ofRing R).toArithmeticVariety.complexPoints :=
  inferInstanceAs (Nonempty (ArithmeticVariety.base R).complexPoints)

/-- **`Spec 𝓞 K` is an Arakelov variety** for every number field `K` (the notes' `X̄_K`, with
`X_∞ ≃ Hom(K, ℂ)` by `ArithmeticVariety.complexPointsSpecEquiv`). -/
noncomputable def ringOfIntegers (K : Type) [Field K] [NumberField K] :
    ArakelovVariety (ArithmeticRing.ringOfIntegers K) :=
  ofRing _

/-- `Spec ℤ` is an Arakelov variety (the notes' `Spec ℤ̄`). -/
noncomputable def int : ArakelovVariety ArithmeticRing.int := ofRing _

end ArakelovVariety

end WeilRH.Arakelov
