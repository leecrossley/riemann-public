import WeilRH.ArithmeticRing

/-!
# Arithmetic varieties (Gillet–Soulé 1990, Definition 3.2.1): first part

Roadmap target A2 of `lean/ROADMAP-arakelov.md`, started in round 44. Source: Gillet–Soulé,
*Arithmetic intersection theory*, Publ. Math. IHÉS 72 (1990), §3.2, Definition 3.2.1 (p. 125).

GS: if `(A, S, F_∞)` is an arithmetic ring, an **arithmetic variety** over `A` is a scheme `X`
that is flat and of finite type over `Spec A`, whose generic fibre `X_F = X ×_{Spec A} Spec F`
(`F` the fraction field of `A`) is smooth over `F`.

`WeilRH.Arakelov.ArithmeticVariety R` encodes exactly this, with "of finite type" as locally of
finite type and quasi-compact (Mathlib's decomposition), and the generic fibre as the pullback of
`π` along `Spec F → Spec A`. `ArithmeticVariety.base R` is `Spec A` itself.

Not yet encoded (the rest of A2, next round): the complex points `X_∞ = X_S(ℂ)` with the
involution induced by `F_∞`, and the real (p,p)-forms and currents of GS 3.2.1, which need the
analytic prerequisites of Tier B.
-/

open AlgebraicGeometry CategoryTheory Limits

namespace WeilRH.Arakelov

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]

/-- The structure map `Spec F → Spec A` of the generic point (`F = Frac A`). -/
noncomputable def genericPoint (A : Type u) [CommRing A] [IsDomain A] :
    Spec (CommRingCat.of (FractionRing A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))

/-- **Arithmetic variety** over an arithmetic ring (Gillet–Soulé 1990, Definition 3.2.1): a
scheme flat and of finite type over `Spec A` whose generic fibre is smooth over `Frac A`. The
arithmetic ring `R` is recorded for the complex points `X_∞ = X_S(ℂ)` (not yet encoded). -/
structure ArithmeticVariety (_R : ArithmeticRing A) where
  /-- The scheme `X`. -/
  X : Scheme.{u}
  /-- The structure map `π : X → Spec A`. -/
  π : X ⟶ Spec (CommRingCat.of A)
  flat : Flat π
  locallyOfFiniteType : LocallyOfFiniteType π
  quasiCompact : QuasiCompact π
  /-- The generic fibre `X_F → Spec F` is smooth. -/
  smooth_generic : Smooth (pullback.snd π (genericPoint A))

namespace ArithmeticVariety

/-- `Spec A` is an arithmetic variety over the arithmetic ring `(A, S, F_∞)`. -/
noncomputable def base (R : ArithmeticRing A) : ArithmeticVariety R where
  X := Spec (CommRingCat.of A)
  π := 𝟙 _
  flat := inferInstance
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance
  smooth_generic := inferInstance

end ArithmeticVariety

/-- `Spec 𝓞 K` is an arithmetic variety over `𝓞 K` (nonvacuity for number fields). -/
noncomputable example (K : Type u) [Field K] [NumberField K] :
    ArithmeticVariety (ArithmeticRing.ringOfIntegers K) :=
  ArithmeticVariety.base _

end WeilRH.Arakelov
