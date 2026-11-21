import Mathlib

/-!
# Zeta functions of schemes of finite type over `Spec ℤ`

`notes.tex`, Section `subsec:schemes`: for a scheme `X` of finite type over `Spec ℤ` with set of
closed points `X₀`, `ζ(X, s) = ∏_{x ∈ X₀} (1 - N(x)^{-s})^{-1}`, where `N(x) = #κ(x)`.

* `isJacobsonRing_int`: `ℤ` is a Jacobson ring (so `Spec ℤ` is a Jacobson space).
* `SchemeZeta.norm`, `SchemeZeta.zeta`: `N(x)` and the Euler product (a `tprod`, meaningful on the
  half-plane where it converges absolutely, as in the manuscript).
* `SchemeZeta.finite_residueField`: for `X` locally of finite type over `Spec ℤ`, the residue field
  at every closed point is finite, so `N(x)` is a genuine prime power (`one_lt_norm`).
* `prop:zeta-intrinsic`: `SchemeZeta.relClosedPoints` are the points that are closed in their fibre
  over a closed point of a base `S`; for `S` a Jacobson scheme and `X → S` locally of finite type
  they are exactly the closed points of `X` (`relClosedPoints_eq`), so the zeta function relative to
  `S` equals the absolute one (`zetaRel_eq`). Instances: `S = Spec ℤ` and `S = Spec 𝒪_K`.
* `SchemeZeta.zeta_specInt`: `ζ(Spec ℤ, s) = ζ(s)` for `Re s > 1`, so the definition is not vacuous
  and is normalized as in the manuscript.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilRH

/-- `ℤ` is a Jacobson ring: its prime ideals are `0`, which is the intersection of the maximal
ideals, and the maximal ideals `(p)`. -/
instance isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun n hn => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hn
    have h1 := Int.isUnit_iff.mp (hn 1)
    have h2 := Int.isUnit_iff.mp (hn 2)
    simp only [Ideal.mem_bot]
    omega
  · exact @Ideal.jacobson_eq_self_of_isMaximal _ _ _ (hP.isMaximal h)

namespace SchemeZeta

/-- The base scheme `Spec ℤ`. -/
noncomputable abbrev SpecZ : Scheme.{0} := Spec (CommRingCat.of ℤ)

/-- The norm `N(x) = #κ(x)` of a point (as `Nat.card`, so `0` if `κ(x)` is infinite). -/
noncomputable def norm (X : Scheme.{0}) (x : X) : ℕ := Nat.card (X.residueField x)

/-- `ζ(X, s) = ∏_{x ∈ X₀} (1 - N(x)^{-s})^{-1}` (`notes.tex`, Section `subsec:schemes`). -/
noncomputable def zeta (X : Scheme.{0}) (s : ℂ) : ℂ :=
  ∏' x : closedPoints X, (1 - ((norm X x : ℕ) : ℂ) ^ (-s))⁻¹

/-- A field that is a finitely generated `ℤ`-module is finite. -/
theorem finite_of_moduleFinite_int (K : Type) [Field K] [Module.Finite ℤ K] : Finite K := by
  have hchar : ringChar K ≠ 0 := by
    intro h0
    haveI : CharP K 0 := ringChar.of_eq h0
    haveI : CharZero K := CharP.charP_to_charZero K
    have hinj : Function.Injective (algebraMap ℤ K) := by
      intro a b hab
      simpa using hab
    exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField K))
  apply Module.finite_of_fg_torsion
  intro m
  refine ⟨⟨(ringChar K : ℤ), ?_⟩, ?_⟩
  · simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
    exact hchar
  · show ((ringChar K : ℕ) : ℤ) • m = 0
    rw [natCast_zsmul, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

/-- At a closed point of a scheme locally of finite type over `Spec ℤ`, the residue field is
finite (Jacobson property of `ℤ`; Zariski's lemma). -/
theorem finite_residueField {X : Scheme.{0}} (f : X ⟶ SpecZ) [LocallyOfFiniteType f] (x : X)
    (hx : x ∈ closedPoints X) : Finite (X.residueField x) := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp (mem_closedPoints_iff.mp hx)
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  rw [← hφ, IsFinite.SpecMap_iff] at hfin
  have hφint : φ.hom = algebraMap ℤ (X.residueField x) := RingHom.ext_int _ _
  rw [hφint, RingHom.finite_algebraMap] at hfin
  exact finite_of_moduleFinite_int _

/-- Every closed point of a scheme locally of finite type over `Spec ℤ` has norm `> 1`. -/
theorem one_lt_norm {X : Scheme.{0}} (f : X ⟶ SpecZ) [LocallyOfFiniteType f] (x : X)
    (hx : x ∈ closedPoints X) : 1 < norm X x := by
  haveI := finite_residueField f x hx
  unfold norm
  exact Finite.one_lt_card

/-! ### `prop:zeta-intrinsic` -/

/-- Points of `X` closed relative to `g : X ⟶ S`: their image is a closed point of `S` and they
are closed points of the fibre `g.fiber (g x)` (identified with `g⁻¹{g x}` by `fiberHomeo`). -/
def relClosedPoints {X S : Scheme.{0}} (g : X ⟶ S) : Set X :=
  {x | IsClosed ({g x} : Set S) ∧
    IsClosed ({(g.fiberHomeo (g x)).symm ⟨x, rfl⟩} : Set (g.fiber (g x)))}

/-- For `S` Jacobson and `g` locally of finite type, the relatively closed points are exactly the
closed points of `X` (Stacks 01TB (1) ⇒ (3) for the image; closed subsets of the closed fibre). -/
theorem relClosedPoints_eq {X S : Scheme.{0}} (g : X ⟶ S) [JacobsonSpace S]
    [LocallyOfFiniteType g] : relClosedPoints g = closedPoints X := by
  ext x
  simp only [relClosedPoints, Set.mem_ofPred_eq, mem_closedPoints_iff]
  have hsub : ∀ (A : Set (g ⁻¹' {g x})), IsClosed A ↔
      IsClosed ((g.fiberHomeo (g x)).symm '' A) := fun A =>
    ((g.fiberHomeo (g x)).symm.isClosed_image).symm
  constructor
  · rintro ⟨hy, hxf⟩
    have hF : IsClosed (g ⁻¹' {g x} : Set X) := hy.preimage g.continuous
    have h1 : IsClosed ({⟨x, rfl⟩} : Set (g ⁻¹' {g x})) := by
      rw [hsub, Set.image_singleton]
      exact hxf
    have := hF.isClosedMap_subtype_val _ h1
    simpa using this
  · intro hx
    refine ⟨?_, ?_⟩
    · exact mem_closedPoints_iff.mp
        (g.closePoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hx))
    · have h1 : IsClosed ({⟨x, rfl⟩} : Set (g ⁻¹' {g x})) := by
        have := hx.preimage (continuous_subtype_val (p := fun z => z ∈ g ⁻¹' {g x}))
        convert this using 1
        ext ⟨z, hz⟩
        simp [Subtype.ext_iff]
      rw [hsub, Set.image_singleton] at h1
      exact h1

/-- The zeta function of `X` relative to `g : X ⟶ S`: the Euler product over relatively closed
points. -/
noncomputable def zetaRel {X S : Scheme.{0}} (g : X ⟶ S) (s : ℂ) : ℂ :=
  ∏' x : relClosedPoints g, (1 - ((norm X x : ℕ) : ℂ) ^ (-s))⁻¹

/-- `prop:zeta-intrinsic`: for `S` Jacobson (e.g. `Spec ℤ`, `Spec 𝒪_K`) and `X → S` locally of
finite type, the zeta function of `X` computed relative to `S` is `ζ(X, s)`; in particular it is
the same over `Spec ℤ` and over `Spec 𝒪_K`. -/
theorem zetaRel_eq {X S : Scheme.{0}} (g : X ⟶ S) [JacobsonSpace S] [LocallyOfFiniteType g]
    (s : ℂ) : zetaRel g s = zeta X s := by
  unfold zetaRel zeta
  rw [relClosedPoints_eq g]

/-- `ℤ`-version of `prop:zeta-intrinsic` stated for two structure morphisms: for `X` locally of
finite type over both `Spec ℤ` and a Jacobson base `S`, the two relative zeta functions agree. -/
theorem zetaRel_eq_zetaRel {X S T : Scheme.{0}} (g : X ⟶ S) (h : X ⟶ T) [JacobsonSpace S]
    [JacobsonSpace T] [LocallyOfFiniteType g] [LocallyOfFiniteType h] (s : ℂ) :
    zetaRel g s = zetaRel h s := by
  rw [zetaRel_eq, zetaRel_eq]

/-- `Spec 𝒪_K` is a Jacobson space (`𝒪_K` is integral over the Jacobson ring `ℤ`). -/
instance isJacobsonRing_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    IsJacobsonRing (NumberField.RingOfIntegers K) :=
  isJacobsonRing_of_isIntegral (R := ℤ)

/-! ### `ζ(Spec ℤ, s) = ζ(s)` -/

theorem span_prime_isPrime (p : Nat.Primes) : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)

theorem span_prime_isMaximal (p : Nat.Primes) : (Ideal.span {(p.1 : ℤ)}).IsMaximal :=
  (span_prime_isPrime p).isMaximal (by simp [p.2.ne_zero])

/-- The closed point `(p)` of `Spec ℤ`. -/
def primePoint (p : Nat.Primes) : closedPoints SpecZ :=
  ⟨⟨Ideal.span {(p.1 : ℤ)}, span_prime_isPrime p⟩, by
    exact mem_closedPoints_iff.mpr
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (span_prime_isMaximal p))⟩

theorem primePoint_bijective : Function.Bijective primePoint := by
  constructor
  · intro p q h
    have h' : Ideal.span {(p.1 : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} :=
      congrArg (fun x : closedPoints SpecZ => x.1.asIdeal) h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h'
    exact Subtype.ext (by simpa using h')
  · rintro ⟨x, hx⟩
    have hmax : x.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp (mem_closedPoints_iff.mp hx)
    have hne : x.asIdeal ≠ ⊥ := by
      intro h
      rw [h] at hmax
      exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hmax)
    have hp : Prime (Submodule.IsPrincipal.generator x.asIdeal) :=
      Submodule.IsPrincipal.prime_generator_of_isPrime _ hne
    refine ⟨⟨_, Int.prime_iff_natAbs_prime.mp hp⟩, Subtype.ext (PrimeSpectrum.ext ?_)⟩
    change Ideal.span {(((Submodule.IsPrincipal.generator x.asIdeal).natAbs : ℕ) : ℤ)} = x.asIdeal
    rw [Int.span_natAbs, Ideal.span_singleton_generator]

/-- Closed points of `Spec ℤ` correspond to rational primes. -/
noncomputable def closedPointsSpecZEquiv : Nat.Primes ≃ closedPoints SpecZ :=
  Equiv.ofBijective primePoint primePoint_bijective

/-- The residue field of `Spec ℤ` at `(p)` has `p` elements. -/
theorem norm_primePoint (p : Nat.Primes) : norm SpecZ (primePoint p).1 = p := by
  unfold norm
  haveI : (primePoint p).1.asIdeal.IsMaximal := span_prime_isMaximal p
  rw [Nat.card_congr (Scheme.Spec.residueFieldIso (CommRingCat.of ℤ) (primePoint p).1).commRingCatIsoToRingEquiv.toEquiv]
  rw [← Nat.card_congr (RingEquiv.ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField (primePoint p).1.asIdeal)).toEquiv]
  change Nat.card (ℤ ⧸ Ideal.span {(p.1 : ℤ)}) = p
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- `ζ(Spec ℤ, s) = ζ(s)` for `Re s > 1`. -/
theorem zeta_specInt {s : ℂ} (hs : 1 < s.re) : zeta SpecZ s = riemannZeta s := by
  unfold zeta
  rw [← Equiv.tprod_eq closedPointsSpecZEquiv]
  simp only [closedPointsSpecZEquiv, Equiv.ofBijective_apply, norm_primePoint]
  exact riemannZeta_eulerProduct_tprod hs

end SchemeZeta

end WeilRH
