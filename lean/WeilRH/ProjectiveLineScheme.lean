/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.NLinesGeometry
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective-line scheme in `prop:N-lines`

`projectiveLineScheme F` is `Proj F[X₀, X₁]` with its total-degree grading, and
`projectiveLineToSpec F` is its structure morphism to `Spec F`. This is the concrete scheme
used for the `ℙ¹` factor in the manuscript's `X = E × ℙ¹` example.

The same polynomial `Proj` model appears in AxiomMath/Stacks,
`StacksFrontier/AlgebraicGeometry/ProjPolyChart/Comparison.lean` (`projToSpecCoeff`). Its
`ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient` is a candidate source for the
missing point equivalence, but depends on StacksFrontier and has not been imported here.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

namespace WeilRH.NLinesGeometry

section Scheme

variable (F : Type) [CommRing F]

/-- The total-degree grading of the polynomial ring in two variables. -/
abbrev projectiveLineGrading : ℕ → Submodule F (MvPolynomial (Fin 2) F) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) F

private noncomputable instance : GradedAlgebra (projectiveLineGrading F) :=
  MvPolynomial.gradedAlgebra

/-- The scheme `ℙ¹_F = Proj F[X₀, X₁]`. -/
noncomputable def projectiveLineScheme : Scheme := Proj (projectiveLineGrading F)

/-- The structure morphism `ℙ¹_F → Spec F`, through the degree-zero piece of the grading. -/
noncomputable def projectiveLineToSpec :
    projectiveLineScheme F ⟶ Spec (CommRingCat.of F) :=
  Proj.toSpecZero (projectiveLineGrading F) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F ↥(projectiveLineGrading F 0)))

private theorem projectiveLine_finiteType :
    Algebra.FiniteType ↥(projectiveLineGrading F 0) (MvPolynomial (Fin 2) F) := by
  letI : IsScalarTower F ↥(projectiveLineGrading F 0) (MvPolynomial (Fin 2) F) :=
    IsScalarTower.of_algebraMap_eq (R := F) (S := ↥(projectiveLineGrading F 0))
      (A := MvPolynomial (Fin 2) F) (fun x => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType F _ _

private theorem projectiveLine_coeff_surjective :
    Function.Surjective (algebraMap F ↥(projectiveLineGrading F 0)) := by
  intro x
  have hx : (x : MvPolynomial (Fin 2) F) ∈ (1 : Submodule F (MvPolynomial (Fin 2) F)) := by
    simpa only [projectiveLineGrading, MvPolynomial.homogeneousSubmodule_zero] using x.property
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp hx
  exact ⟨a, Subtype.ext ha⟩

/-- The structure morphism `ℙ¹_F → Spec F` is proper. -/
theorem projectiveLineToSpec_isProper : IsProper (projectiveLineToSpec F) := by
  letI : Algebra.FiniteType ↥(projectiveLineGrading F 0) (MvPolynomial (Fin 2) F) :=
    projectiveLine_finiteType F
  haveI : IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap F ↥(projectiveLineGrading F 0)))) := by
    apply (IsFinite.SpecMap_iff _).2
    exact RingHom.Finite.of_surjective _ (projectiveLine_coeff_surjective F)
  haveI : IsProper (Proj.toSpecZero (projectiveLineGrading F)) := inferInstance
  haveI : IsProper
      (Spec.map (CommRingCat.ofHom (algebraMap F ↥(projectiveLineGrading F 0)))) := inferInstance
  unfold projectiveLineToSpec
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _
    (inferInstance : IsProper (Proj.toSpecZero (projectiveLineGrading F)))
    (inferInstance : IsProper
      (Spec.map (CommRingCat.ofHom (algebraMap F ↥(projectiveLineGrading F 0)))))

end Scheme

section Zeta

variable (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The rational expression for `E ×_F ℙ¹_F` on `Re s > 2`, conditional on the point-equivalence
for this concrete projective-line scheme and the elliptic Frobenius count. -/
theorem zetaOfCounts_projectiveLineScheme_eq_zetaX {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F))
    (e : ∀ n, 0 < n → KPoints (projectiveLineToSpec F) (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n))
    {α β : ℂ}
    (hα : ‖α‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2))
    (hE : ∀ n, 0 < n → countSequence f (finiteExtensionFamily F p) n =
      (Nat.card F : ℂ) ^ n + 1 - α ^ n - β ^ n)
    {s : ℂ} (hs : 2 < s.re) :
    NLines.zetaOfCounts (Nat.card F)
        (countSequence (pullback.fst f (projectiveLineToSpec F) ≫ f)
          (finiteExtensionFamily F p)) s =
      NLines.zetaX (Nat.card F) α β s :=
  zetaOfCounts_finiteExtensions_eq_zetaX F p f (projectiveLineToSpec F) e hα hβ hE hs

end Zeta

end WeilRH.NLinesGeometry
