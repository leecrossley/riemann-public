import WeilRH.CompactifiedScheme

/-!
# Evaluation topology on the complex points of `Spec 𝓞_K`

Gillet–Soulé, *Arithmetic intersection theory* (1990), Definition 3.2.1, equips `X_∞` with
its complex analytic topology and requires `F_∞` to be continuous. For `X = Spec 𝓞_K`, the
complex points are the finitely many embeddings `K →+* ℂ`. We put the pointwise evaluation
topology on those embeddings and transport it through `complexPointsSpecEquiv`.

The pointwise topology is discrete, so conjugation is continuous. This treats the
zero-dimensional topological case. The comparison with the analytic topology of a base-changed
scheme is not yet formalized. AxiomMath/Weil, `Weil/Definitions.lean` and
`Weil/Defs/AlgebraicGeometry/ComplexPoints/AnalyticTopology.lean` at commit
`27cdb2049be62ee2911429b47f54774078450e32`, provides a general scheme topology that could
support that comparison under a compatible Lean and Mathlib pin.
-/

open Topology

namespace WeilRH.Arakelov.ArithmeticVariety

variable (K : Type) [Field K] [NumberField K]

/-- The pointwise evaluation topology on the embeddings of a number field in `ℂ`. -/
noncomputable abbrev embeddingsTopology : TopologicalSpace (K →+* ℂ) :=
  TopologicalSpace.induced (fun φ : K →+* ℂ => (φ : K → ℂ)) inferInstance

/-- The pointwise topology on the finitely many complex embeddings is discrete. -/
theorem embeddingsTopology_discrete :
    @DiscreteTopology (K →+* ℂ) (embeddingsTopology K) := by
  letI : TopologicalSpace (K →+* ℂ) := embeddingsTopology K
  have hi : Function.Injective (fun φ : K →+* ℂ => (φ : K → ℂ)) := by
    intro φ ψ h
    exact RingHom.ext (congrFun h)
  have he : IsEmbedding (fun φ : K →+* ℂ => (φ : K → ℂ)) :=
    hi.isEmbedding_induced
  haveI : T1Space (K →+* ℂ) := he.t1Space
  infer_instance

/-- The topology on `X_∞` of `Spec 𝓞_K` transported from pointwise evaluation of embeddings. -/
noncomputable abbrev complexPointsSpecTopology :
    TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
  TopologicalSpace.induced (complexPointsSpecEquiv K) (embeddingsTopology K)

/-- The transported topology on `X_∞` of `Spec 𝓞_K` is discrete. -/
theorem complexPointsSpecTopology_discrete :
    @DiscreteTopology (base (ArithmeticRing.ringOfIntegers K)).complexPoints
      (complexPointsSpecTopology K) := by
  letI : TopologicalSpace (K →+* ℂ) := embeddingsTopology K
  letI : TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    complexPointsSpecTopology K
  haveI : DiscreteTopology (K →+* ℂ) := embeddingsTopology_discrete K
  haveI : T1Space (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    (complexPointsSpecEquiv K).injective.isEmbedding_induced.t1Space
  letI : Fintype (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    Fintype.ofEquiv _ (complexPointsSpecEquiv K).symm
  infer_instance

/-- The equivalence between `X_∞` and embeddings is a homeomorphism for the evaluation
topologies. -/
noncomputable def complexPointsSpecHomeomorph :
    letI : TopologicalSpace (K →+* ℂ) := embeddingsTopology K
    letI : TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
      complexPointsSpecTopology K
    (base (ArithmeticRing.ringOfIntegers K)).complexPoints ≃ₜ (K →+* ℂ) := by
  letI : TopologicalSpace (K →+* ℂ) := embeddingsTopology K
  letI : TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    complexPointsSpecTopology K
  haveI : DiscreteTopology (K →+* ℂ) := embeddingsTopology_discrete K
  haveI : DiscreteTopology (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    complexPointsSpecTopology_discrete K
  exact (complexPointsSpecEquiv K).toHomeomorphOfDiscrete

/-- The complex-conjugation involution `F_∞` is continuous on `Spec 𝓞_K`'s complex points for
the transported evaluation topology (the zero-dimensional case of GS 3.2.1). -/
theorem complexPointsSpec_Finf_continuous :
    letI : TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
      complexPointsSpecTopology K
    Continuous ((base (ArithmeticRing.ringOfIntegers K)).Finf) := by
  letI : TopologicalSpace (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    complexPointsSpecTopology K
  haveI : DiscreteTopology (base (ArithmeticRing.ringOfIntegers K)).complexPoints :=
    complexPointsSpecTopology_discrete K
  exact continuous_of_discreteTopology

end WeilRH.Arakelov.ArithmeticVariety

namespace WeilRH.Arakelov.Xbar

variable (K : Type) [Field K] [NumberField K]

/-- The evaluation topology on the complex points of the manuscript's `X̄_K`. -/
noncomputable abbrev pointsTopology : TopologicalSpace (points (S K)) :=
  TopologicalSpace.induced (pointsEquiv K) (ArithmeticVariety.embeddingsTopology K)

/-- The complex points of `X̄_K` are discrete in the evaluation topology. -/
theorem pointsTopology_discrete : @DiscreteTopology (points (S K)) (pointsTopology K) := by
  letI : TopologicalSpace (K →+* ℂ) := ArithmeticVariety.embeddingsTopology K
  letI : TopologicalSpace (points (S K)) := pointsTopology K
  haveI : DiscreteTopology (K →+* ℂ) := ArithmeticVariety.embeddingsTopology_discrete K
  haveI : T1Space (points (S K)) := (pointsEquiv K).injective.isEmbedding_induced.t1Space
  infer_instance

/-- `X̄_K(ℂ)` is homeomorphic to the embeddings of `K` in `ℂ`, both with evaluation topology. -/
noncomputable def pointsHomeomorph :
    letI : TopologicalSpace (K →+* ℂ) := ArithmeticVariety.embeddingsTopology K
    letI : TopologicalSpace (points (S K)) := pointsTopology K
    points (S K) ≃ₜ (K →+* ℂ) := by
  letI : TopologicalSpace (K →+* ℂ) := ArithmeticVariety.embeddingsTopology K
  letI : TopologicalSpace (points (S K)) := pointsTopology K
  haveI : DiscreteTopology (K →+* ℂ) := ArithmeticVariety.embeddingsTopology_discrete K
  haveI : DiscreteTopology (points (S K)) := pointsTopology_discrete K
  exact (pointsEquiv K).toHomeomorphOfDiscrete

/-- Complex conjugation on the manuscript's `X̄_K(ℂ)` is continuous for the evaluation topology. -/
theorem Finf_continuous :
    letI : TopologicalSpace (points (S K)) := pointsTopology K
    Continuous (fun x : points (S K) => Finf x) := by
  letI : TopologicalSpace (points (S K)) := pointsTopology K
  haveI : DiscreteTopology (points (S K)) := pointsTopology_discrete K
  exact continuous_of_discreteTopology

end WeilRH.Arakelov.Xbar
