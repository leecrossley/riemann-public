/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.BlackBoxes
import WeilRH.ContentXiK
import WeilRH.NCount
import WeilRH.MainGeneral
import WeilRH.ArakelovZeta
import WeilRH.ZetaOrder
import WeilRH.CompactifiedZero
import WeilRH.DedekindLocal
import WeilRH.HodgeProj

/-!
# Hecke-conditional results for every number field (round 68)

Until round 68 every result about `Λ_K` or `ξ_K` for a general number field took Hecke's
continuation as data (`C : DedekindContinuation K`) and its simple poles as data
(`P : C.SimplePoles`); both were constructed only for `K = ℚ`. Here each such headline result is
restated for every `K : Type` under the single black box `HeckePackage K`
(`WeilRH/BlackBoxes.lean`), through `HeckePackage.continuation` and `HeckePackage.simplePoles`.
The original hypothesis-form theorems are kept. Every result below is CONDITIONAL on
`HeckePackage K`, which appears as an explicit hypothesis `hB`.

Manuscript labels (`latex/notes.tex`): `prop:xiK`, `prop:content` (i), (iv), `prop:N-count` (i),
`thm:main-number-fields` (first sentence), `thm:A` (i); and Flach–Morin's Prop. 4.14 for `X̄_K`
(`n = 0`, `n = 1`, `n < 0`), with the comparison `ζ(X̄_K, s) = e^{a+bs} Λ_K(s)`.
-/

universe u

open NumberField Complex

namespace WeilRH.Hecke

variable {K : Type} [Field K] [NumberField K] (hB : HeckePackage K)

/-- The entire `ξ_K` supplied by B1. -/
noncomputable abbrev xi : ℂ → ℂ := hB.simplePoles.ξ

/-- **`prop:xiK`** for every number field, conditional on B1: `ξ_K` is entire, `ξ_K(1-s) = ξ_K(s)`,
`ξ_K(0) ξ_K(1) ≠ 0`, its zeros are exactly the nontrivial zeros of `Λ_K`, it agrees with
`s(s-1)Λ_K(s)` for any continuation `C` of `Λ_K` off `{0, 1}`, and it has order at most one. -/
theorem xiK :
    Differentiable ℂ (xi hB) ∧ (∀ s, xi hB (1 - s) = xi hB s) ∧ xi hB 0 ≠ 0 ∧ xi hB 1 ≠ 0 ∧
      (∀ ρ, xi hB ρ = 0 ↔ hB.continuation.Λ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1) ∧
      (∀ (C : DedekindContinuation K) (s : ℂ), s ≠ 0 → s ≠ 1 → xi hB s = xiK C s) ∧
      ∃ c : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖xi hB s‖ ≤ c * ‖s‖ * Real.log ‖s‖ := by
  refine ⟨hB.simplePoles.differentiable, hB.simplePoles.one_sub, hB.simplePoles.xi_zero_ne_zero,
    hB.simplePoles.xi_one_ne_zero, hB.simplePoles.xi_eq_zero_iff, fun C s h0 h1 => ?_,
    hB.growth⟩
  show hB.simplePoles.ξ s = _
  rw [hB.simplePoles.eq_xiK s h0 h1]
  exact xiK_eqOn _ C h0 h1

/-- **`prop:content` (i)** (degree one) for every number field, conditional on B1. -/
theorem content_free :
    WeilRH.Spectral.SpectralCore (TrivialModel.theta (xiFamily hB.simplePoles)) ∧
      ∀ σ, Module.rank ℂ ((TrivialModel.theta (xiFamily hB.simplePoles)).maxGenEigenspace σ) =
        analyticOrderNatAt (xi hB) σ :=
  WeilRH.content_free hB.simplePoles

/-- **`prop:content` (iv)** (degree one) for every number field, conditional on B1: a positive
Weil datum of type `(1, 0)` in degree one with `Sp_1 = div ξ_K` exists iff GRH holds for `ζ_K`. -/
theorem content_iff :
    (∃ (V W T : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W)
      (_ : Module ℂ W) (_ : AddCommGroup T) (_ : Module ℂ T)
      (D : WeightedStarDatum 1 0 1 V W T), D.IsPositive ∧
        ∀ σ, Module.rank ℂ (D.ΘV.maxGenEigenspace σ) = analyticOrderNatAt (xi hB) σ) ↔
      ∀ ρ, xi hB ρ = 0 → ρ.re = 1 / 2 :=
  WeilRH.content_iff hB.simplePoles

/-- **`prop:N-count` (i)** for `ξ_K` and every number field, conditional on B1. -/
theorem nCount :
    Spectral.SpectralCore (TrivialModel.theta (NCount.family' (xi hB))) ∧
      (∀ σ, Module.rank ℂ ((TrivialModel.theta (NCount.family' (xi hB))).maxGenEigenspace σ) =
        analyticOrderNatAt (xi hB) σ + Cardinal.mk {i // TrivialModel.lam NCount.added i = σ}) ∧
      (∀ σ, Module.rank ℂ
          ((TrivialModel.theta (NCount.family' (xi hB))).maxGenEigenspace (1 - σ)) =
        Module.rank ℂ ((TrivialModel.theta (NCount.family' (xi hB))).maxGenEigenspace σ)) ∧
      (∀ T : ℝ, 1 ≤ T →
        Cardinal.mk {i // 0 < (TrivialModel.lam (NCount.family' (xi hB)) i).im ∧
          (TrivialModel.lam (NCount.family' (xi hB)) i).im ≤ T} =
        Cardinal.mk {i // 0 < (TrivialModel.lam (SymEntire.family (xi hB)) i).im ∧
          (TrivialModel.lam (SymEntire.family (xi hB)) i).im ≤ T} + ⌊Real.log T⌋₊) :=
  WeilRH.NCount.xi hB.simplePoles

/-- **`thm:main-number-fields`, first sentence**, for every number field, conditional on B1: a
polarized graded spectral realization of `Λ_K` of type `(1, 0)` forces every nontrivial zero of
`ζ_K` onto `Re s = 1/2`. -/
theorem re_eq_half_of_realization {R : MainGeneral.GradedRealization.{u} 1 0 hB.continuation.Λ}
    (Q : MainGeneral.Polarization R) (e0 : R.V 0 ≃ₗ[ℂ] ℂ) (e2 : R.V 2 ≃ₗ[ℂ] ℂ) {ρ : ℂ}
    (hρ : xi hB ρ = 0) : ρ.re = 1 / 2 :=
  MainGeneral.re_eq_half_of_xi_eq_zero hB.simplePoles Q e0 e2 hρ

/-- **`thm:A` (i), objectwise**, conditional on B1: an `ArithmeticWeilCohomology` for `Λ_K` gives
GRH for `ζ_K`. -/
theorem grh_of_awc (H : ArithmeticWeilCohomology (dedekindDatum K hB.continuation)) :
    ∀ ρ, xi hB ρ = 0 → ρ.re = 1 / 2 := fun ρ hρ => by
  obtain ⟨h, h0, h1⟩ := (hB.simplePoles.xi_eq_zero_iff ρ).1 hρ
  exact grh_dedekind_of_awc_object _ H ρ h h0 h1

/-- **FM: `ζ(X̄_K, s) = e^{a+bs} Λ_K(s)`** on `Re s > 1`, conditional on B1. -/
theorem zetaFM_eq {s : ℂ} (hs : 1 < s.re) :
    Arakelov.zetaFM K s = exp (Arakelov.fmA K + Arakelov.fmB K * s) * hB.continuation.Λ s :=
  Arakelov.zetaFM_eq K hB.continuation hs

/-- **FM's completed `ζ(ℙ̄ⁿ_{𝓞_K}, s)`** on `Re s > n + 1`, conditional on B1. -/
theorem zetaFM_proj_eq (n : ℕ) {s : ℂ} (hs : (n : ℝ) + 1 < s.re) :
    Arakelov.ProjSpace.zetaFMPn K n s = ∏ k ∈ Finset.range (n + 1),
      exp (Arakelov.fmA K + Arakelov.fmB K * (s - k)) * hB.continuation.Λ (s - k) :=
  Arakelov.ProjSpace.zetaFM_eq K n hB.continuation hs

/-- **FM Prop. 4.14 (iii) at `n = 1` for `X̄_K`**, conditional on B1. -/
theorem fm414_one :
    meromorphicOrderAt (Arakelov.zetaFMCont K hB.continuation) 1 =
        (-(Module.finrank ℝ (Arakelov.ArithChowReal.ChowR K) : ℤ) : ℤ) ∧
      meromorphicOrderAt (Arakelov.zetaFMCont K hB.continuation) 1 =
        (-(Module.finrank ℝ (Arakelov.hBar 2) : ℤ) : ℤ) :=
  Arakelov.ZetaOrder.fm414_iii K hB.simplePoles

/-- **FM Prop. 4.14 (iii) at `n = 0` for `X̄_K`**, conditional on B1. -/
theorem fm414_zero :
    meromorphicOrderAt (Arakelov.zetaFMCont K hB.continuation) 0 =
        (-(Module.finrank ℝ (Arakelov.TwistZero.harZero 0) : ℤ) : ℤ) ∧
      meromorphicOrderAt (Arakelov.zetaFMCont K hB.continuation) 0 =
        (-(Module.finrank ℝ (Arakelov.TwistZero.hBar0 0) : ℤ) : ℤ) :=
  Arakelov.TwistZero.fm414_zero K hB.simplePoles

/-- **FM Prop. 4.14 at every `n < 0` for `X̄_K`**, conditional on B1. -/
theorem fm414_neg {n : ℤ} (hn : n < 0) :
    (∀ i : ℤ, Module.finrank ℝ (Arakelov.TwistNeg.harNeg i) = 0) ∧
      meromorphicOrderAt (Arakelov.zetaFMCont K hB.continuation) (n : ℂ) =
        (-(Module.finrank ℝ (Arakelov.TwistNeg.harNeg (2 * n)) : ℤ) : ℤ) :=
  DedekindLocal.fm414_neg' hB.simplePoles hn

end WeilRH.Hecke
