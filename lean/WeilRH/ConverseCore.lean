/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Multiplicities
import WeilRH.Suspension

/-!
# `prop:converse`: RH as the existence of a positive spectral core

Source: `latex/notes.tex`, `prop:converse` (claim C-CONV), with `def:spectral-core` and
`def:inf-pol`. The following are equivalent:

(i) the Riemann hypothesis;
(ii) there is a spectral core `(V, Θ)` with a positive infinitesimal polarization of weight one
such that `spec Θ` with multiplicities is the multiset of nontrivial zeros of `ζ`.

Here (ii) is the structure `PositiveZetaCore`: a complex vector space `V`, `Θ : End V` with
`Spectral.SpectralCore Θ` (`def:spectral-core` (b)), a `PosHermForm` `h` with
`Suspension.IsInfPol h Θ 1` (`def:inf-pol`, `j = 1`), and `Spectral.mult Θ ρ = ord_ρ ξ` for every
`ρ ∈ ℂ` (`def:spectral-core` (c)), where `ord_ρ ξ = analyticOrderNatAt completedXi ρ` is positive
exactly at the nontrivial zeros (`analyticOrderNatAt_completedXi_pos_iff`).

Main results:
* `WeilRH.ArithmeticWeilCohomologyQMult.spectralCore`: the multiplicity-faithful degree-one
  structure is a spectral core (the zeros of the entire `ξ ≢ 0` have no finite accumulation point);
* `WeilRH.riemannHypothesis_iff_nonempty_positiveZetaCore` (`prop:converse`).
-/

open Module Complex ComplexConjugate Filter Topology
open scoped InnerProductSpace

namespace WeilRH

/-- The zeros of `ξ` have no finite accumulation point. -/
theorem not_accPt_zeros_completedXi (z : ℂ) :
    ¬ AccPt z (𝓟 {ρ | completedXi ρ = 0}) := by
  intro h
  rw [accPt_iff_frequently_nhdsNE] at h
  have hξ : AnalyticOnNhd ℂ completedXi Set.univ := fun s _ => analyticAt_completedXi s
  have := hξ.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) h
  exact completedXi_ne_zero_somewhere (this (Set.mem_univ 0))

/-- The positive definite Hermitian form `h(u, v) = ⟪v, u⟫` of an inner product space. -/
noncomputable def PosHermForm.ofInner (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : PosHermForm E where
  toFun := hForm
  add_left u u' v := by simp [hForm_def]
  smul_left c u v := by simp [hForm_def]
  conj_symm u v := by simp [hForm_def]
  re_pos u hu := by
    rw [hForm_def]
    simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hu

namespace ArithmeticWeilCohomologyQMult

variable (H : ArithmeticWeilCohomologyQMult)

/-- The generalized eigenspace of `Θ` restricted to an invariant subspace lies in that of `Θ`. -/
lemma map_maxGenEigenspace_restrict_le {W : Submodule ℂ H.V} (hW : ∀ x ∈ W, H.Θ x ∈ W)
    (ρ : ℂ) :
    (Module.End.maxGenEigenspace (H.Θ.restrict hW) ρ).map W.subtype ≤ H.Θ.maxGenEigenspace ρ := by
  rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict _ _ _ _ hW,
    Submodule.map_comap_subtype]
  exact inf_le_right

/-- **The multiplicity-faithful degree-one structure is a spectral core** (`def:spectral-core`
(b)): `V` is spanned by generalized eigenspaces (AW1's finite-dimensional blocks over `ℂ`), each is
finite-dimensional, and `spec Θ` is the zero set of `ξ`, which has no finite accumulation point. -/
theorem spectralCore : Spectral.SpectralCore H.Θ where
  iSup_eq_top := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨W, hvW, hfin, hinv⟩ := H.locallyFinite v
    have hW : ∀ x ∈ W, H.Θ x ∈ W := fun x hx => hinv hx
    have htop := Module.End.iSup_maxGenEigenspace_eq_top (H.Θ.restrict hW)
    have hv : (⟨v, hvW⟩ : W) ∈ ⨆ ρ, Module.End.maxGenEigenspace (H.Θ.restrict hW) ρ := by
      rw [htop]; trivial
    have := Submodule.mem_map_of_mem (f := W.subtype) hv
    rw [Submodule.map_iSup] at this
    exact (iSup_mono fun ρ => H.map_maxGenEigenspace_restrict_le hW ρ) this
  finiteDimensional ρ := by
    rw [maxGenEigenspace_eq_eigenspace_of_P H.Θ 1 H.P' ρ]
    exact H.finiteDimensional_eigenspace ρ
  noAccPt z := by
    have : Spectral.spec H.Θ = {ρ | completedXi ρ = 0} := by
      ext ρ
      have := H.finiteDimensional_eigenspace ρ
      simp only [Spectral.spec, Set.mem_ofPred_eq]
      rw [completedXi_eq_zero_iff, ← analyticOrderNatAt_completedXi_pos_iff,
        maxGenEigenspace_eq_eigenspace_of_P H.Θ 1 H.P' ρ, ← Submodule.one_le_finrank_iff,
        H.finrank_eigenspace]
      rfl
    rw [this]
    exact not_accPt_zeros_completedXi z

end ArithmeticWeilCohomologyQMult

/-- **`prop:converse` (ii).** A spectral core `(V, Θ)` with a positive infinitesimal polarization
of weight one whose spectrum with multiplicities is the multiset of nontrivial zeros of `ζ`:
`m(ρ) = dim V_{Θ∼ρ} = ord_ρ ξ` for every `ρ ∈ ℂ`. -/
structure PositiveZetaCore where
  /-- The underlying complex vector space. -/
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℂ V]
  /-- The generator. -/
  Θ : Module.End ℂ V
  /-- `(V, Θ)` is a spectral core. -/
  spectralCore : Spectral.SpectralCore Θ
  /-- The positive definite Hermitian form. -/
  h : PosHermForm V
  /-- `h(Θu, v) + h(u, Θv) = h(u, v)`. -/
  isInfPol : Suspension.IsInfPol h Θ 1
  /-- The multiplicity of every `ρ` is the zero order of `ξ` at `ρ`. -/
  mult_eq : ∀ ρ : ℂ, Spectral.mult Θ ρ = analyticOrderNatAt completedXi ρ

attribute [instance] PositiveZetaCore.instAddCommGroup PositiveZetaCore.instModule

/-- `(ii) ⇒ (i)` of `prop:converse`, via `prop:purity`. -/
theorem PositiveZetaCore.riemannHypothesis (C : PositiveZetaCore) : RiemannHypothesis := by
  intro s hs htriv hs1
  have hpos : 0 < Spectral.mult C.Θ s := by
    rw [C.mult_eq]; exact (analyticOrderNatAt_completedXi_pos_iff s).2 ⟨hs, htriv, hs1⟩
  have hne : C.Θ.maxGenEigenspace s ≠ ⊥ := by
    intro h0
    rw [Spectral.mult, h0, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  have hev : C.Θ.HasEigenvalue s :=
    (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (k := ⊤) (by simp)).1 hne
  simpa using C.h.re_eq_half C.Θ 1 C.isInfPol hev

/-- `(i) ⇒ (ii)` of `prop:converse`: the diagonal model with multiplicities. -/
noncomputable def positiveZetaCore (hRH : RiemannHypothesis) : PositiveZetaCore :=
  let H := multDiagonalModel hRH
  { V := H.V
    Θ := H.Θ
    spectralCore := H.spectralCore
    h := PosHermForm.ofInner H.V
    isInfPol := fun u v => by simpa [PosHermForm.ofInner] using H.P u v
    mult_eq := H.finrank_maxGenEigenspace }

/-- **`prop:converse`.** RH holds iff there is a spectral core with a positive infinitesimal
polarization of weight one whose spectrum with multiplicities is the multiset of nontrivial zeros
of `ζ`. -/
theorem riemannHypothesis_iff_nonempty_positiveZetaCore :
    RiemannHypothesis ↔ Nonempty PositiveZetaCore :=
  ⟨fun hRH => ⟨positiveZetaCore hRH⟩, fun ⟨C⟩ => C.riemannHypothesis⟩

end WeilRH
