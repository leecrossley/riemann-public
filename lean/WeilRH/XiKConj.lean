/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.XiKStrip

/-!
# `ξ_K` is real: `ξ_K(s̄) = conj ξ_K(s)` (round 71)

The reflection principle for `ξ_K`, and its consequence `ord_{σ̄} ξ_K = ord_σ ξ_K`. This discharges
the conjugation hypothesis of `NCount.mult_conj` for `f = ξ_K`, completing `prop:N-count` (i)
(invariance of `Σ'` under `ρ ↦ ρ̄`) for `ξ_K`.

## Main results
* `analyticOrderAt_conj`: for an entire `f` with `f (conj z) = conj (f z)`, the order of `f` at
  `conj σ` equals its order at `σ`.
* `XiKConj.xi_conj`: `P.ξ (conj s) = conj (P.ξ s)` for every `s` (identity theorem from `Re s > 1`,
  where the Dirichlet series has real coefficients).
* `NCount.xi_conj`, `Hecke.nCount_conj`: the multiplicities of `Σ'` are invariant under `σ ↦ σ̄`
  (the latter CONDITIONAL on B1).
-/

open NumberField Complex Filter Topology ComplexConjugate

namespace WeilRH

/-- Reflection and order: if `f` is entire and `f (conj z) = conj (f z)`, then
`ord_{conj σ} f ≥ ord_σ f`. -/
lemma analyticOrderAt_le_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (σ : ℂ) :
    analyticOrderAt f σ ≤ analyticOrderAt f (conj σ) := by
  refine ENat.forall_natCast_le_iff_le.1 fun n hn => ?_
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt (hf.analyticAt σ)).1 hn
  refine (natCast_le_analyticOrderAt (hf.analyticAt (conj σ))).2 ⟨conj ∘ g ∘ conj, ?_, ?_⟩
  · rw [analyticAt_iff_eventually_differentiableAt] at hg ⊢
    have ht : Tendsto conj (𝓝 (conj σ)) (𝓝 σ) := by
      simpa using (Complex.continuous_conj.tendsto (conj σ))
    filter_upwards [ht.eventually hg] with w hw
    simpa using hw.conj_conj
  · have ht : Tendsto conj (𝓝 (conj σ)) (𝓝 σ) := by
      simpa using (Complex.continuous_conj.tendsto (conj σ))
    filter_upwards [ht.eventually hev] with w hw
    have h1 : f w = conj (f (conj w)) := by rw [hc, conj_conj]
    rw [h1, hw]
    simp [smul_eq_mul, map_mul, map_pow, map_sub]

/-- Reflection and order: if `f` is entire and `f (conj z) = conj (f z)`, then
`ord_{conj σ} f = ord_σ f`. -/
theorem analyticOrderAt_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (σ : ℂ) :
    analyticOrderAt f (conj σ) = analyticOrderAt f σ :=
  le_antisymm (by simpa using analyticOrderAt_le_conj hf hc (conj σ))
    (analyticOrderAt_le_conj hf hc σ)

theorem analyticOrderNatAt_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : ∀ z, f (conj z) = conj (f z)) (σ : ℂ) :
    analyticOrderNatAt f (conj σ) = analyticOrderNatAt f σ := by
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_conj hf hc]

end WeilRH

namespace WeilRH.XiKConj

variable {K : Type*} [Field K] [NumberField K] {C : DedekindContinuation K} (P : C.SimplePoles)

lemma natCast_cpow_conj (n : ℕ) (s : ℂ) : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
  rw [cpow_conj _ _ (by rw [natCast_arg]; exact Real.pi_ne_zero.symm), conj_natCast]

/-- `ζ_K(s̄) = conj ζ_K(s)`: the Dirichlet series of `ζ_K` has real coefficients. -/
theorem dedekindZeta_conj (s : ℂ) : dedekindZeta K (conj s) = conj (dedekindZeta K s) := by
  rw [DedekindZetaConv.dedekindZeta_eq, DedekindZetaConv.dedekindZeta_eq, LSeries, LSeries,
    conj_tsum]
  congr 1; funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, conj_ofReal,
      natCast_cpow_conj]

lemma conj_two : conj (2 : ℂ) = 2 := map_ofNat _ 2

lemma ofReal_cpow_conj {x : ℝ} (hx : 0 ≤ x) (w : ℂ) :
    (x : ℂ) ^ conj w = conj ((x : ℂ) ^ w) := by
  rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hx]; exact Real.pi_ne_zero.symm), conj_ofReal]

lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, show -(conj s) / 2 = conj (-s / 2) by rw [map_div₀, map_neg, conj_two],
    show conj s / 2 = conj (s / 2) by rw [map_div₀, conj_two], Gamma_conj, ofReal_cpow_conj Real.pi_pos.le]

lemma Gammaℂ_conj (s : ℂ) : Gammaℂ (conj s) = conj (Gammaℂ s) := by
  have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, Gamma_conj, this,
    show -(conj s) = conj (-s) by rw [map_neg], ofReal_cpow_conj (by positivity), conj_two]

lemma gammaFactor_conj (s : ℂ) :
    dedekindGammaFactor K (conj s) = conj (dedekindGammaFactor K s) := by
  have hd : ((|discr K| : ℤ) : ℂ) = (((|discr K| : ℤ) : ℝ) : ℂ) := (ofReal_intCast _).symm
  rw [dedekindGammaFactor, dedekindGammaFactor, map_mul, map_mul, map_pow, map_pow,
    Gammaℝ_conj, Gammaℂ_conj, hd, show conj s / 2 = conj (s / 2) by rw [map_div₀, conj_two],
    ofReal_cpow_conj (by positivity)]

/-- **`ξ_K(s̄) = conj ξ_K(s)`** for every `s`. -/
theorem xi_conj (s : ℂ) : P.ξ (conj s) = conj (P.ξ s) := by
  let g : ℂ → ℂ := conj ∘ P.ξ ∘ conj
  have hg : Differentiable ℂ g := fun z => by
    simpa [g] using (P.differentiable (conj z)).conj_conj
  have hR : ∀ z : ℂ, 1 < z.re → g z = P.ξ z := by
    intro z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    have h0 : ∀ w : ℂ, 1 < w.re → w ≠ 0 := fun w hw h => by rw [h] at hw; norm_num at hw
    have h1 : ∀ w : ℂ, 1 < w.re → w ≠ 1 := fun w hw h => by rw [h] at hw; norm_num at hw
    simp only [g, Function.comp_apply]
    rw [P.eq_xiK _ (h0 _ hz') (h1 _ hz'), P.eq_xiK _ (h0 _ hz) (h1 _ hz), xiK, xiK,
      C.eq_of_one_lt_re _ hz', C.eq_of_one_lt_re _ hz, gammaFactor_conj, dedekindZeta_conj]
    simp only [map_mul, map_sub, map_one, conj_conj]
  have hev : g =ᶠ[𝓝 2] P.ξ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact hR z hz
  have heq : g = P.ξ := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hg.analyticAt z)
    (fun z _ => P.differentiable.analyticAt z) hev
  have := congrFun heq (conj s)
  simp only [g, Function.comp_apply, conj_conj] at this
  rw [← this]

/-- `ord_{σ̄} ξ_K = ord_σ ξ_K`. -/
theorem analyticOrderNatAt_xi_conj (σ : ℂ) :
    analyticOrderNatAt P.ξ (conj σ) = analyticOrderNatAt P.ξ σ :=
  analyticOrderNatAt_conj P.differentiable (xi_conj P) σ

end WeilRH.XiKConj

namespace WeilRH

variable {K : Type} [Field K] [NumberField K] {C : DedekindContinuation K} (P : C.SimplePoles)

/-- **`prop:N-count` (i)**, conjugation clause, for `ξ_K`: the multiplicities of `Σ'` are
invariant under `σ ↦ σ̄`. -/
theorem NCount.xi_conj (σ : ℂ) :
    Module.rank ℂ ((TrivialModel.theta (NCount.family' P.ξ)).maxGenEigenspace (conj σ)) =
      Module.rank ℂ ((TrivialModel.theta (NCount.family' P.ξ)).maxGenEigenspace σ) :=
  NCount.mult_conj P.differentiable P.one_sub P.xi_one_ne_zero
    (XiKConj.analyticOrderNatAt_xi_conj P) σ

/-- **`prop:N-count` (i)**, conjugation clause, for every number field, CONDITIONAL on B1. -/
theorem Hecke.nCount_conj (hB : HeckePackage K) (σ : ℂ) :
    Module.rank ℂ ((TrivialModel.theta (NCount.family' (Hecke.xi hB))).maxGenEigenspace (conj σ)) =
      Module.rank ℂ ((TrivialModel.theta (NCount.family' (Hecke.xi hB))).maxGenEigenspace σ) :=
  NCount.xi_conj hB.simplePoles σ

/-- **`ξ_K(s̄) = conj ξ_K(s)`** for every number field, CONDITIONAL on B1. -/
theorem Hecke.xi_conj (hB : HeckePackage K) (s : ℂ) :
    Hecke.xi hB (conj s) = conj (Hecke.xi hB s) :=
  XiKConj.xi_conj hB.simplePoles s

end WeilRH
