/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Spectral
import WeilRH.WeilConverse
import WeilRH.Calibration

/-!
# Logarithmic suspension (`notes.tex`, §"Logarithmic suspension")

Round 6 of the formalization had only the semisimple, one-copy-per-`k` model of the suspension
(`WeilRH.suspension` in `Calibration.lean`, Q2 Definition 6.1). This file builds the manuscript's
full object of `def:log-susp`: the algebraic direct sum
`V̂ = ⨁_{ρ : q^ρ ∈ spec F} V_{(q^ρ)}` with `Θ = ρ + (log q)⁻¹ N_{q^ρ}` on the summand `V̂_ρ`, where
`N_α = log(α⁻¹F)` is the (finite) logarithm series on the generalized eigenspace `V_{(α)}`.

## Main results

* `WeilRH.Suspension.mem_logSusp_iff_zero` and `hasDerivAt_one_sub` (`prop:suspension` (i), first
  clause): the zeros of `s ↦ 1 - α q^{-s}` are exactly `Σ_q(α)`, each simple.
* `WeilRH.Suspension.spectralCore_theta` (`prop:suspension` (ii)): `(V̂, Θ)` is a spectral core, with
  `maxGenEigenspace_theta` (`V̂_{Θ∼ρ} = V̂_ρ`), `spec_theta` and `mult_theta`
  (`dim V̂_{Θ∼ρ} = dim V_{(q^ρ)}`).
* `WeilRH.Suspension.det_one_sub_smul_eq_prod`, `analyticOrderAt_det` (`prop:suspension` (i), last
  clause): `det(1 - F q^{-s}) = ∏_α (1 - α q^{-s})^{dim V_{(α)}}`, and its zero order at every `ρ`
  is the algebraic multiplicity `mult Θ ρ`.
* `WeilRH.Suspension.isInfPol_suspForm` (`prop:suspension` (iii)): a positive Frobenius polarization
  of weight `j` suspends to a positive infinitesimal polarization of weight `j`.
* `WeilRH.Suspension.re_eq_of_mem_spec`, `iSup_eigenspace_theta` (`prop:suspension` (iv)).

The construction is generic: `diag` is a block-diagonal operator on a direct sum whose `i`-th block
is `c i` plus a nilpotent map, and `spectralCore_diag` shows such an operator is a spectral core as
soon as `c` is injective with discrete range. This also shows `SpectralCore` is not vacuous.
-/

open Module Complex Filter Topology
open scoped ComplexConjugate DirectSum

namespace WeilRH.Suspension

open WeilRH.Spectral

/-! ### Block-diagonal operators on a direct sum -/

section Diagonal

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module ℂ (M i)]

/-- The block-diagonal operator `⨁ T_i` on `⨁ M_i`. -/
noncomputable def diag (T : ∀ i, Module.End ℂ (M i)) : Module.End ℂ (⨁ i, M i) :=
  DirectSum.lmap T

omit [DecidableEq ι] in
lemma diag_apply (T : ∀ i, Module.End ℂ (M i)) (x : ⨁ i, M i) (i : ι) :
    diag T x i = T i (x i) :=
  DirectSum.lmap_apply T x i

omit [DecidableEq ι] in
lemma diag_sub_pow_apply (T : ∀ i, Module.End ℂ (M i)) (ρ : ℂ) (k : ℕ) (x : ⨁ i, M i)
    (i : ι) : (((diag T - ρ • 1) ^ k) x) i = ((T i - ρ • 1) ^ k) (x i) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1

variable (c : ι → ℂ) (T : ∀ i, Module.End ℂ (M i))

/-- If `T_i - c_i` is nilpotent for every `i` and `c` is injective, the generalized
`ρ`-eigenspace of `⨁ T_i` consists of the vectors supported on the (at most one) index with
`c i = ρ`. -/
theorem mem_maxGenEigenspace_diag (hc : Function.Injective c)
    (hT : ∀ i, IsNilpotent (T i - c i • 1)) (ρ : ℂ) (x : ⨁ i, M i) :
    x ∈ (diag T).maxGenEigenspace ρ ↔ ∀ i, c i ≠ ρ → x i = 0 := by
  rw [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩ i hi
    have h1 : ((T i - ρ • 1) ^ k) (x i) = 0 := by
      rw [← diag_sub_pow_apply, hk, DirectSum.zero_apply]
    have hu : IsUnit (T i - ρ • 1) := by
      have : T i - ρ • 1 = (c i - ρ) • (1 : Module.End ℂ (M i)) + (T i - c i • 1) := by
        rw [sub_smul]; abel
      rw [this]
      refine (hT i).isUnit_add_left_of_commute ?_ ?_
      · rw [← Algebra.algebraMap_eq_smul_one]
        exact (sub_ne_zero.mpr hi).isUnit.map _
      · exact (Commute.one_right _).smul_right _
    have hinj := ((Module.End.isUnit_iff _).mp (hu.pow k)).1
    exact hinj (h1.trans (map_zero _).symm)
  · intro hx
    by_cases h : ∃ i, c i = ρ
    · obtain ⟨i0, rfl⟩ := h
      obtain ⟨n, hn⟩ := hT i0
      refine ⟨n, DirectSum.ext fun i => ?_⟩
      rw [diag_sub_pow_apply]
      by_cases hi : i = i0
      · subst hi; rw [hn]; simp
      · rw [hx i (fun h => hi (hc h))]; simp
    · refine ⟨0, DirectSum.ext fun i => ?_⟩
      rw [diag_sub_pow_apply, hx i (fun h' => h ⟨i, h'⟩)]; simp

/-- The generalized eigenspaces of `⨁ T_i` span `⨁ M_i`. -/
theorem iSup_maxGenEigenspace_diag (hc : Function.Injective c)
    (hT : ∀ i, IsNilpotent (T i - c i • 1)) : ⨆ ρ, (diag T).maxGenEigenspace ρ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of i y =>
    refine Submodule.mem_iSup_of_mem (c i) ((mem_maxGenEigenspace_diag c T hc hT _ _).2 ?_)
    intro j hj
    exact DirectSum.of_eq_of_ne _ _ _ (fun h => hj (h ▸ rfl))
  | add x y hx hy => exact add_mem hx hy

/-- A generalized eigenvalue of `⨁ T_i` is one of the `c i`. -/
theorem spec_diag_subset (hc : Function.Injective c) (hT : ∀ i, IsNilpotent (T i - c i • 1)) :
    spec (diag T) ⊆ Set.range c := by
  intro ρ hρ
  by_contra h
  apply hρ
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact DirectSum.ext fun i =>
    (mem_maxGenEigenspace_diag c T hc hT ρ x).1 hx i (fun h' => h ⟨i, h'⟩)

/-- The component at `i` identifies `V_{⨁T∼c i}` with `M i`. -/
noncomputable def maxGenEigenspaceDiagEquiv (hc : Function.Injective c)
    (hT : ∀ i, IsNilpotent (T i - c i • 1)) (i : ι) :
    (diag T).maxGenEigenspace (c i) ≃ₗ[ℂ] M i :=
  LinearEquiv.ofBijective ((DirectSum.component ℂ ι M i).comp (Submodule.subtype _)) <| by
    constructor
    · intro x y hxy
      have hxy' : (x : ⨁ i, M i) i = (y : ⨁ i, M i) i := hxy
      apply Subtype.ext
      refine DirectSum.ext fun j => ?_
      by_cases hj : j = i
      · subst hj; exact hxy'
      · have hne : c j ≠ c i := fun h => hj (hc h)
        rw [(mem_maxGenEigenspace_diag c T hc hT _ _).1 x.2 j hne,
          (mem_maxGenEigenspace_diag c T hc hT _ _).1 y.2 j hne]
    · intro y
      refine ⟨⟨DirectSum.lof ℂ ι M i y, (mem_maxGenEigenspace_diag c T hc hT _ _).2 ?_⟩, ?_⟩
      · intro j hj
        exact DirectSum.of_eq_of_ne _ _ _ (fun h => hj (h ▸ rfl))
      · simp [DirectSum.component.lof_self]

/-- `dim V_{⨁T∼c i} = dim M i`. -/
theorem mult_diag (hc : Function.Injective c) (hT : ∀ i, IsNilpotent (T i - c i • 1)) (i : ι) :
    mult (diag T) (c i) = finrank ℂ (M i) :=
  (maxGenEigenspaceDiagEquiv c T hc hT i).finrank_eq

/-- **A spectral core from blocks.** If every `M i` is finite-dimensional, `T_i - c_i` is
nilpotent, `c` is injective and `range c` has no finite accumulation point, then `(⨁ M_i, ⨁ T_i)`
is a spectral core (`def:spectral-core`). -/
theorem spectralCore_diag [∀ i, FiniteDimensional ℂ (M i)] (hc : Function.Injective c)
    (hT : ∀ i, IsNilpotent (T i - c i • 1)) (hdisc : ∀ z : ℂ, ¬ AccPt z (𝓟 (Set.range c))) :
    SpectralCore (diag T) where
  iSup_eq_top := iSup_maxGenEigenspace_diag c T hc hT
  finiteDimensional ρ := by
    by_cases h : ∃ i, c i = ρ
    · obtain ⟨i, rfl⟩ := h
      exact LinearEquiv.finiteDimensional (maxGenEigenspaceDiagEquiv c T hc hT i).symm
    · refine Module.Finite.of_injective (0 : (diag T).maxGenEigenspace ρ →ₗ[ℂ] ℂ) ?_
      intro x y _
      have hz : ∀ z : (diag T).maxGenEigenspace ρ, z = 0 := fun z => Subtype.ext <|
        DirectSum.ext fun i =>
          (mem_maxGenEigenspace_diag c T hc hT ρ z).1 z.2 i (fun h' => h ⟨i, h'⟩)
      rw [hz x, hz y]
  noAccPt z hz := hdisc z (hz.mono (principal_mono.2 (spec_diag_subset c T hc hT)))

end Diagonal

/-! ### The logarithmic suspension -/

section Suspension

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- `q^ρ = e^{ρ log q}` with `log q ∈ ℝ`. -/
noncomputable def qpow (q : ℝ) (ρ : ℂ) : ℂ := cexp ((Real.log q : ℂ) * ρ)

lemma qpow_ne_zero (q : ℝ) (ρ : ℂ) : qpow q ρ ≠ 0 := Complex.exp_ne_zero _

lemma norm_qpow {q : ℝ} (hq : 0 < q) (ρ : ℂ) : ‖qpow q ρ‖ = q ^ ρ.re := by
  rw [qpow, Complex.norm_exp, Real.rpow_def_of_pos hq]
  congr 1
  simp [Complex.mul_re]

/-- **`def:suspension`**: the logarithmic suspension `Σ_q(α) = {ρ ∈ ℂ : q^ρ = α}`. -/
def logSusp (q : ℝ) (α : ℂ) : Set ℂ := {ρ | qpow q ρ = α}

/-- The explicit form after `def:suspension`: `Σ_q(α) = {(log α + 2πik)/log q : k ∈ ℤ}`. -/
theorem mem_logSusp_iff {q : ℝ} (hq : 1 < q) {α : ℂ} (hα : α ≠ 0) (ρ : ℂ) :
    ρ ∈ logSusp q α ↔ ∃ k : ℤ, ρ = WeilRH.suspEigen q k α := by
  have hL := WeilRH.log_ne_zero_of_one_lt hq
  constructor
  · intro h
    have h' : cexp ((Real.log q : ℂ) * ρ) = cexp (Complex.log α) := by
      rw [Complex.exp_log hα]; exact h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h'
    refine ⟨n, ?_⟩
    rw [WeilRH.suspEigen, eq_div_iff hL, mul_comm, hn]
    ring
  · rintro ⟨k, rfl⟩
    exact WeilRH.exp_suspEigen hq k hα

/-- **`prop:suspension` (i), first clause.** `1 - α q^{-s} = 0` iff `s ∈ Σ_q(α)`. -/
theorem mem_logSusp_iff_zero (q : ℝ) (α s : ℂ) : 1 - α * qpow q (-s) = 0 ↔ s ∈ logSusp q α := by
  have hs : qpow q (-s) * qpow q s = 1 := by
    rw [qpow, qpow, ← Complex.exp_add, mul_neg, neg_add_cancel, Complex.exp_zero]
  change _ ↔ qpow q s = α
  constructor
  · intro h
    have h' : α * qpow q (-s) = 1 := (sub_eq_zero.1 h).symm
    calc qpow q s = α * qpow q (-s) * qpow q s := by rw [h', one_mul]
      _ = α := by rw [mul_assoc, hs, mul_one]
  · intro h
    rw [← h, mul_comm, hs, sub_self]

/-- **`prop:suspension` (i), simplicity.** `s ↦ 1 - α q^{-s}` has derivative
`α (log q) q^{-s}`, which never vanishes when `α ≠ 0` and `q ≠ 1`, `q > 0`. -/
theorem hasDerivAt_one_sub (q : ℝ) (α s : ℂ) :
    HasDerivAt (fun s => 1 - α * qpow q (-s)) (α * (Real.log q : ℂ) * qpow q (-s)) s := by
  have h1 : HasDerivAt (fun s : ℂ => (Real.log q : ℂ) * -s) (-(Real.log q : ℂ)) s := by
    simpa using ((hasDerivAt_id s).neg.const_mul (Real.log q : ℂ))
  have h2 := (h1.cexp.const_mul α).const_sub 1
  convert h2 using 1
  all_goals (simp only [qpow, mul_neg]; try ring)

theorem deriv_ne_zero {q : ℝ} (hq : 1 < q) {α : ℂ} (hα : α ≠ 0) (s : ℂ) :
    α * (Real.log q : ℂ) * qpow q (-s) ≠ 0 :=
  mul_ne_zero (mul_ne_zero hα (WeilRH.log_ne_zero_of_one_lt hq)) (qpow_ne_zero q _)

variable (F : Module.End ℂ V) (q : ℝ)

/-- The index set `{ρ ∈ ℂ : q^ρ ∈ spec F}` of `def:log-susp`; it is `⋃_α Σ_q(α)`. -/
noncomputable def Idx : Type := {ρ : ℂ // F.HasEigenvalue (qpow q ρ)}

noncomputable instance : DecidableEq (Idx F q) := Classical.decEq _

/-- The summand `V̂_ρ = V_{(q^ρ)}`. -/
noncomputable abbrev Summand (ρ : Idx F q) : Submodule ℂ V := F.maxGenEigenspace (qpow q ρ.1)

/-- The suspended space `V̂ = ⨁_{ρ} V_{(q^ρ)}` (algebraic direct sum, `def:log-susp`). -/
abbrev SuspSpace : Type _ := ⨁ ρ : Idx F q, Summand F q ρ

/-- `F` restricted to its generalized eigenspace `V_{(α)}`. -/
noncomputable def restrictF (α : ℂ) : Module.End ℂ (F.maxGenEigenspace α) :=
  F.restrict (F.mapsTo_maxGenEigenspace_of_comm (Commute.refl F) α)

/-- `N_α = log(α⁻¹F) = ∑_{k ≥ 1} (-1)^{k+1} (α⁻¹F - 1)^k / k` on `V_{(α)}` (`def:log-susp`).
`α⁻¹F - 1` is nilpotent on `V_{(α)}` of index at most `dim V_{(α)} ≤ dim V`, so truncating at
`k = dim V` is the full series. -/
noncomputable def logNil (α : ℂ) : Module.End ℂ (F.maxGenEigenspace α) :=
  ∑ k ∈ Finset.Icc 1 (finrank ℂ V),
    ((-1 : ℂ) ^ (k + 1) / k) • (α⁻¹ • restrictF F α - 1) ^ k

lemma isNilpotent_unip {α : ℂ} (hα : α ≠ 0) : IsNilpotent (α⁻¹ • restrictF F α - 1) := by
  have h0 : IsNilpotent (restrictF F α - α • 1) := by
    have := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap F α
    convert this using 1
    ext x
    simp [restrictF, Algebra.algebraMap_eq_smul_one]
    rfl
  have : α⁻¹ • restrictF F α - 1 = α⁻¹ • (restrictF F α - α • 1) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [this]
  exact h0.smul _

lemma isNilpotent_logNil {α : ℂ} (hα : α ≠ 0) : IsNilpotent (logNil F α) := by
  have hU := isNilpotent_unip F hα
  refine Commute.isNilpotent_sum (fun k hk => ?_) (fun k l _ _ => ?_)
  · exact (hU.pow_of_pos (by simp at hk; omega)).smul _
  · exact ((Commute.refl _).pow_pow k l).smul_left _ |>.smul_right _

/-- The block `Θ|_{V̂_ρ} = ρ + (log q)⁻¹ N_{q^ρ}`. -/
noncomputable def thetaBlock (ρ : Idx F q) : Module.End ℂ (Summand F q ρ) :=
  ρ.1 • 1 + ((Real.log q : ℂ)⁻¹) • logNil F (qpow q ρ.1)

/-- **`def:log-susp`**: the operator `Θ` on the logarithmic suspension `V̂`. -/
noncomputable def theta : Module.End ℂ (SuspSpace F q) := diag (thetaBlock F q)

lemma isNilpotent_thetaBlock (ρ : Idx F q) : IsNilpotent (thetaBlock F q ρ - ρ.1 • 1) := by
  rw [thetaBlock, add_sub_cancel_left]
  exact (isNilpotent_logNil F (qpow_ne_zero q _)).smul _

omit [FiniteDimensional ℂ V] in
lemma val_injective : Function.Injective (fun ρ : Idx F q => ρ.1) := Subtype.val_injective

/-- `qpow q` is injective on any ball of radius `π / log q`. -/
lemma qpow_injOn_ball {q : ℝ} (hq : 1 < q) (z : ℂ) :
    Set.InjOn (qpow q) (Metric.ball z (Real.pi / Real.log q)) := by
  have hL : 0 < Real.log q := Real.log_pos hq
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hxy
  have hd : dist x y < 2 * Real.pi / Real.log q := by
    have := dist_triangle_right x y z
    rw [Metric.mem_ball] at hx hy
    have : 2 * Real.pi / Real.log q = Real.pi / Real.log q + Real.pi / Real.log q := by ring
    linarith
  have hnorm : ‖(Real.log q : ℂ) * (x - y)‖ = |(n : ℝ)| * (2 * Real.pi) := by
    rw [mul_sub, hn, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_intCast]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, ← dist_eq_norm] at hnorm
  have hlt : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rw [← hnorm]
    calc Real.log q * dist x y < Real.log q * (2 * Real.pi / Real.log q) :=
          mul_lt_mul_of_pos_left hd hL
      _ = 2 * Real.pi := by field_simp
  have hn1 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hn0 : n = 0 := by
    rw [← Int.cast_abs] at hn1
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast hn1)
  subst hn0
  have : (Real.log q : ℂ) * x = (Real.log q : ℂ) * y := by simpa using hn
  exact mul_left_cancel₀ (WeilRH.log_ne_zero_of_one_lt hq) this

/-- `⋃_α Σ_q(α)` over the eigenvalues of `F` has no finite accumulation point. -/
theorem noAccPt_idx {q : ℝ} (hq : 1 < q) (z : ℂ) :
    ¬ AccPt z (𝓟 {ρ : ℂ | F.HasEigenvalue (qpow q ρ)}) := by
  set S := {ρ : ℂ | F.HasEigenvalue (qpow q ρ)}
  set B := Metric.ball z (Real.pi / Real.log q)
  have hr : 0 < Real.pi / Real.log q := div_pos Real.pi_pos (Real.log_pos hq)
  have hfin : (S ∩ B).Finite := by
    refine Set.Finite.of_finite_image ?_ ((qpow_injOn_ball hq z).mono Set.inter_subset_right)
    exact F.finite_hasEigenvalue.subset (by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.1)
  intro hacc
  rw [accPt_iff_nhds] at hacc
  have hU : B ∩ ((S ∩ B) \ {z})ᶜ ∈ 𝓝 z := by
    refine Filter.inter_mem (Metric.ball_mem_nhds z hr) ?_
    refine (hfin.sdiff.isClosed).isOpen_compl.mem_nhds ?_
    simp
  obtain ⟨y, ⟨⟨hyB, hyc⟩, hyS⟩, hyz⟩ := hacc _ hU
  exact hyc ⟨⟨hyS, hyB⟩, hyz⟩

/-- **`prop:suspension` (ii).** For `q > 1`, the logarithmic suspension `(V̂, Θ)` is a spectral
core. -/
theorem spectralCore_theta {q : ℝ} (hq : 1 < q) : SpectralCore (theta F q) := by
  refine spectralCore_diag (fun ρ : Idx F q => ρ.1) (thetaBlock F q) (val_injective F q)
    (isNilpotent_thetaBlock F q) (fun z hz => noAccPt_idx F hq z (hz.mono ?_))
  exact principal_mono.2 (by rintro _ ⟨ρ, rfl⟩; exact ρ.2)

/-- **`prop:suspension` (ii), `V̂_{Θ∼ρ} = V̂_ρ`.** The generalized `ρ`-eigenspace of `Θ` is the
set of vectors supported on the summand `V̂_ρ`. -/
theorem mem_maxGenEigenspace_theta (ρ : ℂ) (x : SuspSpace F q) :
    x ∈ (theta F q).maxGenEigenspace ρ ↔ ∀ σ : Idx F q, σ.1 ≠ ρ → x σ = 0 :=
  mem_maxGenEigenspace_diag _ _ (val_injective F q) (isNilpotent_thetaBlock F q) ρ x

/-- The component at `ρ` identifies `V̂_{Θ∼ρ}` with `V_{(q^ρ)}`. -/
noncomputable def maxGenEigenspaceThetaEquiv (ρ : Idx F q) :
    (theta F q).maxGenEigenspace ρ.1 ≃ₗ[ℂ] F.maxGenEigenspace (qpow q ρ.1) :=
  maxGenEigenspaceDiagEquiv (fun σ : Idx F q => σ.1) (thetaBlock F q) (val_injective F q)
    (isNilpotent_thetaBlock F q) ρ

/-- **`prop:suspension` (ii)/(i), multiplicities.** `spec Θ = ⋃_α Σ_q(α)`. -/
theorem spec_theta : spec (theta F q) = {ρ : ℂ | F.HasEigenvalue (qpow q ρ)} := by
  ext ρ
  constructor
  · intro h
    obtain ⟨σ, rfl⟩ := spec_diag_subset _ _ (val_injective F q) (isNilpotent_thetaBlock F q) h
    exact σ.2
  · intro h hbot
    have hne : F.maxGenEigenspace (qpow q ρ) ≠ ⊥ := by
      intro h'
      apply Module.End.hasEigenvalue_iff.1 h
      rw [eq_bot_iff, ← h']
      exact Module.End.eigenspace_le_maxGenEigenspace
    have e := maxGenEigenspaceThetaEquiv F q ⟨ρ, h⟩
    apply hne
    rw [eq_bot_iff]
    intro v hv
    have hv' := e.symm.injective (Subsingleton.elim (h := by
      change Subsingleton ((theta F q).maxGenEigenspace ρ)
      rw [hbot]; infer_instance) (e.symm ⟨v, hv⟩) (e.symm 0))
    simpa using congrArg Subtype.val hv'

/-- **`prop:suspension` (i), multiplicities.** The algebraic multiplicity of `ρ` as an eigenvalue
of `Θ` is `dim V_{(q^ρ)}`. -/
theorem mult_theta (ρ : Idx F q) :
    mult (theta F q) ρ.1 = finrank ℂ (F.maxGenEigenspace (qpow q ρ.1)) :=
  mult_diag _ _ (val_injective F q) (isNilpotent_thetaBlock F q) ρ

/-! ### Polarizations (`prop:suspension` (iii)–(iv)) -/

/-- **`def:inf-pol`**: `h` is a positive infinitesimal polarization of weight `j` on `(W, Θ)` if
`h(Θu, v) + h(u, Θv) = j h(u, v)` for all `u, v` (positivity is carried by `PosHermForm`). -/
def IsInfPol {W : Type*} [AddCommGroup W] [Module ℂ W] (h : PosHermForm W)
    (Θ : Module.End ℂ W) (j : ℝ) : Prop :=
  ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = (j : ℂ) * h.toFun u v

variable {F q}

open Classical in
/-- `ĥ(u, v) = ∑_ρ h(u_ρ, v_ρ)`, summed over the support of `v`. -/
noncomputable def suspFun (h : PosHermForm V) (u v : SuspSpace F q) : ℂ :=
  ∑ ρ ∈ v.support, h.toFun (u ρ : V) (v ρ : V)

omit [FiniteDimensional ℂ V] in
/-- `ĥ(u, v)` may be summed over any finset containing the support of `v`. -/
lemma suspFun_eq (h : PosHermForm V) (u v : SuspSpace F q) (s : Finset (Idx F q))
    (hs : ∀ ρ, v ρ ≠ 0 → ρ ∈ s) : suspFun h u v = ∑ ρ ∈ s, h.toFun (u ρ : V) (v ρ : V) := by
  classical
  unfold suspFun
  refine Finset.sum_subset (fun ρ hρ => hs ρ (DFinsupp.mem_support_iff.1 hρ)) ?_
  intro ρ _ hρ
  have : v ρ = 0 := by simpa using hρ
  rw [this, ZeroMemClass.coe_zero, h.zero_right]

omit [FiniteDimensional ℂ V] in
lemma re_nonneg (h : PosHermForm V) (x : V) : 0 ≤ (h.toFun x x).re := by
  by_cases hx : x = 0
  · rw [hx, h.zero_left, Complex.zero_re]
  · exact (h.re_pos x hx).le

/-- **`def:log-susp` (a)**: the suspended form `ĥ`, the orthogonal sum of the restrictions of `h`
to the summands `V̂_ρ`. -/
noncomputable def suspForm (h : PosHermForm V) : PosHermForm (SuspSpace F q) where
  toFun := suspFun h
  add_left u u' v := by
    simp only [suspFun, DirectSum.add_apply, Submodule.coe_add, h.add_left,
      Finset.sum_add_distrib]
  smul_left c u v := by
    simp only [suspFun, DirectSum.smul_apply, Submodule.coe_smul, h.smul_left, Finset.mul_sum]
  conj_symm u v := by
    classical
    have hu : ∀ ρ, u ρ ≠ 0 → ρ ∈ u.support ∪ v.support := fun ρ hρ =>
      Finset.mem_union_left _ (DFinsupp.mem_support_iff.2 hρ)
    have hv : ∀ ρ, v ρ ≠ 0 → ρ ∈ u.support ∪ v.support := fun ρ hρ =>
      Finset.mem_union_right _ (DFinsupp.mem_support_iff.2 hρ)
    rw [suspFun_eq h u v _ hv, suspFun_eq h v u _ hu, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => h.conj_symm _ _
  re_pos u hu := by
    classical
    obtain ⟨ρ, hρ⟩ : ∃ ρ, u ρ ≠ 0 := by
      by_contra hc; push Not at hc; exact hu (DirectSum.ext hc)
    rw [suspFun_eq h u u u.support (fun σ hσ => DFinsupp.mem_support_iff.2 hσ), Complex.re_sum]
    exact Finset.sum_pos' (fun σ _ => re_nonneg h _)
      ⟨ρ, DFinsupp.mem_support_iff.2 hρ, h.re_pos _ (by simpa using hρ)⟩

omit [FiniteDimensional ℂ V] in
lemma restrictF_eq_smul {α : ℂ} (hss : F.maxGenEigenspace α = F.eigenspace α) :
    restrictF F α = α • 1 := by
  ext x
  have hx : (x : V) ∈ F.eigenspace α := hss ▸ x.2
  simp only [restrictF, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
  exact Module.End.mem_eigenspace_iff.1 hx

omit [FiniteDimensional ℂ V] in
lemma logNil_eq_zero {α : ℂ} (hα : α ≠ 0) (h : restrictF F α = α • 1) : logNil F α = 0 := by
  have hU : α⁻¹ • restrictF F α - 1 = 0 := by
    rw [h, smul_smul, inv_mul_cancel₀ hα, one_smul, sub_self]
  unfold logNil
  rw [hU]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [zero_pow (by simp at hk; omega), smul_zero]

variable {j : ℝ} {h : PosHermForm V}

/-- Under a positive Frobenius polarization every block of `Θ` is the scalar `ρ`. -/
lemma thetaBlock_eq_of_pol (hq : 1 < q) (hF : IsFrobPol h F q j) (σ : Idx F q) :
    thetaBlock F q σ = σ.1 • 1 := by
  have hss := (h.isSemisimple_of_weil F q j (by linarith) hF).isFinitelySemisimple
  rw [thetaBlock, logNil_eq_zero (qpow_ne_zero q _)
    (restrictF_eq_smul (hss.maxGenEigenspace_eq_eigenspace _)), smul_zero, add_zero]

lemma theta_apply_of_pol (hq : 1 < q) (hF : IsFrobPol h F q j) (x : SuspSpace F q)
    (σ : Idx F q) : theta F q x σ = σ.1 • x σ := by
  rw [theta, diag_apply, thetaBlock_eq_of_pol hq hF]; rfl

omit [FiniteDimensional ℂ V] in
/-- Under a positive Frobenius polarization of weight `j`, every `ρ` in the index set has
`Re ρ = j/2` (from `|q^ρ| = q^{j/2}`, `prop:weil-linear`). -/
lemma re_eq_of_pol (hq : 1 < q) (hF : IsFrobPol h F q j) (σ : Idx F q) : σ.1.re = j / 2 := by
  have hq0 : 0 < q := by linarith
  have h1 := h.norm_eq_rpow F q j hq0 hF σ.2
  rw [norm_qpow hq0, Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hq0] at h1
  exact mul_left_cancel₀ (Real.log_pos hq).ne' (Real.exp_injective h1)

/-- **`prop:suspension` (iii).** If `h` is a positive Frobenius polarization of weight `j` on
`(V, F)`, the suspended form `ĥ` is a positive infinitesimal polarization of weight `j` on
`(V̂, Θ)`. -/
theorem isInfPol_suspForm (hq : 1 < q) (hF : IsFrobPol h F q j) :
    IsInfPol (suspForm h : PosHermForm (SuspSpace F q)) (theta F q) j := by
  classical
  intro u v
  have hΘ := theta_apply_of_pol hq hF
  have hsupp : ∀ σ, theta F q v σ ≠ 0 → v σ ≠ 0 := fun σ hσ hv => hσ (by rw [hΘ, hv, smul_zero])
  change suspFun h _ _ + suspFun h _ _ = _ * suspFun h _ _
  rw [suspFun_eq h (theta F q u) v v.support (fun σ hσ => DFinsupp.mem_support_iff.2 hσ),
    suspFun_eq h u (theta F q v) v.support
      (fun σ hσ => DFinsupp.mem_support_iff.2 (hsupp σ hσ)),
    suspFun_eq h u v v.support (fun σ hσ => DFinsupp.mem_support_iff.2 hσ), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hΘ, hΘ, Submodule.coe_smul, Submodule.coe_smul, h.smul_left, h.smul_right, ← add_mul,
    Complex.add_conj, re_eq_of_pol hq hF σ]
  push_cast; ring

/-- **`prop:suspension` (iv), real parts.** Under a positive Frobenius polarization of weight `j`,
every (generalized) eigenvalue of `Θ` has real part `j/2`. -/
theorem re_eq_of_mem_spec (hq : 1 < q) (hF : IsFrobPol h F q j) {ρ : ℂ}
    (hρ : ρ ∈ spec (theta F q)) : ρ.re = j / 2 := by
  rw [spec_theta] at hρ
  exact re_eq_of_pol hq hF ⟨ρ, hρ⟩

theorem re_eq_of_hasEigenvalue (hq : 1 < q) (hF : IsFrobPol h F q j) {ρ : ℂ}
    (hρ : (theta F q).HasEigenvalue ρ) : ρ.re = j / 2 :=
  re_eq_of_mem_spec hq hF fun hbot => Module.End.hasEigenvalue_iff.1 hρ
    (eq_bot_iff.2 (hbot ▸ Module.End.eigenspace_le_maxGenEigenspace))

lemma maxGenEigenspace_le_eigenspace (hq : 1 < q) (hF : IsFrobPol h F q j) (ρ : ℂ) :
    (theta F q).maxGenEigenspace ρ ≤ (theta F q).eigenspace ρ := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  refine DirectSum.ext fun τ => ?_
  rw [theta_apply_of_pol hq hF, DirectSum.smul_apply]
  by_cases hτ : τ.1 = ρ
  · rw [hτ]
  · rw [(mem_maxGenEigenspace_theta F q ρ x).1 hx τ hτ, smul_zero, smul_zero]

/-- **`prop:suspension` (iv), diagonalizability.** Under a positive Frobenius polarization the
eigenspaces of `Θ` span `V̂`. -/
theorem iSup_eigenspace_theta (hq : 1 < q) (hF : IsFrobPol h F q j) :
    ⨆ ρ, (theta F q).eigenspace ρ = ⊤ :=
  eq_top_iff.2 ((spectralCore_theta F hq).iSup_eq_top.ge.trans
    (iSup_mono (maxGenEigenspace_le_eigenspace hq hF)))

end Suspension

/-- **`SpectralCore` is not vacuous.** The logarithmic suspension of `id_ℂ` with `q = 2` is a
spectral core whose spectrum `Σ_2(1) = (2πi / log 2) ℤ` contains `0`. -/
theorem spectralCore_nonvacuous :
    SpectralCore (theta (1 : Module.End ℂ ℂ) 2) ∧ (0 : ℂ) ∈ spec (theta (1 : Module.End ℂ ℂ) 2) := by
  refine ⟨spectralCore_theta _ one_lt_two, ?_⟩
  rw [spec_theta]
  show Module.End.HasEigenvalue 1 (qpow 2 0)
  rw [qpow, mul_zero, Complex.exp_zero, Module.End.hasEigenvalue_iff]
  intro h
  have : (1 : ℂ) ∈ (1 : Module.End ℂ ℂ).eigenspace 1 := by simp
  rw [h] at this
  simp at this


/-! ### The determinant `det(1 - F q^{-s})` (`prop:suspension` (i)) -/

section Determinant

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (F : Module.End ℂ V)

/-- `det(1 - tF) = ∏_{α ∈ roots(χ_F)} (1 - α t)` (with multiplicity) for `t ≠ 0`. -/
theorem det_one_sub_smul_eq_multiset {t : ℂ} (ht : t ≠ 0) :
    LinearMap.det (1 - t • F) = (F.charpoly.roots.map (fun a => 1 - a * t)).prod := by
  have hsplit : F.charpoly.Splits := IsAlgClosed.splits _
  have hmon := F.charpoly_monic
  have hcard : Multiset.card F.charpoly.roots = finrank ℂ V := by
    rw [← F.charpoly_natDegree, ← Polynomial.splits_iff_card_roots.mp hsplit]
  have h1 : (1 : Module.End ℂ V) - t • F = t • (algebraMap ℂ (Module.End ℂ V) t⁻¹ - F) := by
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [h1, LinearMap.det_smul, ← LinearMap.eval_charpoly]
  conv_lhs => rw [hsplit.eq_prod_roots_of_monic hmon]
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, ← hcard, ← Multiset.prod_replicate,
    ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  field_simp

/-- **`prop:suspension` (i), factorization** (proof of (i)):
`det(1 - tF) = ∏_α (1 - α t)^{dim V_{(α)}}` for `t ≠ 0`, the product over the eigenvalues of `F`.
With `t = q^{-s}`, which never vanishes, this is `det(1 - F q^{-s}) = ∏_α (1 - α q^{-s})^{dim V_{(α)}}`. -/
theorem det_one_sub_smul_eq_prod {t : ℂ} (ht : t ≠ 0) :
    LinearMap.det (1 - t • F) = ∏ α ∈ F.charpoly.roots.toFinset,
      (1 - α * t) ^ finrank ℂ (F.maxGenEigenspace α) := by
  rw [det_one_sub_smul_eq_multiset F ht, Finset.prod_multiset_map_count]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Polynomial.count_roots, LinearMap.finrank_maxGenEigenspace_eq]

lemma analyticAt_one_sub (q : ℝ) (α z : ℂ) : AnalyticAt ℂ (fun s => 1 - α * qpow q (-s)) z := by
  unfold qpow; fun_prop

/-- The analytic order of a finite product of analytic functions is the sum of the orders. -/
lemma analyticOrderAt_fun_prod {ι : Type*} (s : Finset ι) (G : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ i ∈ s, AnalyticAt ℂ (G i) z) :
    analyticOrderAt (fun x => ∏ i ∈ s, G i x) z = ∑ i ∈ s, analyticOrderAt (G i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [analyticOrderAt_eq_zero]
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [← ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    exact analyticOrderAt_mul (h a (Finset.mem_insert_self a s))
      (Finset.analyticAt_fun_prod _ fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `s ↦ 1 - α q^{-s}` has a simple zero at `ρ` if `α = q^ρ` and no zero otherwise
(`α = 0` allowed). -/
lemma analyticOrderAt_one_sub {q : ℝ} (hq : 1 < q) (α ρ : ℂ) :
    analyticOrderAt (fun s => 1 - α * qpow q (-s)) ρ = if α = qpow q ρ then 1 else 0 := by
  split_ifs with h
  · refine (analyticAt_one_sub q α ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · exact (mem_logSusp_iff_zero q α ρ).2 h.symm
    · rw [(hasDerivAt_one_sub q α ρ).deriv]
      exact deriv_ne_zero hq (h ▸ qpow_ne_zero q ρ) ρ
  · rw [analyticOrderAt_eq_zero]
    right
    rw [Ne, mem_logSusp_iff_zero]
    exact fun h' => h h'.symm

/-- `mult_theta` for every `ρ ∈ ℂ`: both sides vanish when `q^ρ` is not an eigenvalue of `F`. -/
theorem mult_theta_eq (q : ℝ) (ρ : ℂ) :
    mult (theta F q) ρ = finrank ℂ (F.maxGenEigenspace (qpow q ρ)) := by
  by_cases h : F.HasEigenvalue (qpow q ρ)
  · exact mult_theta F q ⟨ρ, h⟩
  · have h1 : ρ ∉ spec (theta F q) := by rw [spec_theta]; exact h
    have h2 : (theta F q).maxGenEigenspace ρ = ⊥ := by simpa [spec] using h1
    rw [mult, h2, finrank_bot, LinearMap.finrank_maxGenEigenspace_eq,
      Polynomial.rootMultiplicity_eq_zero]
    rwa [← Module.End.hasEigenvalue_iff_isRoot_charpoly]

/-- **`prop:suspension` (i), last clause.** The zeros of `det(1 - F q^{-s})`, counted with
multiplicity, are the eigenvalues of `Θ` on `V̂`, counted with algebraic multiplicity: for every
`ρ ∈ ℂ` the analytic order of `s ↦ det(1 - F q^{-s})` at `ρ` is `mult Θ ρ = dim V̂_{Θ∼ρ}`. -/
theorem analyticOrderAt_det {q : ℝ} (hq : 1 < q) (ρ : ℂ) :
    analyticOrderAt (fun s => LinearMap.det (1 - qpow q (-s) • F)) ρ = mult (theta F q) ρ := by
  set m : ℂ → ℕ := fun α => finrank ℂ (F.maxGenEigenspace α)
  set G : ℂ → ℂ → ℂ := fun α => (fun s => 1 - α * qpow q (-s)) ^ m α
  have hfun : (fun s => LinearMap.det (1 - qpow q (-s) • F)) =
      fun s => ∏ α ∈ F.charpoly.roots.toFinset, G α s := by
    funext s; exact det_one_sub_smul_eq_prod F (qpow_ne_zero q _)
  have hG : ∀ α, analyticOrderAt (G α) ρ = m α • (if α = qpow q ρ then 1 else 0) := by
    intro α
    rw [analyticOrderAt_pow (analyticAt_one_sub q α ρ), analyticOrderAt_one_sub hq]
  rw [hfun, analyticOrderAt_fun_prod _ G _ fun α _ => (analyticAt_one_sub q α ρ).pow _,
    Finset.sum_congr rfl fun α _ => hG α]
  rw [Finset.sum_eq_single (qpow q ρ)]
  · simp [m, mult_theta_eq]
  · intro b _ hb; simp [hb]
  · intro h
    have : m (qpow q ρ) = 0 := by
      simp only [m, LinearMap.finrank_maxGenEigenspace_eq]
      rw [Polynomial.rootMultiplicity_eq_zero]
      intro hr
      exact h (Multiset.mem_toFinset.2 ((Polynomial.mem_roots F.charpoly_monic.ne_zero).2 hr))
    simp [this]

end Determinant

end WeilRH.Suspension
