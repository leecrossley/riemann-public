/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ContentXiK

/-!
# `prop:N-count` (i): adding the points `1/2 ± i eᵏ` to `div ξ_K`

Round 67 formalization of `latex/notes.tex`, `prop:N-count` (i).

For an entire `f` with `f(1 - s) = f(s)` and `f ≢ 0`, `Σ = div f` is listed with multiplicity by
the trivial model of `SymEntire.family f` (round 51, `ContentXiK.lean`). The enlarged divisor
`Σ' = Σ + Σ_{k ≥ 1} ([1/2 + i eᵏ] + [1/2 - i eᵏ])` is listed by the family on `Idx f ⊕ ℕ` whose
new members are `1/2 + i e^{k+1}`; their partners `1 - (1/2 + i eᵏ) = 1/2 - i eᵏ` supply the
second points. So `Σ'` is again the spectrum of a trivial model.

## Main results

* `NCount.spectralCore` (`prop:N-count` (i), first clause): `Θ'` is a spectral core, and
  `NCount.rank_maxGenEigenspace`: `dim V'_{Θ'∼σ} = m_f(σ) + #{k ≥ 1 : σ = 1/2 ± i eᵏ}`.
* `NCount.mult_one_sub`, `NCount.mult_conj` (second clause): the multiplicities of `Σ'` are
  invariant under `σ ↦ 1 - σ`, and under `σ ↦ σ̄` when those of `Σ` are.
* `NCount.card_count` (third clause): for `T ≥ 1`, the number of points of `Σ'` (with
  multiplicity) with `0 < Im ρ ≤ T` is that of `Σ` plus `⌊log T⌋`. Counts are cardinals, so the
  identity holds whether or not the counts are finite.
* `NCount.xi`: the case `f = ξ_K`, conditional on Hecke's simple poles (`SimplePoles`, as in
  `prop:content`).

`prop:N-count` (ii) (the spectral zeta function of `Σ'` has a simple pole at `w = 0`) needs
`thm:det-K` and zeta-regularized determinants and is not formalized.
-/

open Complex ComplexConjugate Filter Topology Cardinal WeilRH.Spectral

namespace WeilRH.NCount

/-- The added points `1/2 + i e^{k+1}`, `k ≥ 0` (the manuscript's `k ≥ 1`). -/
noncomputable def added (k : ℕ) : ℂ := ⟨1 / 2, Real.exp (k + 1)⟩

lemma added_im (k : ℕ) : (added k).im = Real.exp (k + 1) := rfl

lemma added_re (k : ℕ) : (added k).re = 1 / 2 := rfl


lemma lam_added_im (i : ℕ × Bool) :
    (TrivialModel.lam added i).im = if i.2 then Real.exp (i.1 + 1) else -Real.exp (i.1 + 1) := by
  rcases i with ⟨k, b⟩
  cases b <;> simp [TrivialModel.lam, added_im]

lemma lam_added_injective : Function.Injective (TrivialModel.lam added) := by
  rintro ⟨k, b⟩ ⟨l, c⟩ h
  have hre := lam_added_im (k, b)
  have hre' := lam_added_im (l, c)
  rw [h] at hre
  have hpos : ∀ m : ℕ, 0 < Real.exp (m + 1) := fun m => Real.exp_pos _
  have hkl : ∀ m n : ℕ, Real.exp (m + 1) = Real.exp (n + 1) → m = n := by
    intro m n hmn
    have := Real.exp_injective hmn
    exact_mod_cast (add_left_inj 1).1 this
  cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hre hre'
  · rw [hre] at hre'; rw [hkl k l (neg_inj.1 hre')]
  · linarith [hpos k, hpos l]
  · linarith [hpos k, hpos l]
  · rw [hre] at hre'; rw [hkl k l hre']

/-- Finitely many added points lie in any ball. -/
lemma finite_added_ball (z : ℂ) (R : ℝ) :
    {i : ℕ × Bool | TrivialModel.lam added i ∈ Metric.ball z R}.Finite := by
  refine Set.Finite.subset ((Set.finite_Iio (⌈|z.im| + R⌉₊)).prod Set.finite_univ) ?_
  rintro ⟨k, b⟩ hk
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq] at hk
  refine ⟨?_, trivial⟩
  have him : |(TrivialModel.lam added (k, b)).im| = Real.exp (k + 1) := by
    rw [lam_added_im]; split_ifs <;> simp [abs_of_pos (Real.exp_pos _)]
  have h1 : |(TrivialModel.lam added (k, b)).im| ≤ |z.im| + ‖TrivialModel.lam added (k, b) - z‖ := by
    have := abs_im_le_norm (TrivialModel.lam added (k, b) - z)
    rw [sub_im] at this
    linarith [abs_sub_abs_le_abs_sub (TrivialModel.lam added (k, b)).im z.im]
  have h2 : (k : ℝ) < |z.im| + R := by
    have := Real.add_one_le_exp ((k : ℝ) + 1)
    linarith
  simp only [Set.mem_Iio]
  exact_mod_cast (Nat.lt_ceil.2 h2)

/-- A set meeting every ball of radius `1` in finitely many points has no finite accumulation
point. -/
lemma not_accPt_of_finite_ball {S : Set ℂ} (h : ∀ z, (S ∩ Metric.ball z 1).Finite) (z : ℂ) :
    ¬ AccPt z (𝓟 S) := by
  intro hacc
  rw [accPt_iff_nhds] at hacc
  set T := (S ∩ Metric.ball z 1) \ {z}
  have hT : IsClosed T := ((h z).sdiff).isClosed
  have hU : Metric.ball z 1 ∩ Tᶜ ∈ 𝓝 z :=
    inter_mem (Metric.ball_mem_nhds z one_pos)
      (hT.isOpen_compl.mem_nhds fun hz => hz.2 rfl)
  obtain ⟨y, ⟨⟨hy1, hy2⟩, hyS⟩, hyz⟩ := hacc _ hU
  exact hy2 ⟨⟨hyS, hy1⟩, hyz⟩

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsym : ∀ s, f (1 - s) = f s)
  {z₀ : ℂ} (hz₀ : f z₀ ≠ 0)

variable (f) in
/-- The family listing `Σ'`: the designated zeros of `f`, then the added points. -/
noncomputable def family' : SymEntire.Idx f ⊕ ℕ → ℂ := Sum.elim (SymEntire.family f) added

/-- `(Idx f ⊕ ℕ) × Bool` splits into the old basis and the added basis. -/
noncomputable def splitEquiv :
    (SymEntire.Idx f ⊕ ℕ) × Bool ≃ (SymEntire.Idx f × Bool) ⊕ (ℕ × Bool) :=
  Equiv.sumProdDistrib _ _ _

lemma lam_split (i : (SymEntire.Idx f ⊕ ℕ) × Bool) :
    TrivialModel.lam (family' f) i =
      Sum.elim (TrivialModel.lam (SymEntire.family f)) (TrivialModel.lam added) (splitEquiv i) := by
  rcases i with ⟨i | k, b⟩ <;> rfl

/-- The fibre of `λ'` over `σ` is the disjoint union of the old fibre and the added fibre. -/
noncomputable def fiberEquiv (σ : ℂ) :
    {i // TrivialModel.lam (family' f) i = σ} ≃
      {i // TrivialModel.lam (SymEntire.family f) i = σ} ⊕ {i // TrivialModel.lam added i = σ} :=
  ((splitEquiv).subtypeEquiv fun i => by rw [lam_split]).trans
    (Equiv.subtypeSum (p := fun x => Sum.elim (TrivialModel.lam (SymEntire.family f))
      (TrivialModel.lam added) x = σ))

/-- More generally, for any predicate `P` on `ℂ`, the basis vectors of `Σ'` whose eigenvalue
satisfies `P` split into the old ones and the added ones. -/
noncomputable def predEquiv (P : ℂ → Prop) :
    {i // P (TrivialModel.lam (family' f) i)} ≃
      {i // P (TrivialModel.lam (SymEntire.family f) i)} ⊕ {i // P (TrivialModel.lam added i)} :=
  ((splitEquiv).subtypeEquiv fun i => by rw [lam_split]).trans
    (Equiv.subtypeSum (p := fun x => P (Sum.elim (TrivialModel.lam (SymEntire.family f))
      (TrivialModel.lam added) x)))

lemma card_fiber' (σ : ℂ) :
    #{i // TrivialModel.lam (family' f) i = σ} =
      #{i // TrivialModel.lam (SymEntire.family f) i = σ} + #{i // TrivialModel.lam added i = σ} := by
  rw [Cardinal.mk_congr (fiberEquiv σ), Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]

lemma finite_added_fiber (σ : ℂ) : {i | TrivialModel.lam added i = σ}.Finite :=
  Set.Subsingleton.finite fun _ ha _ hb => lam_added_injective (ha.trans hb.symm)

include hf hsym hz₀ in
/-- **`prop:N-count` (i)**, the multiplicities: `dim V'_{Θ'∼σ} = m_f(σ) + #{added points = σ}`. -/
theorem rank_maxGenEigenspace (σ : ℂ) :
    Module.rank ℂ ((TrivialModel.theta (family' f)).maxGenEigenspace σ) =
      analyticOrderNatAt f σ + #{i // TrivialModel.lam added i = σ} := by
  rw [TrivialModel.rank_maxGenEigenspace_theta, card_fiber', SymEntire.card_fiber hf hsym hz₀]

include hf hsym hz₀ in
/-- **`prop:N-count` (i)**: `Σ'` is the spectrum, with multiplicity, of a spectral core. -/
theorem spectralCore : SpectralCore (TrivialModel.theta (family' f)) := by
  have hcore := SymEntire.spectralCore hf hsym hz₀
  refine TrivialModel.spectralCore_theta (family' f) (fun σ => ?_) (fun z => ?_)
  · -- finite fibres
    have hold : {i | TrivialModel.lam (SymEntire.family f) i = σ}.Finite := by
      have hlt : #{i // TrivialModel.lam (SymEntire.family f) i = σ} < ℵ₀ := by
        rw [SymEntire.card_fiber hf hsym hz₀]; exact natCast_lt_aleph0
      exact lt_aleph0_iff_set_finite.1 hlt
    have hlt : #{i // TrivialModel.lam (family' f) i = σ} < ℵ₀ := by
      rw [card_fiber']
      exact add_lt_aleph0 (lt_aleph0_iff_set_finite.2 hold)
        (lt_aleph0_iff_set_finite.2 (finite_added_fiber σ))
    exact lt_aleph0_iff_set_finite.1 hlt
  · -- no finite accumulation point
    have hrange : Set.range (TrivialModel.lam (family' f)) =
        Set.range (TrivialModel.lam (SymEntire.family f)) ∪ Set.range (TrivialModel.lam added) := by
      ext σ; constructor
      · rintro ⟨i, rfl⟩
        rw [lam_split]
        rcases splitEquiv i with j | j
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr ⟨j, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨splitEquiv.symm (Sum.inl j), by rw [lam_split]; simp⟩
        · exact ⟨splitEquiv.symm (Sum.inr j), by rw [lam_split]; simp⟩
    rw [hrange, AccPt, ← Filter.sup_principal, inf_sup_left, Filter.sup_neBot]
    rintro (h | h)
    · have := hcore.noAccPt z
      rw [TrivialModel.spec_theta] at this
      exact this h
    · refine not_accPt_of_finite_ball (fun w => ?_) z h
      refine Set.Finite.subset ((finite_added_ball w 1).image (TrivialModel.lam added)) ?_
      rintro _ ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩

/-- The partner involution `e_p ↔ f_p` on the added basis. -/
def swapE : ℕ × Bool ≃ ℕ × Bool where
  toFun := TrivialModel.swap
  invFun := TrivialModel.swap
  left_inv i := by simp [TrivialModel.swap]
  right_inv i := by simp [TrivialModel.swap]

lemma lam_added_swap (i : ℕ × Bool) :
    TrivialModel.lam added (swapE i) = 1 - TrivialModel.lam added i := by
  rcases i with ⟨k, b⟩
  cases b <;> simp [swapE, TrivialModel.swap, TrivialModel.lam]

lemma conj_lam_added (i : ℕ × Bool) :
    conj (TrivialModel.lam added i) = 1 - TrivialModel.lam added i := by
  rcases i with ⟨k, b⟩
  cases b <;> apply Complex.ext <;>
    simp [TrivialModel.lam, added_re, added_im] <;> norm_num

lemma card_added_fiber_one_sub (σ : ℂ) :
    #{i // TrivialModel.lam added i = 1 - σ} = #{i // TrivialModel.lam added i = σ} := by
  refine (Cardinal.mk_congr (swapE.subtypeEquiv fun i => ?_)).symm
  rw [lam_added_swap, sub_right_inj]

include hf hsym hz₀ in
/-- **`prop:N-count` (i)**: the multiplicities of `Σ'` are invariant under `σ ↦ 1 - σ`. -/
theorem mult_one_sub (σ : ℂ) :
    Module.rank ℂ ((TrivialModel.theta (family' f)).maxGenEigenspace (1 - σ)) =
      Module.rank ℂ ((TrivialModel.theta (family' f)).maxGenEigenspace σ) := by
  rw [rank_maxGenEigenspace hf hsym hz₀, rank_maxGenEigenspace hf hsym hz₀,
    SymEntire.mult_one_sub hsym, card_added_fiber_one_sub]

lemma card_added_fiber_conj (σ : ℂ) :
    #{i // TrivialModel.lam added i = conj σ} = #{i // TrivialModel.lam added i = σ} := by
  refine (Cardinal.mk_congr (swapE.subtypeEquiv fun i => ?_)).symm
  rw [lam_added_swap, ← conj_lam_added]
  exact (RingHom.injective _).eq_iff.symm

include hf hsym hz₀ in
/-- **`prop:N-count` (i)**: if the multiplicities of `Σ` are invariant under `σ ↦ σ̄` (for
`f = ξ_K`, since `ξ_K` is real on the real axis), so are those of `Σ'`. -/
theorem mult_conj (hconj : ∀ σ, analyticOrderNatAt f (conj σ) = analyticOrderNatAt f σ)
    (σ : ℂ) :
    Module.rank ℂ ((TrivialModel.theta (family' f)).maxGenEigenspace (conj σ)) =
      Module.rank ℂ ((TrivialModel.theta (family' f)).maxGenEigenspace σ) := by
  rw [rank_maxGenEigenspace hf hsym hz₀, rank_maxGenEigenspace hf hsym hz₀, hconj,
    card_added_fiber_conj]

/-- An added basis vector has `0 < Im λ ≤ T` iff it is `e_k` (not `f_k`) with `k < ⌊log T⌋`. -/
lemma mem_count_iff {T : ℝ} (hT : 1 ≤ T) (i : ℕ × Bool) :
    (0 < (TrivialModel.lam added i).im ∧ (TrivialModel.lam added i).im ≤ T) ↔
      (i.2 = true ∧ i.1 < ⌊Real.log T⌋₊) := by
  rcases i with ⟨k, b⟩
  rw [lam_added_im]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false, not_and]
    intro h; exact absurd h (not_lt.2 (neg_nonpos.2 (Real.exp_pos _).le))
  · simp only [↓reduceIte, true_and, Real.exp_pos]
    rw [← Real.le_log_iff_exp_le (by linarith), Nat.lt_iff_add_one_le,
      Nat.le_floor_iff (Real.log_nonneg hT)]
    push_cast; rfl

/-- The added points with `0 < Im ≤ T` are `1/2 + i e^{k+1}` with `e^{k+1} ≤ T`; there are
`⌊log T⌋` of them. -/
lemma card_added_count {T : ℝ} (hT : 1 ≤ T) :
    #{i : ℕ × Bool // 0 < (TrivialModel.lam added i).im ∧ (TrivialModel.lam added i).im ≤ T} =
      ⌊Real.log T⌋₊ := by
  rw [Cardinal.mk_congr (Equiv.subtypeEquivRight (mem_count_iff hT))]
  let e : {i : ℕ × Bool // i.2 = true ∧ i.1 < ⌊Real.log T⌋₊} ≃ Fin ⌊Real.log T⌋₊ :=
    { toFun := fun i => ⟨i.1.1, i.2.2⟩
      invFun := fun k => ⟨(k.1, true), rfl, k.2⟩
      left_inv := by
        rintro ⟨⟨k, b⟩, hb, hk⟩
        simp only at hb; subst hb; rfl
      right_inv := fun k => rfl }
  rw [Cardinal.mk_congr e, Cardinal.mk_fin]

/-- **`prop:N-count` (i)**, the count: for `T ≥ 1` the number of points of `Σ'` (with
multiplicity) with `0 < Im ρ ≤ T` exceeds that of `Σ` by `⌊log T⌋`. -/
theorem card_count {T : ℝ} (hT : 1 ≤ T) :
    #{i // 0 < (TrivialModel.lam (family' f) i).im ∧ (TrivialModel.lam (family' f) i).im ≤ T} =
      #{i // 0 < (TrivialModel.lam (SymEntire.family f) i).im ∧
        (TrivialModel.lam (SymEntire.family f) i).im ≤ T} + ⌊Real.log T⌋₊ := by
  rw [← card_added_count hT, Cardinal.mk_congr (predEquiv fun z => 0 < z.im ∧ z.im ≤ T),
    Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]

end WeilRH.NCount

namespace WeilRH

open NumberField

variable {K : Type} [Field K] [NumberField K] {C : DedekindContinuation K} (P : C.SimplePoles)

/-- **`prop:N-count` (i)** for `ξ_K` (conditional on Hecke's simple poles, as `prop:content`):
`Σ' = div ξ_K + Σ_{k ≥ 1} ([1/2 + i eᵏ] + [1/2 - i eᵏ])` is the spectrum, with multiplicity, of a
spectral core, invariant under `σ ↦ 1 - σ`, and its count up to height `T ≥ 1` exceeds that of
`div ξ_K` by `⌊log T⌋`. -/
theorem NCount.xi :
    Spectral.SpectralCore (TrivialModel.theta (NCount.family' P.ξ)) ∧
      (∀ σ, Module.rank ℂ ((TrivialModel.theta (NCount.family' P.ξ)).maxGenEigenspace σ) =
        analyticOrderNatAt P.ξ σ + Cardinal.mk {i // TrivialModel.lam NCount.added i = σ}) ∧
      (∀ σ, Module.rank ℂ ((TrivialModel.theta (NCount.family' P.ξ)).maxGenEigenspace (1 - σ)) =
        Module.rank ℂ ((TrivialModel.theta (NCount.family' P.ξ)).maxGenEigenspace σ)) ∧
      (∀ T : ℝ, 1 ≤ T →
        Cardinal.mk {i // 0 < (TrivialModel.lam (NCount.family' P.ξ) i).im ∧
          (TrivialModel.lam (NCount.family' P.ξ) i).im ≤ T} =
        Cardinal.mk {i // 0 < (TrivialModel.lam (SymEntire.family P.ξ) i).im ∧
          (TrivialModel.lam (SymEntire.family P.ξ) i).im ≤ T} + ⌊Real.log T⌋₊) :=
  ⟨NCount.spectralCore P.differentiable P.one_sub P.xi_one_ne_zero,
    NCount.rank_maxGenEigenspace P.differentiable P.one_sub P.xi_one_ne_zero,
    NCount.mult_one_sub P.differentiable P.one_sub P.xi_one_ne_zero,
    fun _ hT => NCount.card_count hT⟩

end WeilRH
