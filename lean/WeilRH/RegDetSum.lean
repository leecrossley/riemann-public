/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import WeilRH.RegDet
import WeilRH.R2Block

/-!
# Adding a finite spectrum to a zeta-regularizable one (`prop:R3` (iii), round 73)

Source: `latex/notes.tex`, `def:regdet`, `prop:R3` (iii).

`Regularization.addFinite`: if `(S', m')` is zeta-regularizable for a cut `c'` on `U`, and `F` is a
finite set with multiplicities `m_F`, then there is a nonempty open `U₀ ⊆ U` and a cut of
`S' ∪ F` on `U₀` extending `c'` (same branches on `S'`) for which `(S' ∪ F, m' + m_F)` is
zeta-regularizable, with

`det_reg((s - Θ' ⊕ Θ)/2π) = ∏_{ρ ∈ F} ((s - ρ)/2π)^{m_F(ρ)} · det_reg((s - Θ')/2π)`.

The new branches are rotated principal logarithms `log((s - ρ)u_ρ/2π) - log u_ρ` with
`u_ρ = |s₀ - ρ|/(s₀ - ρ)` for a point `s₀ ∈ U \ F`.

`R2.det_sum` (`prop:R3` (iii)) specializes `F` to the four eigenvalues `λ, λ̄, 1 - λ, 1 - λ̄` of the
quaternionic block with multiplicity one, where the product is `(2π)^{-4} p(s)`.

**Representation.** As in `RegDet`, spectra are sets with multiplicity functions. That the
spectrum of `Θ' ⊕ Θ` is `spec Θ' ∪ spec Θ` with multiplicities `m' + m` (the first sentence of the
manuscript's proof) is not restated here; `(S' ∪ F, m'')` is that datum by definition.
-/

open Complex Set Filter Topology
open scoped Real Classical

noncomputable section

namespace WeilRH

namespace RegDet

variable {S' : Set ℂ} (F : Finset ℂ)

/-- The summand `m(ρ) exp(-w L(ρ, s))` as a function of `ρ ∈ ℂ`. -/
noncomputable def termFn (L : ℂ → ℂ → ℂ) (m : ℂ → ℕ) (w s : ℂ) (ρ : ℂ) : ℂ :=
  (m ρ : ℂ) * exp (-w * L ρ s)

lemma specZeta_eq_tsum_indicator {S : Set ℂ} (c : SpectralCut S) (m : ℂ → ℕ) (w s : ℂ) :
    specZeta c m w s = ∑' ρ, S.indicator (termFn c.L m w s) ρ := by
  unfold specZeta zetaTerm SpectralCut.pow
  exact tsum_subtype S (termFn c.L m w s)

/-- Combined multiplicity `m' + m_F`. -/
def addMult (S' : Set ℂ) (F : Finset ℂ) (m' mF : ℂ → ℕ) (ρ : ℂ) : ℕ :=
  (if ρ ∈ S' then m' ρ else 0) + (if ρ ∈ F then mF ρ else 0)

section Cut

variable (c' : SpectralCut S')

/-- A point of `U` outside `F`. -/
lemma exists_mem_U_notMem : ∃ s₀ ∈ c'.U, s₀ ∉ (F : Set ℂ) := by
  obtain ⟨z, hz⟩ := c'.nonempty
  have hinf : (c'.U).Infinite := by
    exact infinite_of_mem_nhds z (c'.isOpen.mem_nhds hz)
  obtain ⟨s₀, hs₀, hF⟩ := (hinf.diff F.finite_toSet).nonempty
  exact ⟨s₀, hs₀, hF⟩

/-- The chosen base point. -/
noncomputable def basePt : ℂ := (exists_mem_U_notMem F c').choose

lemma basePt_mem : basePt F c' ∈ c'.U := (exists_mem_U_notMem F c').choose_spec.1

lemma basePt_notMem : basePt F c' ∉ (F : Set ℂ) := (exists_mem_U_notMem F c').choose_spec.2

/-- The rotation `u_ρ = |s₀ - ρ|/(s₀ - ρ)`. -/
noncomputable def rot (ρ : ℂ) : ℂ := (‖basePt F c' - ρ‖ : ℂ) / (basePt F c' - ρ)

lemma rot_ne_zero {ρ : ℂ} (hρ : ρ ∈ F) : rot F c' ρ ≠ 0 := by
  have h : basePt F c' - ρ ≠ 0 := sub_ne_zero.2 (fun h => basePt_notMem F c' (h ▸ hρ))
  simp [rot, h]

/-- The rotated branch `log((s - ρ)u_ρ/2π) - log u_ρ`. -/
noncomputable def newL (ρ s : ℂ) : ℂ := log ((s - ρ) / (2 * π) * rot F c' ρ) - log (rot F c' ρ)

/-- The combined branches: those of `c'` on `S'`, the rotated ones elsewhere. -/
noncomputable def combL (ρ s : ℂ) : ℂ := if ρ ∈ S' then c'.L ρ s else newL F c' ρ s

lemma combL_of_mem {ρ : ℂ} (h : ρ ∈ S') : combL F c' ρ = c'.L ρ := by
  funext s; simp [combL, h]

lemma combL_of_notMem {ρ : ℂ} (h : ρ ∉ S') : combL F c' ρ = newL F c' ρ := by
  funext s; simp [combL, h]

/-- The new domain `U₀ = U ∩ {s | (s - ρ)u_ρ/2π ∈ slitPlane for all ρ ∈ F}`. -/
def U₀ : Set ℂ := c'.U ∩ ⋂ ρ ∈ F, {s | (s - ρ) / (2 * π) * rot F c' ρ ∈ slitPlane}

lemma U₀_subset : U₀ F c' ⊆ c'.U := inter_subset_left

lemma isOpen_U₀ : IsOpen (U₀ F c') := by
  refine c'.isOpen.inter (isOpen_biInter_finset fun ρ _ => ?_)
  exact isOpen_slitPlane.preimage (by fun_prop)

lemma basePt_mem_U₀ : basePt F c' ∈ U₀ F c' := by
  refine ⟨basePt_mem F c', mem_iInter₂.2 fun ρ hρ => ?_⟩
  have h : basePt F c' - ρ ≠ 0 := sub_ne_zero.2 (fun h => basePt_notMem F c' (h ▸ hρ))
  have : (basePt F c' - ρ) / (2 * π) * rot F c' ρ = ((‖basePt F c' - ρ‖ / (2 * π) : ℝ) : ℂ) := by
    simp only [rot]; push_cast; field_simp
  rw [mem_setOf_eq, this]
  exact ofReal_mem_slitPlane.2 (by positivity)

lemma mem_slit {s ρ : ℂ} (hs : s ∈ U₀ F c') (hρ : ρ ∈ F) :
    (s - ρ) / (2 * π) * rot F c' ρ ∈ slitPlane := mem_iInter₂.1 hs.2 ρ hρ

lemma disjoint_U₀ : Disjoint (U₀ F c') (S' ∪ F) := by
  rw [Set.disjoint_union_right]
  refine ⟨c'.disjoint.mono_left (U₀_subset F c'), Set.disjoint_left.2 fun s hs hF => ?_⟩
  have := mem_slit F c' hs hF
  simp [sub_self] at this

/-- The combined cut of `S' ∪ F` on `U₀`. -/
noncomputable def combCut : SpectralCut (S' ∪ F) where
  U := U₀ F c'
  isOpen := isOpen_U₀ F c'
  nonempty := ⟨_, basePt_mem_U₀ F c'⟩
  disjoint := disjoint_U₀ F c'
  L := combL F c'
  holo := by
    intro ρ hρ
    by_cases h : ρ ∈ S'
    · rw [combL_of_mem F c' h]
      exact (c'.holo ρ h).mono (U₀_subset F c')
    · have hF : ρ ∈ F := by simpa [h] using hρ
      rw [combL_of_notMem F c' h]
      intro s hs
      have h1 : DifferentiableAt ℂ (fun s => log ((s - ρ) / (2 * π) * rot F c' ρ)) s :=
        DifferentiableAt.clog (by fun_prop) (mem_slit F c' hs hF)
      exact (h1.sub (differentiableAt_const (log (rot F c' ρ)))).differentiableWithinAt
  exp_L := by
    intro ρ hρ s hs
    by_cases h : ρ ∈ S'
    · rw [combL_of_mem F c' h]; exact c'.exp_L ρ h s (U₀_subset F c' hs)
    · have hF : ρ ∈ F := by simpa [h] using hρ
      rw [combL_of_notMem F c' h]
      simp only [newL]
      rw [exp_sub, exp_log (slitPlane_ne_zero (mem_slit F c' hs hF)),
        exp_log (rot_ne_zero F c' hF), mul_div_cancel_right₀ _ (rot_ne_zero F c' hF)]

lemma combCut_L_of_mem {ρ : ℂ} (hρ : ρ ∈ S') : (combCut F c').L ρ = c'.L ρ := by
  exact combL_of_mem F c' hρ

end Cut

section Reg

variable (c' : SpectralCut S') {m' : ℂ → ℕ} (mF : ℂ → ℕ) (r' : Regularization c' m')

/-- The finite part `∑_{ρ ∈ F} m_F(ρ) exp(-w L(ρ, s))` for the combined branches. -/
noncomputable def finPart (s w : ℂ) : ℂ := ∑ ρ ∈ F, termFn (combL F c') mF w s ρ

lemma indicator_split (w s : ℂ) :
    (S' ∪ (F : Set ℂ)).indicator (termFn (combL F c') (addMult S' F m' mF) w s) =
      S'.indicator (termFn c'.L m' w s) + (F : Set ℂ).indicator (termFn (combL F c') mF w s) := by
  funext ρ
  by_cases h1 : ρ ∈ S' <;> by_cases h2 : ρ ∈ (F : Set ℂ) <;>
    (simp [indicator, termFn, addMult, combL, h1, h2, Finset.mem_coe.1, add_mul]; try simp_all)

lemma tsum_finPart (s w : ℂ) :
    ∑' ρ, (F : Set ℂ).indicator (termFn (combL F c') mF w s) ρ = finPart F c' mF s w := by
  rw [← tsum_subtype, Finset.tsum_subtype']; rfl

lemma specZeta_comb {s w : ℂ} (hconv : ConvergesAt c' m' w s) :
    specZeta (combCut F c') (addMult S' F m' mF) w s = specZeta c' m' w s + finPart F c' mF s w := by
  rw [specZeta_eq_tsum_indicator, specZeta_eq_tsum_indicator]
  change ∑' ρ, (S' ∪ (F : Set ℂ)).indicator (termFn (combL F c') (addMult S' F m' mF) w s) ρ = _
  rw [indicator_split, ← tsum_finPart F c' mF s w]
  have hA : Summable (S'.indicator (termFn c'.L m' w s)) :=
    (summable_subtype_iff_indicator).1 hconv.of_norm
  have hB : Summable ((F : Set ℂ).indicator (termFn (combL F c') mF w s)) :=
    summable_of_finite_support ((F.finite_toSet).subset (support_indicator_subset))
  exact hA.tsum_add hB

lemma converges_comb {s w : ℂ} (hconv : ConvergesAt c' m' w s) :
    ConvergesAt (combCut F c') (addMult S' F m' mF) w s := by
  unfold ConvergesAt
  show Summable (fun ρ : ↥(S' ∪ (F : Set ℂ)) =>
    ‖termFn (combL F c') (addMult S' F m' mF) w s ρ‖)
  have hA : Summable (S'.indicator (fun ρ => ‖termFn c'.L m' w s ρ‖)) :=
    (summable_subtype_iff_indicator).1 hconv
  have hB : Summable ((F : Set ℂ).indicator (fun ρ => ‖termFn (combL F c') mF w s ρ‖)) :=
    summable_of_finite_support ((F.finite_toSet).subset (support_indicator_subset))
  refine (summable_subtype_iff_indicator
    (f := fun ρ => ‖termFn (combL F c') (addMult S' F m' mF) w s ρ‖)).2 ?_
  refine Summable.of_nonneg_of_le
    (fun ρ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) ρ)
    (fun ρ => ?_) (hA.add hB)
  have := congrFun (indicator_split F c' (m' := m') mF w s) ρ
  have e1 := norm_indicator_eq_indicator_norm (s := S' ∪ (F : Set ℂ))
    (f := termFn (combL F c') (addMult S' F m' mF) w s) ρ
  have e2 := norm_indicator_eq_indicator_norm (s := S') (f := termFn c'.L m' w s) ρ
  have e3 := norm_indicator_eq_indicator_norm (s := (F : Set ℂ))
    (f := termFn (combL F c') mF w s) ρ
  rw [← e1, ← e2, ← e3, this, Pi.add_apply]
  exact norm_add_le _ _

lemma hasDerivAt_finPart (s w : ℂ) :
    HasDerivAt (finPart F c' mF s)
      (∑ ρ ∈ F, (mF ρ : ℂ) * (exp (-w * combL F c' ρ s) * (-combL F c' ρ s))) w := by
  unfold finPart termFn
  refine HasDerivAt.fun_sum (fun ρ _ => ?_)
  have h1 : HasDerivAt (fun w : ℂ => -w * combL F c' ρ s) (-combL F c' ρ s) w := by
    simpa using ((hasDerivAt_id w).neg.mul_const (combL F c' ρ s))
  exact h1.cexp.const_mul _

lemma differentiable_finPart (s : ℂ) : Differentiable ℂ (finPart F c' mF s) :=
  fun w => (hasDerivAt_finPart F c' mF s w).differentiableAt

lemma deriv_finPart_zero (s : ℂ) :
    deriv (finPart F c' mF s) 0 = -∑ ρ ∈ F, (mF ρ : ℂ) * combL F c' ρ s := by
  rw [(hasDerivAt_finPart F c' mF s 0).deriv, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun ρ _ => by simp)

lemma exp_neg_deriv_finPart {s : ℂ} (hs : s ∈ U₀ F c') :
    exp (-deriv (finPart F c' mF s) 0) = finDet F mF s := by
  rw [deriv_finPart_zero, neg_neg, exp_sum]
  refine Finset.prod_congr rfl (fun ρ hρ => ?_)
  rw [exp_nat_mul]
  exact congrArg (· ^ mF ρ) ((combCut F c').exp_L ρ (Or.inr (by simpa using hρ)) s hs)

/-- **Adding a finite spectrum.** The combined datum is zeta-regularizable for the combined cut. -/
noncomputable def Regularization.addFinite :
    Regularization (combCut F c') (addMult S' F m' mF) where
  σ := r'.σ
  converges := fun s hs w hw =>
    converges_comb F c' mF (r'.converges s (U₀_subset F c' hs) w hw)
  Z := fun s w => r'.Z s w + finPart F c' mF s w
  dom := r'.dom
  dom_open := fun s hs => r'.dom_open s (U₀_subset F c' hs)
  dom_preconnected := fun s hs => r'.dom_preconnected s (U₀_subset F c' hs)
  halfPlane_subset := fun s hs => r'.halfPlane_subset s (U₀_subset F c' hs)
  zero_mem := fun s hs => r'.zero_mem s (U₀_subset F c' hs)
  merom := fun s hs w hw =>
    (r'.merom s (U₀_subset F c' hs) w hw).add
      ((differentiable_finPart F c' mF s).analyticAt w).meromorphicAt
  eq_series := fun s hs w hw => by
    have hs' := U₀_subset F c' hs
    rw [r'.eq_series s hs' w hw, specZeta_comb F c' mF (r'.converges s hs' w hw)]
  regular := fun s hs =>
    (r'.regular s (U₀_subset F c' hs)).add ((differentiable_finPart F c' mF s).analyticAt 0)
  holo_deriv := by
    have heq : EqOn (fun s => deriv (fun w => r'.Z s w + finPart F c' mF s w) 0)
        (fun s => deriv (r'.Z s) 0 + -∑ ρ ∈ F, (mF ρ : ℂ) * combL F c' ρ s) (U₀ F c') := by
      intro s hs
      simp only
      rw [deriv_fun_add (r'.regular s (U₀_subset F c' hs)).differentiableAt
        (differentiable_finPart F c' mF s 0), deriv_finPart_zero]
    refine DifferentiableOn.congr ?_ heq
    refine (r'.holo_deriv.mono (U₀_subset F c')).add
      (DifferentiableOn.fun_sum (fun ρ hρ => ?_)).neg
    exact ((combCut F c').holo ρ (Or.inr (by simpa using hρ))).const_mul _
  D := fun s => finDet F mF s * r'.D s
  entire := (differentiable_finDet F mF).mul r'.entire
  D_eq := fun s hs => by
    have hs' := U₀_subset F c' hs
    rw [deriv_fun_add (r'.regular s hs').differentiableAt (differentiable_finPart F c' mF s 0),
      neg_add, exp_add, ← r'.D_eq s hs', exp_neg_deriv_finPart F c' mF hs, mul_comm]

/-- `det_reg` of the sum is the finite product times `det_reg` of the given datum. -/
theorem detreg_addFinite :
    detreg (Regularization.addFinite F c' mF r') = fun s => finDet F mF s * detreg r' s := rfl

/-- Adding a finite spectrum keeps a half-plane regularization a half-plane one (revised
`def:regdet` (c)). -/
theorem Regularization.addFinite_onHalfPlane (h : r'.OnHalfPlane) :
    (Regularization.addFinite F c' mF r').OnHalfPlane :=
  fun s hs => h s (U₀_subset F c' hs)

end Reg

end RegDet

namespace R2

open RegDet

variable (a T : ℝ)

/-- The four eigenvalues `λ, λ̄, 1 - λ, 1 - λ̄` of the quaternionic block. -/
noncomputable def eigs : Finset ℂ :=
  {lam a T, (starRingEnd ℂ) (lam a T), 1 - lam a T, 1 - (starRingEnd ℂ) (lam a T)}

lemma eigs_card (ha : 0 < a) (hT : 0 < T) : (eigs a T).card = 4 := by
  have hne : ∀ x y : ℂ, x.re ≠ y.re ∨ x.im ≠ y.im → x ≠ y := fun x y h hxy => by
    rcases h with h | h <;> exact h (by rw [hxy])
  simp only [eigs, lam]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · exact hne _ _ (Or.inr (by simp; linarith))
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne _ _ (Or.inl (by simp; linarith)), hne _ _ (Or.inl (by simp; linarith))⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne _ _ (Or.inr (by simp; linarith)), hne _ _ (Or.inl (by simp; linarith)),
      hne _ _ (Or.inl (by simp; linarith))⟩

/-- `∏_{ρ ∈ spec Θ} (s - ρ)/2π = (2π)^{-4} p(s)`. -/
theorem finDet_eigs (ha : 0 < a) (hT : 0 < T) (s : ℂ) :
    finDet (eigs a T) 1 s = (2 * π : ℂ)⁻¹ ^ 4 * p a T s := by
  have hne : ∀ x y : ℂ, x.re ≠ y.re ∨ x.im ≠ y.im → x ≠ y := fun x y h hxy => by
    rcases h with h | h <;> exact h (by rw [hxy])
  have h1 : lam a T ∉ ({(starRingEnd ℂ) (lam a T), 1 - lam a T,
      1 - (starRingEnd ℂ) (lam a T)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, lam]
    exact ⟨hne _ _ (Or.inr (by simp; linarith)), hne _ _ (Or.inl (by simp; linarith)),
      hne _ _ (Or.inl (by simp; linarith))⟩
  have h2 : (starRingEnd ℂ) (lam a T) ∉ ({1 - lam a T, 1 - (starRingEnd ℂ) (lam a T)} :
      Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, lam]
    exact ⟨hne _ _ (Or.inl (by simp; linarith)), hne _ _ (Or.inl (by simp; linarith))⟩
  have h3 : 1 - lam a T ≠ 1 - (starRingEnd ℂ) (lam a T) :=
    hne _ _ (Or.inr (by simp [lam]; linarith))
  unfold finDet eigs
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_pair h3, p_eq_mul]
  simp only [lam, Pi.one_apply, pow_one, map_add, map_div₀, map_one, map_ofNat, map_mul,
    conj_ofReal, conj_I]
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * π).ne'
  field_simp
  linear_combination (32 * s * (T:ℂ) ^ 2 - 32 * s ^ 2 * (T:ℂ) ^ 2 - 32 * (a:ℂ) ^ 2 * (T:ℂ) ^ 2
    - 8 * (T:ℂ) ^ 2 - 16 * (T:ℂ) ^ 4 * (1 - I ^ 2)) * I_sq

/-- **`prop:R3` (iii).** If `(S', m')` is zeta-regularizable for a cut `c'` on `U`, then the datum
`(S' ∪ spec Θ, m' + 1)` of `V' ⊕ V` is zeta-regularizable for a cut on a nonempty open `U₀ ⊆ U`
extending `c'`, and `det_reg((s - Θ' ⊕ Θ)/2π) = (2π)^{-4} p(s) det_reg((s - Θ')/2π)`. -/
theorem det_sum {S' : Set ℂ} {m' : ℂ → ℕ} (c' : SpectralCut S') (r' : Regularization c' m')
    (ha : 0 < a) (hT : 0 < T) :
    ∃ (c'' : SpectralCut (S' ∪ eigs a T)) (r'' : Regularization c'' (addMult S' (eigs a T) m' 1)),
      c''.U ⊆ c'.U ∧ (∀ ρ ∈ S', c''.L ρ = c'.L ρ) ∧
      ∀ s, detreg r'' s = (2 * π : ℂ)⁻¹ ^ 4 * p a T s * detreg r' s :=
  ⟨combCut (eigs a T) c', Regularization.addFinite (eigs a T) c' 1 r', U₀_subset _ c',
    fun ρ hρ => combCut_L_of_mem _ c' hρ, fun s => by
      rw [detreg_addFinite]; simp only; rw [finDet_eigs a T ha hT]⟩

/-- **`prop:R3` (iii), revised `def:regdet`.** If `(S', m')` is zeta-regularizable for `c'` in the
revised sense (a half-plane regularization, `OnHalfPlane`), then so is
`(S' ∪ spec Θ, m' + 1)` for a cut extending `c'`, and
`det_reg((s - Θ' ⊕ Θ)/2π) = (2π)^{-4} p(s) det_reg((s - Θ')/2π)`; by `detreg_eq_of_onHalfPlane`
both determinants are the canonical ones for their cuts. -/
theorem det_sum_onHalfPlane {S' : Set ℂ} {m' : ℂ → ℕ} (c' : SpectralCut S')
    (r' : Regularization c' m') (hr' : r'.OnHalfPlane) (ha : 0 < a) (hT : 0 < T) :
    ∃ (c'' : SpectralCut (S' ∪ eigs a T)) (r'' : Regularization c'' (addMult S' (eigs a T) m' 1)),
      r''.OnHalfPlane ∧ c''.U ⊆ c'.U ∧ (∀ ρ ∈ S', c''.L ρ = c'.L ρ) ∧
      ∀ s, detreg r'' s = (2 * π : ℂ)⁻¹ ^ 4 * p a T s * detreg r' s :=
  ⟨combCut (eigs a T) c', Regularization.addFinite (eigs a T) c' 1 r',
    Regularization.addFinite_onHalfPlane (eigs a T) c' 1 r' hr', U₀_subset _ c',
    fun ρ hρ => combCut_L_of_mem _ c' hρ, fun s => by
      rw [detreg_addFinite]; simp only; rw [finDet_eigs a T ha hT]⟩

end R2

end WeilRH
