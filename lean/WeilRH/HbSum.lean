/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.BlackBoxes2
import WeilRH.RoucheRoute
import WeilRH.XiK
import WeilRH.ContentXiK
import WeilRH.ZetaZerosRvM

/-!
# The partial-fraction expansion of `𝔪 = -F'/F` and `Im 𝔪 > 0` (round 75)

Source: `latex/notes.tex`, `prop:hb-high` (second clause) and the series `eq:hb-product` used in
`prop:hb`. For an even entire `F` with a genus-one Hadamard product
`F(s) = e^{a+bs} g(s)`, `(log g)' = ∑ (1/(s-ρ) + 1/ρ)`, evenness cancels both `b` and the
non-absolutely-convergent `∑ 1/ρ`:

  `𝔪(z) = -F'(z)/F(z) = ½ ∑_ρ (1/(ρ - z) + 1/(-ρ - z))`   (`HbSum.hasSum_neg_logDeriv`).

Each term has `Im > 0` when `Im z > |Im ρ|`, so `Im 𝔪(z) > 0` (`HbSum.im_neg_logDeriv_pos`).
This is the manuscript's argument, with the pairing `{r, -r}` replaced by the identity
`𝔪(z) = (L(-z) - L(z))/2`, `L = F'/F`.

For `F(z) = ξ(1/2 - iz)` (`riemannXiUpper`) the hypotheses come from B1 for `ℚ` (growth of `ξ`),
B3' (locally uniform Hadamard product) and B6 (a zero exists):
`riemannXiUpper_im_neg_logDeriv_pos` is `prop:hb-high`, second clause, CONDITIONAL on those boxes.
-/

open Complex Filter Topology

namespace WeilRH.HbSum

variable {F : ℂ → ℂ} {ι : Type} (ρ : ι → ℂ) {a b : ℂ} {g : ℂ → ℂ}

/-- `F' / F` of `e^{a+bs} g(s)` is `b + g'/g`. -/
lemma logDeriv_eq (hF : Differentiable ℂ F) (hfac : ∀ s, F s = exp (a + b * s) * g s)
    {z : ℂ} (hFz : F z ≠ 0) : logDeriv F z = b + logDeriv g z := by
  have hg : ∀ s, g s = exp (-(a + b * s)) * F s := by
    intro s; rw [hfac s, ← mul_assoc, ← Complex.exp_add]; simp
  have hgd : Differentiable ℂ g := by
    have : g = fun s => exp (-(a + b * s)) * F s := funext hg
    rw [this]; fun_prop
  have hgz : g z ≠ 0 := by
    intro h0; apply hFz; rw [hfac z, h0, mul_zero]
  have hFeq : F = fun s => exp (a + b * s) * g s := funext hfac
  have hexp : logDeriv (fun s => exp (a + b * s)) z = b := by
    have hd : HasDerivAt (fun s => exp (a + b * s)) (exp (a + b * z) * b) z := by
      have h1 : HasDerivAt (fun s => a + b * s) b z := by
        simpa using ((hasDerivAt_id z).const_mul b).const_add a
      exact h1.cexp
    rw [logDeriv_apply, hd.deriv]
    field_simp [Complex.exp_ne_zero]
  rw [hFeq]
  show logDeriv ((fun s => exp (a + b * s)) * g) z = b + logDeriv g z
  rw [logDeriv_mul (f := fun s => exp (a + b * s)) z (Complex.exp_ne_zero _) hgz
    (by fun_prop) (hgd z), hexp]

/-- For an even differentiable `F`, `L(-z) = -L(z)` with `L = F'/F`. -/
lemma logDeriv_neg (heven : ∀ z, F (-z) = F z) (z : ℂ) :
    logDeriv F (-z) = -logDeriv F z := by
  have hFn : F = fun w => F (-w) := funext fun w => (heven w).symm
  have hd : deriv F z = -deriv F (-z) := by
    conv_lhs => rw [hFn]
    rw [deriv_comp_neg]
  rw [logDeriv_apply, logDeriv_apply, hd, heven]
  simp [neg_div]

/-- **The symmetric partial-fraction expansion of `𝔪 = -F'/F`.** For an even entire `F` with
`F = e^{a+bs} g`, `(log g)'(s) = ∑ (1/(s-ρ_i) + 1/ρ_i)` off the zeros, and `F(z) ≠ 0`, `z, -z`
off the list:
`-F'(z)/F(z) = ∑_i (1/(ρ_i - z) + 1/(-ρ_i - z)) / 2`. -/
theorem hasSum_neg_logDeriv (hF : Differentiable ℂ F) (heven : ∀ z, F (-z) = F z)
    (hfac : ∀ s, F s = exp (a + b * s) * g s)
    (hsum : ∀ s : ℂ, (∀ i, s ≠ ρ i) → HasSum (fun i => 1 / (s - ρ i) + 1 / ρ i) (logDeriv g s))
    {z : ℂ} (hFz : F z ≠ 0) (hz : ∀ i, z ≠ ρ i) (hz' : ∀ i, -z ≠ ρ i) :
    HasSum (fun i => (1 / (ρ i - z) + 1 / (-ρ i - z)) / 2) (-logDeriv F z) := by
  have hFz' : F (-z) ≠ 0 := by rwa [heven]
  have h1 := hsum z hz
  have h2 := hsum (-z) hz'
  have hL1 := logDeriv_eq hF hfac hFz
  have hL2 := logDeriv_eq hF hfac hFz'
  have hn := logDeriv_neg heven z
  have h3 := (h2.sub h1).div_const 2
  have hval : (logDeriv g (-z) - logDeriv g z) / 2 = -logDeriv F z := by
    have : logDeriv g (-z) = -logDeriv F z - b := by rw [← hn, hL2]; ring
    rw [this, hL1]; ring
  rw [hval] at h3
  convert h3 using 2 with i
  have e1 : 1 / (ρ i - z) = -(1 / (z - ρ i)) := by rw [← neg_sub, div_neg]
  have e2 : 1 / (-ρ i - z) = 1 / (-z - ρ i) := by ring_nf
  rw [e1, e2]; ring

/-- `Im (1/(ρ - z)) > 0` when `Im ρ < Im z`. -/
lemma im_one_div_pos {w z : ℂ} (h : w.im < z.im) : 0 < (1 / (w - z)).im := by
  have hne : w - z ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  rw [one_div, inv_im, neg_div]
  have hn : 0 < normSq (w - z) := normSq_pos.2 hne
  have : (w - z).im < 0 := by simp; linarith
  have := div_neg_of_neg_of_pos this hn
  linarith

/-- **`Im 𝔪(z) > 0` above the zeros.** Under the hypotheses of `hasSum_neg_logDeriv`, if the
list is nonempty and `|Im ρ_i| < Im z` for every `i`, then `Im(-F'(z)/F(z)) > 0`. -/
theorem im_neg_logDeriv_pos (hF : Differentiable ℂ F) (heven : ∀ z, F (-z) = F z)
    (hfac : ∀ s, F s = exp (a + b * s) * g s)
    (hsum : ∀ s : ℂ, (∀ i, s ≠ ρ i) → HasSum (fun i => 1 / (s - ρ i) + 1 / ρ i) (logDeriv g s))
    [Nonempty ι] {z : ℂ} (hFz : F z ≠ 0) (hy : ∀ i, |(ρ i).im| < z.im) :
    0 < (-logDeriv F z).im := by
  have hz : ∀ i, z ≠ ρ i := by
    intro i h; have := hy i; rw [← h] at this; linarith [le_abs_self z.im]
  have hz' : ∀ i, -z ≠ ρ i := by
    intro i h; have := hy i; rw [← h] at this; simp at this; linarith [le_abs_self z.im]
  have hS := Complex.imCLM.hasSum (hasSum_neg_logDeriv ρ hF heven hfac hsum hFz hz hz')
  have hpos : ∀ i, 0 < Complex.imCLM ((1 / (ρ i - z) + 1 / (-ρ i - z)) / 2) := by
    intro i
    have h1 : (ρ i).im < z.im := lt_of_le_of_lt (le_abs_self _) (hy i)
    have h2 : (-ρ i).im < z.im := by
      simp only [neg_im]; exact lt_of_le_of_lt (neg_le_abs _) (hy i)
    have a1 := im_one_div_pos h1
    have a2 := im_one_div_pos h2
    simp only [Complex.imCLM_apply, div_ofNat_im, add_im]
    linarith
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have := hasSum_lt (f := fun _ : ι => (0 : ℝ)) (fun i => (hpos i).le) (hpos i₀) hasSum_zero hS
  simpa using this


/-! ### Zeros listed with multiplicity -/

/-- The zeros of an entire `f`, listed with multiplicity: a zero `w` of order `m` gives the indices
`(w, 0), …, (w, m - 1)`. -/
def ZIdx (f : ℂ → ℂ) : Type :=
  {p : ℂ × ℕ // f p.1 = 0 ∧ p.2 < analyticOrderNatAt f p.1}

/-- The zero attached to an index. -/
def ZIdx.pt {f : ℂ → ℂ} (i : ZIdx f) : ℂ := i.1.1

/-- The fiber of `ZIdx.pt` over `w` has `ord_w f` elements. -/
noncomputable def ZIdx.fiberEquiv {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0)
    (w : ℂ) : {i : ZIdx f // i.pt = w} ≃ Fin (analyticOrderNatAt f w) where
  toFun i := ⟨i.1.1.2, by
    obtain ⟨⟨⟨v, k⟩, h⟩, hv⟩ := i
    simp only [ZIdx.pt] at hv
    subst hv
    exact h.2⟩
  invFun k := ⟨⟨(w, k), (SymEntire.mult_pos_iff hf hz₀ w).1 (Nat.zero_lt_of_lt k.2), k.2⟩, rfl⟩
  left_inv i := by
    obtain ⟨⟨⟨v, k⟩, h⟩, rfl⟩ := i
    rfl
  right_inv _ := rfl

/-- `ZIdx.pt` lists exactly the zeros: `f w = 0 ↔ ∃ i, pt i = w`. -/
lemma ZIdx.exists_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (w : ℂ) :
    f w = 0 ↔ ∃ i : ZIdx f, i.pt = w :=
  ⟨fun h => ⟨⟨(w, 0), h, (SymEntire.mult_pos_iff hf hz₀ w).2 h⟩, rfl⟩,
    fun ⟨i, hi⟩ => by rw [← hi]; exact i.2.1⟩

/-- The fibers of `ZIdx.pt` have the right cardinality. -/
lemma ZIdx.card_fiber {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0) (w : ℂ) :
    Nat.card {i : ZIdx f // i.pt = w} = analyticOrderNatAt f w := by
  rw [Nat.card_congr (ZIdx.fiberEquiv hf hz₀ w), Nat.card_fin]

/-! ### Growth transfer -/

/-- A growth bound `log ‖f s‖ ≤ C ‖s‖ log ‖s‖` for `‖s‖ ≥ 2` and continuity give
`log ‖f s‖ ≤ A + B ‖s‖^{3/2}` for every `s`, with `A, B ≥ 0`. -/
lemma log_norm_le_global {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ s : ℂ, Real.log ‖f s‖ ≤ A + B * ‖s‖ ^ (1 + (1 : ℝ) / 2) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, 2 * |C|, le_max_right _ _, by positivity, fun s => ?_⟩
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  have hrp : 0 ≤ ‖s‖ ^ (1 + (1 : ℝ) / 2) := Real.rpow_nonneg hn _
  rcases le_or_gt 2 ‖s‖ with h2 | h2
  · have hlog0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hlog : Real.log ‖s‖ ≤ 2 * ‖s‖ ^ ((1 : ℝ) / 2) := by
      have := Real.log_le_rpow_div hn (ε := 1 / 2) (by norm_num)
      linarith
    calc Real.log ‖f s‖ ≤ C * ‖s‖ * Real.log ‖s‖ := hC s h2
      _ = C * (‖s‖ * Real.log ‖s‖) := by ring
      _ ≤ |C| * (‖s‖ * Real.log ‖s‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg hn hlog0)
      _ ≤ |C| * (‖s‖ * (2 * ‖s‖ ^ ((1 : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hn) (abs_nonneg C)
      _ = 2 * |C| * ‖s‖ ^ (1 + (1 : ℝ) / 2) := by
          rw [Real.rpow_one_add' hn (by norm_num)]; ring
      _ ≤ max M 0 + 2 * |C| * ‖s‖ ^ (1 + (1 : ℝ) / 2) := by
          linarith [le_max_right M 0]
  · have hb : ‖f s‖ ≤ M := hM s (by simpa [Metric.mem_closedBall] using h2.le)
    have := Real.log_le_self (norm_nonneg (f s))
    have : 0 ≤ 2 * |C| * ‖s‖ ^ (1 + (1 : ℝ) / 2) := by positivity
    linarith [le_max_left M 0]

/-- Transfer along `z ↦ 1/2 - i z`: from a global bound on `f` to the bound required by B3' for
`z ↦ f (1/2 - i z)`. -/
lemma growth_comp {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s : ℂ, Real.log ‖f s‖ ≤ A + B * ‖s‖ ^ (1 + (1 : ℝ) / 2)) :
    ∃ C : ℝ, ∀ z : ℂ, 2 ≤ ‖z‖ →
      Real.log ‖f (1 / 2 - I * z)‖ ≤ C * ‖z‖ ^ (1 + (1 : ℝ) / 2) := by
  refine ⟨A + 4 * B, fun z hz => ?_⟩
  set e : ℝ := 1 + (1 : ℝ) / 2
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hw : ‖(1 / 2 : ℂ) - I * z‖ ≤ 2 * ‖z‖ := by
    calc ‖(1 / 2 : ℂ) - I * z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖I * z‖ := norm_sub_le _ _
      _ = 1 / 2 + ‖z‖ := by simp
      _ ≤ 2 * ‖z‖ := by linarith
  have h1 : ‖(1 / 2 : ℂ) - I * z‖ ^ e ≤ (2 * ‖z‖) ^ e :=
    Real.rpow_le_rpow (norm_nonneg _) hw (by norm_num [e])
  have h2 : (2 * ‖z‖) ^ e = (2 : ℝ) ^ e * ‖z‖ ^ e := Real.mul_rpow (by norm_num) hz0
  have h3 : (2 : ℝ) ^ e ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) (show e ≤ 2 by
      norm_num [e])
    norm_num at this ⊢; linarith
  have h4 : 1 ≤ ‖z‖ ^ e := Real.one_le_rpow (by linarith) (by norm_num [e])
  have h5 : 0 ≤ ‖z‖ ^ e := by linarith
  calc Real.log ‖f (1 / 2 - I * z)‖ ≤ A + B * ‖(1 / 2 : ℂ) - I * z‖ ^ e := h _
    _ ≤ A + B * (4 * ‖z‖ ^ e) := by
        gcongr
        calc ‖(1 / 2 : ℂ) - I * z‖ ^ e ≤ (2 : ℝ) ^ e * ‖z‖ ^ e := h2 ▸ h1
          _ ≤ 4 * ‖z‖ ^ e := mul_le_mul_of_nonneg_right h3 h5
    _ ≤ A * ‖z‖ ^ e + B * (4 * ‖z‖ ^ e) := by nlinarith
    _ = (A + 4 * B) * ‖z‖ ^ e := by ring

end WeilRH.HbSum

namespace WeilRH

open HbSum

/-- For `K = ℚ`, the entire `ξ_ℚ` of B1 is `2 ξ` everywhere. -/
theorem HeckePackage.xi_rat (hB : HeckePackage ℚ) (s : ℂ) :
    hB.simplePoles.ξ s = 2 * completedXi s := by
  have hc1 : Continuous hB.simplePoles.ξ := hB.simplePoles.differentiable.continuous
  have hc2 : Continuous fun s => 2 * completedXi s := differentiable_completedXi.continuous.const_mul 2
  have h := Continuous.ext_on DedekindContinuation.SimplePoles.dense_compl_zero_one hc1 hc2
    (fun w hw => by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
      rw [hB.simplePoles.eq_xiK w hw.1 hw.2, xiK_rat _ hw.1 hw.2])
  exact congrFun h s

/-- B1 for `ℚ` gives a growth bound for `F(z) = ξ(1/2 - iz)` of the form B3' requires. -/
theorem riemannXiUpper_growth (hB : HeckePackage ℚ) :
    ∃ C : ℝ, ∀ z : ℂ, 2 ≤ ‖z‖ → Real.log ‖riemannXiUpper z‖ ≤ C * ‖z‖ ^ (1 + (1 : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hB.growth
  obtain ⟨A, B, hA, hB0, h⟩ :=
    log_norm_le_global hB.simplePoles.differentiable.continuous hC
  have h' : ∀ s : ℂ, Real.log ‖completedXi s‖ ≤ A + B * ‖s‖ ^ (1 + (1 : ℝ) / 2) := by
    intro s
    refine le_trans ?_ (h s)
    rw [HeckePackage.xi_rat hB s]
    rcases eq_or_ne (completedXi s) 0 with h0 | h0
    · simp [h0]
    · exact Real.log_le_log (norm_pos_iff.2 h0)
        (by rw [norm_mul]; norm_num; linarith [norm_nonneg (completedXi s)])
  exact growth_comp hA hB0 h'

/-- `F(z) = ξ(1/2 - iz)` is entire. -/
lemma differentiable_riemannXiUpper : Differentiable ℂ riemannXiUpper := by
  unfold riemannXiUpper
  exact differentiable_completedXi.comp (by fun_prop)

/-- `F(0) = ξ(1/2) ≠ 0`. -/
lemma riemannXiUpper_zero_ne : riemannXiUpper 0 ≠ 0 := by
  obtain ⟨h1, -, h3⟩ := F_zero_pos
  intro h0; rw [h1] at h0; rw [h0] at h3; simp at h3

/-- Under B6, `F` has a zero. -/
lemma riemannXiUpper_exists_zero (hR : RiemannVonMangoldt) : ∃ w, riemannXiUpper w = 0 := by
  obtain ⟨ρ, h0, h1, h2⟩ := RvM.exists_nontrivial_zero hR
  refine ⟨I * (ρ - 1 / 2), ?_⟩
  have hw : (1 / 2 : ℂ) - I * (I * (ρ - 1 / 2)) = ρ := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [riemannXiUpper, hw, completedXi_eq_zero_iff]
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    simp at h1; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rintro rfl; simp at h2

/-- **`prop:hb-high`, second clause.** For `F(z) = ξ(1/2 - iz)` and `𝔪 = -F'/F`,
`Im 𝔪(z) > 0` whenever `Im z ≥ 1/2`. CONDITIONAL on B1 for `ℚ` (growth of `ξ`), B3' (locally
uniform Hadamard product with its logarithmic derivative) and B6 (used only to know that `F` has a
zero; with no zeros the sum would vanish). -/
theorem riemannXiUpper_im_neg_logDeriv_pos_of_zero (hB : HeckePackage ℚ)
    (hH : HadamardOrderOneLU) (hz0 : ∃ w, riemannXiUpper w = 0) {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    0 < (-logDeriv riemannXiUpper z).im := by
  have hFd := differentiable_riemannXiUpper
  have hF0 := riemannXiUpper_zero_ne
  set ρ : ZIdx riemannXiUpper → ℂ := ZIdx.pt
  obtain ⟨-, a, b, g, -, hfac, hlog⟩ := hH riemannXiUpper hFd ⟨0, hF0⟩
    (riemannXiUpper_growth hB) ρ
    (fun i hi => hF0 (by have := i.2.1; simp only [ρ, ZIdx.pt] at hi; rwa [hi] at this))
    (fun w _ => ZIdx.exists_iff hFd hF0 w) (fun w _ => ZIdx.card_fiber hFd hF0 w)
  have h00 : analyticOrderNatAt riemannXiUpper 0 = 0 := by
    by_contra h
    exact hF0 ((SymEntire.mult_pos_iff hFd hF0 0).1 (Nat.pos_of_ne_zero h))
  have hfac' : ∀ s, riemannXiUpper s = exp (a + b * s) * g s := by
    intro s; rw [hfac s, h00, pow_zero, mul_one]
  obtain ⟨w, hw⟩ := hz0
  have : Nonempty (ZIdx riemannXiUpper) := ⟨⟨(w, 0), hw, (SymEntire.mult_pos_iff hFd hF0 w).2 hw⟩⟩
  refine HbSum.im_neg_logDeriv_pos ρ hFd riemannXiUpper_neg hfac' hlog
    (riemannXiUpper_ne_zero hz) (fun i => ?_)
  have := riemannXiUpper_eq_zero_mem_strip i.2.1
  simp only [ρ, ZIdx.pt]; linarith

/-- **`prop:hb-high`, second clause** (round 75 form, with B6 supplying the zero). -/
theorem riemannXiUpper_im_neg_logDeriv_pos (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU)
    (hR : RiemannVonMangoldt) {z : ℂ} (hz : 1 / 2 ≤ z.im) :
    0 < (-logDeriv riemannXiUpper z).im :=
  riemannXiUpper_im_neg_logDeriv_pos_of_zero hB hH (riemannXiUpper_exists_zero hR) hz

end WeilRH
