/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.GapStrip
import WeilRH.HilbertSelfAdjoint

/-!
# Three examples on spectral approximation (`prop:R16`)

Source: `latex/notes.tex`, Definitions `def:Fminus`, `def:R16-examples` and Proposition `prop:R16`.

* (a), (i): `A_δ = diag(0, δ, 1)` on `ℂ³`, `k = (1, 1, 0)`, `P_δ` the orthogonal projection onto
  `ker A_δ`. For `δ > 0`, `‖A_δ k‖ = δ` and `‖k - P_δ k‖ = 1` (`norm_A_k`, `norm_k_sub_proj`).
* (b), (ii): for `b > 0`, `ℓ ≥ 1`, `f_ℓ = e^{-bℓ}(1_{[ℓ-1,ℓ]} + 1_{[-ℓ,-ℓ+1]})` is even, has
  `‖f_ℓ‖₂ = √2 e^{-bℓ}`, `𝓕₋f_ℓ(ib) = (1 - e^{-b})/b + e^{-2bℓ}(e^b - 1)/b → (1 - e^{-b})/b > 0`,
  and for `Im z = b` the supremum of `|𝓕₋ g(z)|` over `g` supported in `[-ℓ, ℓ]` with `‖g‖₂ ≤ 1`
  is `√(sinh(2bℓ)/b)` (`f_even`, `norm_f`, `Fminus_f`, `tendsto_Fminus_f`, `isGreatest_Fminus`).
* (c), (iii): `A e_n = n² e_n` on `ℓ²(ℕ_{≥1})` with its maximal domain; `x_n = e_n / n` has
  `‖x_n‖ → 0` and `‖A x_n‖ = n` (`tendsto_norm_x`, `norm_A_x`).

## Representation

* `A_δ` is the linear map `x ↦ (0, δ x₁, x₂)` on `EuclideanSpace ℂ (Fin 3)`, i.e. `diag(0, δ, 1)`.
* `𝓕₋ g(z) = ∫ g(t) e^{-izt} dt` (`Fminus`). For the supremum clause, "`g ∈ L²(ℝ)` supported in
  `[-ℓ, ℓ]`" is an element of `L²([-ℓ, ℓ])` (`Gap.L2I ℓ`), and `𝓕₋ g(z) = ĝ(-z)` with `ĝ` from
  `GapStrip`; the supremum is attained (`IsGreatest`).
* `‖f_ℓ‖₂` is `√(∫ |f_ℓ|²)` over `ℝ`.
* `ℓ²(ℕ_{≥1})` is `lp (fun _ : ℕ+ => ℂ) 2` with its standard Hilbert basis, and `A` is the diagonal
  operator `Hilbert.Diag.op` with `τ_n = n²`, whose domain is `{x : (n² ⟪e_n, x⟫)_n ∈ ℓ²}`, the
  manuscript's `{∑ c_n e_n : ∑ n⁴ |c_n|² < ∞}`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped InnerProductSpace

namespace WeilRH

namespace R16

/-! ### (i) A small residual far from the eigenvector -/

/-- `A_δ = diag(0, δ, 1)` on `ℂ³`. -/
noncomputable def A (δ : ℝ) : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun x := WithLp.toLp 2 ![0, (δ : ℂ) * x.ofLp 1, x.ofLp 2]
  map_add' x y := by
    ext i; fin_cases i <;> simp [mul_add]
  map_smul' c x := by
    ext i; fin_cases i <;> simp; ring

/-- `k = (1, 1, 0)`. -/
noncomputable def k : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 1, 0]

/-- `e₀ = (1, 0, 0)`. -/
noncomputable def e0 : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]

lemma norm_toLp3 (a b c : ℂ) :
    ‖(WithLp.toLp 2 ![a, b, c] : EuclideanSpace ℂ (Fin 3))‖ =
      Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp

lemma mem_ker_iff {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℂ (Fin 3)) :
    x ∈ LinearMap.ker (A δ) ↔ x.ofLp 1 = 0 ∧ x.ofLp 2 = 0 := by
  have hδ' : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := congrArg (fun y : EuclideanSpace ℂ (Fin 3) => y.ofLp 1) h
    have h2 := congrArg (fun y : EuclideanSpace ℂ (Fin 3) => y.ofLp 2) h
    simp [A] at h1 h2
    exact ⟨h1.resolve_left hδ.ne', h2⟩
  · rintro ⟨h1, h2⟩
    ext i; fin_cases i <;> simp [A, h1, h2]

/-- `P_δ k = e₀`. -/
theorem proj_k {δ : ℝ} (hδ : 0 < δ) : (LinearMap.ker (A δ)).starProjection k = e0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [mem_ker_iff hδ]; simp [e0]
  · rw [mem_ker_iff hδ] at hw
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [k, e0, dotProduct, Fin.sum_univ_three, hw.1, hw.2]

/-- **`prop:R16` (i), first equality.** `‖A_δ k‖ = δ`. -/
theorem norm_A_k {δ : ℝ} (hδ : 0 < δ) : ‖A δ k‖ = δ := by
  change ‖(WithLp.toLp 2 ![0, (δ : ℂ) * k.ofLp 1, k.ofLp 2] : EuclideanSpace ℂ (Fin 3))‖ = δ
  rw [norm_toLp3]
  simp [k, abs_of_pos hδ, Real.sqrt_sq hδ.le]

/-- **`prop:R16` (i), second equality.** `‖k - P_δ k‖ = 1`. -/
theorem norm_k_sub_proj {δ : ℝ} (hδ : 0 < δ) :
    ‖k - (LinearMap.ker (A δ)).starProjection k‖ = 1 := by
  rw [proj_k hδ]
  have : k - e0 = (WithLp.toLp 2 ![0, 1, 0] : EuclideanSpace ℂ (Fin 3)) := by
    ext i; fin_cases i <;> simp [k, e0]
  rw [this, norm_toLp3]
  simp

/-! ### (ii) Strip values of compactly supported functions -/

/-- The negative-sign Fourier transform `𝓕₋ g(z) = ∫ g(t) e^{-izt} dt` (`def:Fminus`). -/
noncomputable def Fminus (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t, g t * cexp (-(I * z * t))

/-- `f_ℓ = e^{-bℓ}(1_{[ℓ-1,ℓ]} + 1_{[-ℓ,-ℓ+1]})` (`def:R16-examples` (b)). -/
noncomputable def f (b ℓ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(b * ℓ)) * ((Icc (ℓ - 1) ℓ).indicator 1 t + (Icc (-ℓ) (-ℓ + 1)).indicator 1 t)

/-- `f_ℓ` is even. -/
theorem f_even (b ℓ t : ℝ) : f b ℓ (-t) = f b ℓ t := by
  have h1 : (Icc (ℓ - 1) ℓ).indicator (1 : ℝ → ℝ) (-t) = (Icc (-ℓ) (-ℓ + 1)).indicator 1 t := by
    by_cases ht : t ∈ Icc (-ℓ) (-ℓ + 1)
    · have : -t ∈ Icc (ℓ - 1) ℓ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [indicator_of_mem this, indicator_of_mem ht]; rfl
    · have : -t ∉ Icc (ℓ - 1) ℓ := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_notMem this, indicator_of_notMem ht]
  have h2 : (Icc (-ℓ) (-ℓ + 1)).indicator (1 : ℝ → ℝ) (-t) = (Icc (ℓ - 1) ℓ).indicator 1 t := by
    by_cases ht : t ∈ Icc (ℓ - 1) ℓ
    · have : -t ∈ Icc (-ℓ) (-ℓ + 1) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [indicator_of_mem this, indicator_of_mem ht]; rfl
    · have : -t ∉ Icc (-ℓ) (-ℓ + 1) := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [indicator_of_notMem this, indicator_of_notMem ht]
  rw [f, f, h1, h2, add_comm]

lemma integral_exp_mul_Icc {b : ℝ} (hb : b ≠ 0) {u v : ℝ} (huv : u ≤ v) :
    ∫ t in Icc u v, Real.exp (b * t) = (Real.exp (b * v) - Real.exp (b * u)) / b := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
  have hderiv : ∀ x ∈ uIcc u v, HasDerivAt (fun t => Real.exp (b * t) / b) (Real.exp (b * x)) x := by
    intro x _
    have := ((hasDerivAt_id x).const_mul b).exp.div_const b
    simp only [id_eq, mul_one] at this
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t => Real.exp (b * t)).intervalIntegrable _ _)]
  ring

lemma integrable_indicator_exp (b u v : ℝ) :
    Integrable ((Icc u v).indicator fun t => Real.exp (b * t)) :=
  ((by fun_prop : Continuous fun t => Real.exp (b * t)).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

/-- **`prop:R16` (ii), the value at `ib`.**
`𝓕₋f_ℓ(ib) = (1 - e^{-b})/b + e^{-2bℓ}(e^b - 1)/b`. -/
theorem Fminus_f {b : ℝ} (ℓ : ℝ) (hb : 0 < b) :
    Fminus (fun t => (f b ℓ t : ℂ)) (b * I) =
      (((1 - Real.exp (-b)) / b + Real.exp (-(2 * b * ℓ)) * ((Real.exp b - 1) / b) : ℝ) : ℂ) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : ∀ t : ℝ, (f b ℓ t : ℂ) * cexp (-(I * (b * I) * t)) =
      ((Real.exp (-(b * ℓ)) * ((Icc (ℓ - 1) ℓ).indicator (fun t => Real.exp (b * t)) t +
        (Icc (-ℓ) (-ℓ + 1)).indicator (fun t => Real.exp (b * t)) t) : ℝ) : ℂ) := by
    intro t
    have hexp : cexp (-(I * (b * I) * t)) = ((Real.exp (b * t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1
      have : I * (b * I) * t = -(b * t) := by
        rw [mul_comm (b : ℂ) I, ← mul_assoc, I_mul_I]; push_cast; ring
      rw [this, neg_neg]; push_cast; ring
    rw [hexp, f]
    push_cast
    simp only [indicator, Pi.one_apply, mem_Icc]
    split_ifs <;> push_cast <;> ring
  rw [Fminus]
  simp_rw [hint]
  rw [integral_complex_ofReal, integral_const_mul,
    integral_add (integrable_indicator_exp b _ _) (integrable_indicator_exp b _ _),
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc,
    integral_exp_mul_Icc hb0 (by linarith), integral_exp_mul_Icc hb0 (by linarith)]
  congr 1
  have e1 : Real.exp (b * (ℓ - 1)) = Real.exp (b * ℓ) * Real.exp (-b) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (b * (-ℓ + 1)) = Real.exp (-(b * ℓ)) * Real.exp b := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (b * -ℓ) = Real.exp (-(b * ℓ)) := by ring_nf
  have e4 : Real.exp (-(2 * b * ℓ)) = Real.exp (-(b * ℓ)) * Real.exp (-(b * ℓ)) := by
    rw [← Real.exp_add]; ring_nf
  have e5 : Real.exp (-(b * ℓ)) * Real.exp (b * ℓ) = 1 := by
    rw [← Real.exp_add]; simp
  rw [e1, e2, e3, e4]
  calc _ = (Real.exp (-(b * ℓ)) * Real.exp (b * ℓ)) * ((1 - Real.exp (-b)) / b) +
        Real.exp (-(b * ℓ)) * Real.exp (-(b * ℓ)) * ((Real.exp b - 1) / b) := by ring
    _ = _ := by rw [e5, one_mul]

/-- **`prop:R16` (ii), the limit.** `𝓕₋f_ℓ(ib) → (1 - e^{-b})/b > 0` as `ℓ → ∞`. -/
theorem tendsto_Fminus_f {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ℓ : ℝ => (1 - Real.exp (-b)) / b + Real.exp (-(2 * b * ℓ)) * ((Real.exp b - 1) / b))
      atTop (𝓝 ((1 - Real.exp (-b)) / b)) ∧ 0 < (1 - Real.exp (-b)) / b := by
  refine ⟨?_, ?_⟩
  · have h0 : Tendsto (fun ℓ : ℝ => Real.exp (-(2 * b * ℓ))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun ℓ : ℝ => (2 * b) * ℓ) atTop atTop :=
        tendsto_id.const_mul_atTop (by positivity)
      exact tendsto_neg_atTop_atBot.comp this
    have := (tendsto_const_nhds (x := (1 - Real.exp (-b)) / b)).add
      (h0.mul_const ((Real.exp b - 1) / b))
    simpa using this
  · have : Real.exp (-b) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (by linarith) hb

/-- **`prop:R16` (ii), the norm.** `‖f_ℓ‖₂ = √2 e^{-bℓ}` for `ℓ ≥ 1`. -/
theorem norm_f (b : ℝ) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    Real.sqrt (∫ t, ‖(f b ℓ t : ℂ)‖ ^ 2) = Real.sqrt 2 * Real.exp (-(b * ℓ)) := by
  set A := Icc (ℓ - 1) ℓ
  set B := Icc (-ℓ) (-ℓ + 1)
  have hAB : volume (A ∩ B) = 0 := by
    refine measure_mono_null (t := Icc (ℓ - 1) (-ℓ + 1)) ?_ ?_
    · rintro t ⟨hA, hB⟩; exact ⟨hA.1, hB.2⟩
    · rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
  have hae : (fun t => ‖(f b ℓ t : ℂ)‖ ^ 2) =ᵐ[volume]
      fun t => Real.exp (-(b * ℓ)) ^ 2 * (A.indicator 1 t + B.indicator 1 t) := by
    have hnull : ∀ᵐ t ∂volume, t ∉ A ∩ B := measure_eq_zero_iff_ae_notMem.mp hAB
    filter_upwards [hnull] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, f]
    simp only [indicator, Pi.one_apply]
    split_ifs with h1 h2 h2
    · exact absurd ⟨h1, h2⟩ ht
    · ring
    · ring
    · ring
  have hiA : Integrable (A.indicator (1 : ℝ → ℝ)) :=
    (integrableOn_const (by simp [A, Real.volume_Icc])).integrable_indicator measurableSet_Icc
  have hiB : Integrable (B.indicator (1 : ℝ → ℝ)) :=
    (integrableOn_const (by simp [B, Real.volume_Icc])).integrable_indicator measurableSet_Icc
  rw [integral_congr_ae hae, integral_const_mul, integral_add hiA hiB,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
  rw [Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  rw [show Real.exp (-(b * ℓ)) ^ 2 * (ℓ - (ℓ - 1) + (-ℓ + 1 - -ℓ)) =
      (Real.sqrt 2 * Real.exp (-(b * ℓ))) ^ 2 by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring]
  exact Real.sqrt_sq (by positivity)

/-- **`prop:R16` (ii), the supremum.** For `Im z = b > 0` and `ℓ > 0`, the supremum of `|𝓕₋ g(z)|`
over `g ∈ L²([-ℓ, ℓ])` with `‖g‖₂ ≤ 1` is `√(sinh(2bℓ)/b)`, and it is attained. Here
`𝓕₋ g(z) = ĝ(-z)`. -/
theorem isGreatest_Fminus {b ℓ : ℝ} (hb : 0 < b) (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im = b) :
    IsGreatest {r : ℝ | ∃ g : Gap.L2I ℓ, ‖g‖ ≤ 1 ∧ ‖Gap.hat g (-z)‖ = r}
      (Real.sqrt (Real.sinh (2 * b * ℓ) / b)) := by
  have hz' : |(-z).im| = b := by rw [neg_im, abs_neg, hz, abs_of_pos hb]
  have hC : Gap.C ℓ b = Real.sqrt (Real.sinh (2 * b * ℓ) / b) := by
    simp only [Gap.C, hb.ne', ite_false]
  have hK := Gap.norm_kernel_eq hℓ.le hb hz'
  have hpos : 0 < Real.sinh (2 * b * ℓ) / b := div_pos (Real.sinh_pos_iff.mpr (by positivity)) hb
  have hKpos : 0 < ‖Gap.kernel ℓ (-z)‖ := by rw [hK, hC]; exact Real.sqrt_pos.mpr hpos
  refine ⟨⟨(‖Gap.kernel ℓ (-z)‖⁻¹ : ℂ) • Gap.kernel ℓ (-z), ?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKpos,
      inv_mul_cancel₀ hKpos.ne']
  · rw [Gap.hat_eq_inner, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKpos, norm_pow]
    rw [RCLike.norm_ofReal, abs_of_pos hKpos, ← hC, ← hK]
    field_simp
  · rintro r ⟨g, hg, rfl⟩
    rw [← hC]
    calc ‖Gap.hat g (-z)‖ ≤ Gap.C ℓ b * ‖g‖ := Gap.norm_hat_le hℓ.le hb.le g hz'.le
      _ ≤ Gap.C ℓ b * 1 := by
        gcongr
        rw [Gap.C, if_neg hb.ne']; exact Real.sqrt_nonneg _
      _ = Gap.C ℓ b := mul_one _

/-! ### (iii) Small vectors with large images -/

/-- `ℓ²(ℕ_{≥1})`. -/
noncomputable abbrev H := lp (fun _ : ℕ+ => ℂ) 2

/-- The standard Hilbert basis `(e_n)_{n ≥ 1}` of `ℓ²(ℕ_{≥1})`. -/
noncomputable def e : HilbertBasis ℕ+ ℂ H := default

/-- `A e_n = n² e_n` with its maximal domain (`def:R16-examples` (c)). -/
noncomputable def Aop : H →ₗ.[ℂ] H := Hilbert.Diag.op e (fun n => ((n : ℕ) : ℝ) ^ 2)

/-- `x_n = e_n / n`, as an element of the domain of `A`. -/
noncomputable def x (n : ℕ+) : Aop.domain :=
  ((((n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • ⟨e n, Hilbert.Diag.basis_mem_domain e _ n⟩

lemma norm_e (n : ℕ+) : ‖e n‖ = 1 := e.orthonormal.1 n

theorem norm_x (n : ℕ+) : ‖(x n : H)‖ = ((n : ℕ) : ℝ)⁻¹ := by
  rw [x, Submodule.coe_smul, norm_smul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by exact_mod_cast n.pos))]

/-- **`prop:R16` (iii), first half.** `‖x_n‖ → 0`. -/
theorem tendsto_norm_x : Tendsto (fun n : ℕ+ => ‖(x n : H)‖) atTop (𝓝 0) := by
  simp_rw [norm_x]
  have : Tendsto (fun n : ℕ+ => ((n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
  exact tendsto_inv_atTop_zero.comp this

/-- **`prop:R16` (iii), second half.** `‖A x_n‖ = n`. -/
theorem norm_A_x (n : ℕ+) : ‖Aop (x n)‖ = (n : ℕ) := by
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  rw [x, LinearPMap.map_smul]
  erw [Hilbert.Diag.op_basis]
  rw [norm_smul, norm_smul, norm_e, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

end R16

end WeilRH
