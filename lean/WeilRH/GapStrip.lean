/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Spectral approximation on `L²([-ℓ, ℓ])` (`prop:gap`)

Source: `latex/notes.tex`, subsection `subsec:gap`, Definition `def:residual-gap` and
Proposition `prop:gap`. For a gap datum `(𝓔, A, v, μ)` on `[-ℓ, ℓ]` with gap `d` and `k ∈ 𝓔` with
residual `r = ‖(A - μ) k‖₂` and projection `w = P k` (orthogonal projection onto `ℂ v`):

* (`eq:gap-l2`) `‖k - w‖₂ ≤ r / d`;
* (`eq:gap-strip`) for every `b ≥ 0`, `sup_{|Im z| ≤ b} |k̂(z) - ŵ(z)| ≤ C(ℓ, b) r / d`, with
  `C(ℓ, b) = √(sinh(2bℓ)/b)` for `b > 0` and `C(ℓ, 0) = √(2ℓ)`.

The Fourier transform is that of `def:weil-form` (a), `ĝ(z) = ∫ g(t) e^{izt} dt`.

## Representation

* `L²([-ℓ, ℓ])` is `Lp ℂ 2 (volume.restrict (Icc (-ℓ) ℓ))` (`L2I ℓ`); `hat g z` is the integral of
  `g t * exp(i z t)` against that measure.
* `gap_l2` is stated for any finite-dimensional complex inner product space `E` (every finite-dimensional
  subspace `𝓔` of `L²([-ℓ, ℓ])` is one). The gap is encoded as a lower bound: every eigenvalue `λ` of
  `A|_{v^⊥}` has `d ≤ |λ - μ|`. The manuscript's `d = dist(μ, spec(A|_{v^⊥}))` satisfies it, and the
  case `v^⊥ = 0` (`d = +∞`) is covered by any `d > 0`, since then `k - w = 0`.
* `gap_strip` is stated for a finite-dimensional submodule `𝓔` of `L2I ℓ` and every `z` with
  `|Im z| ≤ b`; the supremum bound is the pointwise bound for all such `z`.
* The unit-vector condition on `v` is not needed for either inequality.
-/

open MeasureTheory Complex ComplexConjugate Set
open scoped InnerProductSpace

namespace WeilRH

namespace Gap

/-! ### The finite-dimensional estimate `eq:gap-l2` -/

section L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The orthogonal complement of an eigenvector of a symmetric map is invariant. -/
theorem orth_invariant {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {v : E} {c : ℂ} (hv : A v = c • v) :
    ∀ x ∈ (ℂ ∙ v)ᗮ, A x ∈ (ℂ ∙ v)ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← hA, hv, inner_smul_left, hx, mul_zero]

/-- A symmetric map whose eigenvalues all lie at distance at least `d ≥ 0` from `μ` satisfies
`d ‖u‖ ≤ ‖T u - μ u‖`. -/
theorem mul_norm_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T : F →ₗ[ℂ] F} (hT : T.IsSymmetric) (μ : ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hgap : ∀ c : ℂ, Module.End.HasEigenvalue T c → d ≤ ‖c - μ‖) (u : F) :
    d * ‖u‖ ≤ ‖T u - (μ : ℂ) • u‖ := by
  have hn : Module.finrank ℂ F = Module.finrank ℂ F := rfl
  have hrep : ∀ i, (hT.eigenvectorBasis hn).repr (T u - (μ : ℂ) • u) i = ((hT.eigenvalues hn i : ℂ) - μ) * (hT.eigenvectorBasis hn).repr u i := by
    intro i
    simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hT.eigenvectorBasis_apply_self_apply hn u i]
    exact (sub_mul _ _ _).symm
  have hsq : (d * ‖u‖) ^ 2 ≤ ‖T u - (μ : ℂ) • u‖ ^ 2 := by
    rw [← (hT.eigenvectorBasis hn).repr.norm_map u,
      ← (hT.eigenvectorBasis hn).repr.norm_map (T u - (μ : ℂ) • u), EuclideanSpace.norm_sq_eq,
      mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hrep i, norm_mul, mul_pow]
    have hlam := hgap _ (hT.hasEigenvalue_eigenvalues hn i)
    gcongr
    exact hlam
  have h1 : 0 ≤ d * ‖u‖ := mul_nonneg hd (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ h1 (norm_nonneg _) two_ne_zero).mp hsq

/-- **`prop:gap`, `eq:gap-l2`.** Let `A` be symmetric on a finite-dimensional inner product space,
`v` an eigenvector, `μ ∈ ℝ`, and `d > 0` with `d ≤ |λ - μ|` for every eigenvalue `λ` of `A` on
`v^⊥`. Then `‖k - w‖ ≤ r / d`, where `w` is the orthogonal projection of `k` onto `ℂ v` and
`r = ‖(A - μ) k‖`. -/
theorem gap_l2 [FiniteDimensional ℂ E] {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {v : E} {c : ℂ} (hv : A v = c • v) (μ : ℝ)
    {d : ℝ} (hd : 0 < d)
    (hgap : ∀ c' : ℂ, Module.End.HasEigenvalue (A.restrict (orth_invariant hA hv)) c' →
      d ≤ ‖c' - μ‖) (k : E) :
    ‖k - (ℂ ∙ v).starProjection k‖ ≤ ‖A k - (μ : ℂ) • k‖ / d := by
  set K := (ℂ ∙ v)ᗮ
  set w := (ℂ ∙ v).starProjection k
  have hu : k - w ∈ K := (ℂ ∙ v).sub_starProjection_mem_orthogonal k
  have hw : w ∈ ℂ ∙ v := (ℂ ∙ v).starProjection_apply_mem k
  -- `(A - μ) w ∈ ℂ v` and `(A - μ)(k - w) ∈ v^⊥`
  have hAw : A w - (μ : ℂ) • w ∈ ℂ ∙ v := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ha, map_smul, hv]
    apply Submodule.sub_mem <;>
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hAu : A (k - w) - (μ : ℂ) • (k - w) ∈ K :=
    K.sub_mem (orth_invariant hA hv _ hu) (K.smul_mem _ hu)
  have hsplit : A k - (μ : ℂ) • k = (A (k - w) - (μ : ℂ) • (k - w)) + (A w - (μ : ℂ) • w) := by
    rw [map_sub, smul_sub]; abel
  have horth : ⟪A (k - w) - (μ : ℂ) • (k - w), A w - (μ : ℂ) • w⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hAw hAu
  have hge : ‖A (k - w) - (μ : ℂ) • (k - w)‖ ≤ ‖A k - (μ : ℂ) • k‖ := by
    rw [hsplit]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    nlinarith [norm_nonneg (A (k - w) - (μ : ℂ) • (k - w)),
      norm_nonneg (A (k - w) - (μ : ℂ) • (k - w) + (A w - (μ : ℂ) • w)),
      sq_nonneg ‖A w - (μ : ℂ) • w‖]
  -- the spectral estimate on `v^⊥`
  have hres := mul_norm_le (hA.restrict_invariant (orth_invariant hA hv)) μ hd.le hgap
    ⟨k - w, hu⟩
  have hnorm : ‖(A.restrict (orth_invariant hA hv)) ⟨k - w, hu⟩ - (μ : ℂ) • ⟨k - w, hu⟩‖ =
      ‖A (k - w) - (μ : ℂ) • (k - w)‖ := rfl
  have hnorm' : ‖(⟨k - w, hu⟩ : K)‖ = ‖k - w‖ := rfl
  rw [hnorm, hnorm'] at hres
  rw [le_div_iff₀ hd, mul_comm]
  exact hres.trans hge

end L2

/-! ### Fourier transforms on `L²([-ℓ, ℓ])` -/

/-- Lebesgue measure on `[-ℓ, ℓ]`. -/
noncomputable abbrev μI (ℓ : ℝ) : Measure ℝ := volume.restrict (Icc (-ℓ) ℓ)

/-- `L²([-ℓ, ℓ])`, functions on `ℝ` modulo equality a.e. on `[-ℓ, ℓ]`. -/
noncomputable abbrev L2I (ℓ : ℝ) := Lp ℂ 2 (μI ℓ)

/-- The Fourier transform `ĝ(z) = ∫_{-ℓ}^{ℓ} g(t) e^{izt} dt` of `def:weil-form` (a). -/
noncomputable def hat {ℓ : ℝ} (g : L2I ℓ) (z : ℂ) : ℂ := ∫ t, g t * cexp (I * z * t) ∂μI ℓ

/-- The constant `C(ℓ, b)` of `def:residual-gap` (c). -/
noncomputable def C (ℓ b : ℝ) : ℝ :=
  if b = 0 then Real.sqrt (2 * ℓ) else Real.sqrt (Real.sinh (2 * b * ℓ) / b)

lemma norm_cexp_I_mul (z : ℂ) (t : ℝ) : ‖cexp (I * z * t)‖ = Real.exp (-(z.im * t)) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma kernel_memLp (ℓ : ℝ) (z : ℂ) :
    MemLp (fun t : ℝ => conj (cexp (I * z * t))) 2 (μI ℓ) := by
  refine MemLp.of_bound (C := Real.exp (|z.im| * |ℓ|))
    (by fun_prop : Continuous fun t : ℝ => conj (cexp (I * z * t))).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_
  rw [RCLike.norm_conj, norm_cexp_I_mul, Real.exp_le_exp]
  have ht' : |t| ≤ |ℓ| := (abs_le.mpr ⟨ht.1, ht.2⟩).trans (le_abs_self ℓ)
  calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
    _ = |z.im| * |t| := abs_mul _ _
    _ ≤ |z.im| * |ℓ| := by gcongr

/-- The kernel `t ↦ conj(e^{izt})` as an element of `L²([-ℓ, ℓ])`. -/
noncomputable def kernel (ℓ : ℝ) (z : ℂ) : L2I ℓ := (kernel_memLp ℓ z).toLp _

theorem hat_eq_inner {ℓ : ℝ} (g : L2I ℓ) (z : ℂ) : hat g z = ⟪kernel ℓ z, g⟫_ℂ := by
  rw [L2.inner_def, hat]
  refine integral_congr_ae ?_
  filter_upwards [(kernel_memLp ℓ z).coeFn_toLp] with t ht
  rw [kernel, ht]
  simp [mul_comm]

theorem hat_sub {ℓ : ℝ} (f g : L2I ℓ) (z : ℂ) : hat (f - g) z = hat f z - hat g z := by
  rw [hat_eq_inner, hat_eq_inner, hat_eq_inner, inner_sub_right]

theorem norm_kernel_sq (ℓ : ℝ) (z : ℂ) :
    ‖kernel ℓ z‖ ^ 2 = ∫ t, Real.exp (-(2 * z.im * t)) ∂μI ℓ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  have hcongr : (fun t => ⟪(kernel ℓ z : ℝ → ℂ) t, (kernel ℓ z : ℝ → ℂ) t⟫_ℂ) =ᵐ[μI ℓ]
      fun t => ((Real.exp (-(2 * z.im * t)) : ℝ) : ℂ) := by
    filter_upwards [(kernel_memLp ℓ z).coeFn_toLp] with t ht
    rw [kernel, ht, inner_self_eq_norm_sq_to_K, RCLike.norm_conj, norm_cexp_I_mul]
    have hr : Real.exp (-(z.im * t)) ^ 2 = Real.exp (-(2 * z.im * t)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← hr]; exact (Complex.ofReal_pow _ _).symm
  rw [integral_congr_ae hcongr, integral_complex_ofReal]
  simp

/-- `∫_{-ℓ}^{ℓ} e^{-2yt} dt = ∫_{-ℓ}^{ℓ} cosh(2yt) dt`. -/
lemma integral_exp_eq_cosh {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (y : ℝ) :
    ∫ t, Real.exp (-(2 * y * t)) ∂μI ℓ = ∫ t in (-ℓ)..ℓ, Real.cosh (2 * y * t) := by
  have hle : -ℓ ≤ ℓ := by linarith
  rw [μI, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hsym : ∫ t in (-ℓ)..ℓ, Real.exp (-(2 * y * t)) = ∫ t in (-ℓ)..ℓ, Real.exp (2 * y * t) := by
    have := intervalIntegral.integral_comp_neg (a := -ℓ) (b := ℓ)
      (fun t => Real.exp (2 * y * t))
    simp only [neg_neg, mul_neg] at this
    exact this
  have hint : ∀ c : ℝ, IntervalIntegrable (fun t => Real.exp (c * t)) volume (-ℓ) ℓ := fun c =>
    (by fun_prop : Continuous fun t => Real.exp (c * t)).intervalIntegrable _ _
  have hcosh : (fun t => Real.cosh (2 * y * t)) =
      fun t => (Real.exp (2 * y * t) + Real.exp (-(2 * y * t))) / 2 := by
    funext t; rw [Real.cosh_eq]
  rw [hcosh, intervalIntegral.integral_div, intervalIntegral.integral_add (hint _)]
  · rw [← hsym]; ring
  · simpa [neg_mul] using hint (-(2 * y))

lemma integral_cosh_mono {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {y b : ℝ} (hy : |y| ≤ b) :
    ∫ t in (-ℓ)..ℓ, Real.cosh (2 * y * t) ≤ ∫ t in (-ℓ)..ℓ, Real.cosh (2 * b * t) := by
  refine intervalIntegral.integral_mono_on (by linarith)
    ((by fun_prop : Continuous fun t => Real.cosh (2 * y * t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => Real.cosh (2 * b * t)).intervalIntegrable _ _)
    fun t _ => ?_
  have hb : |b| = b := abs_of_nonneg ((abs_nonneg y).trans hy)
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_mul, abs_mul, hb]
  gcongr

lemma integral_cosh_eq (ℓ : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ t in (-ℓ)..ℓ, Real.cosh (2 * b * t) = Real.sinh (2 * b * ℓ) / b := by
  have h2b : (2 * b) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := -ℓ) (b := ℓ) Real.cosh h2b
  rw [this]
  have hderiv : ∀ x ∈ Set.uIcc (2 * b * -ℓ) (2 * b * ℓ), HasDerivAt Real.sinh (Real.cosh x) x :=
    fun x _ => Real.hasDerivAt_sinh x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Real.continuous_cosh.intervalIntegrable _ _)]
  rw [mul_neg, Real.sinh_neg, smul_eq_mul]
  field_simp
  ring

lemma integral_exp_zero (ℓ : ℝ) :
    ∫ t in (-ℓ)..ℓ, Real.cosh (2 * 0 * t) = 2 * ℓ := by
  simp; ring

/-- For `|Im z| ≤ b`, `‖kernel ℓ z‖ ≤ C(ℓ, b)`. -/
theorem norm_kernel_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : |z.im| ≤ b) :
    ‖kernel ℓ z‖ ≤ C ℓ b := by
  have hsq : ‖kernel ℓ z‖ ^ 2 ≤ ∫ t in (-ℓ)..ℓ, Real.cosh (2 * b * t) := by
    rw [norm_kernel_sq, integral_exp_eq_cosh hℓ]
    exact integral_cosh_mono hℓ hz
  rw [C]
  split_ifs with hb0
  · subst hb0
    rw [integral_exp_zero ℓ] at hsq
    exact Real.le_sqrt_of_sq_le hsq
  · rw [integral_cosh_eq ℓ (lt_of_le_of_ne hb (Ne.symm hb0))] at hsq
    exact Real.le_sqrt_of_sq_le hsq

/-- For `|Im z| = b > 0`, `‖kernel ℓ z‖ = C(ℓ, b)` exactly. -/
theorem norm_kernel_eq {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : |z.im| = b) :
    ‖kernel ℓ z‖ = C ℓ b := by
  have hsq : ‖kernel ℓ z‖ ^ 2 = Real.sinh (2 * b * ℓ) / b := by
    rw [norm_kernel_sq, integral_exp_eq_cosh hℓ, ← integral_cosh_eq ℓ hb]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have habs : |2 * z.im * t| = |2 * b * t| := by
      rw [abs_mul, abs_mul (2 * b), abs_mul, abs_mul, hz, abs_of_pos hb]
    rw [← Real.cosh_abs (2 * z.im * t), habs, Real.cosh_abs]
  simp only [C, hb.ne', ite_false]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- Cauchy–Schwarz on the strip: `|ĝ(z)| ≤ C(ℓ, b) ‖g‖₂` for `|Im z| ≤ b`. -/
theorem norm_hat_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {b : ℝ} (hb : 0 ≤ b) (g : L2I ℓ) {z : ℂ}
    (hz : |z.im| ≤ b) : ‖hat g z‖ ≤ C ℓ b * ‖g‖ := by
  rw [hat_eq_inner]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_kernel_le hℓ hb hz) (norm_nonneg _))

/-- **`prop:gap`.** Let `ℓ > 0`, let `𝓔 ⊂ L²([-ℓ, ℓ])` be finite-dimensional with a symmetric `A`,
eigenvector `v`, `μ ∈ ℝ` and gap `d > 0` (every eigenvalue `λ` of `A` on `v^⊥` has `d ≤ |λ - μ|`),
and let `k ∈ 𝓔` have residual `r = ‖(A - μ)k‖₂` and projection `w`. Then `‖k - w‖₂ ≤ r / d`
(`eq:gap-l2`) and `|k̂(z) - ŵ(z)| ≤ C(ℓ, b) r / d` whenever `|Im z| ≤ b`, `b ≥ 0`
(`eq:gap-strip`). -/
theorem gap {ℓ : ℝ} (hℓ : 0 < ℓ) (𝓔 : Submodule ℂ (L2I ℓ)) [FiniteDimensional ℂ 𝓔]
    {A : 𝓔 →ₗ[ℂ] 𝓔} (hA : A.IsSymmetric) {v : 𝓔} {c : ℂ} (hv : A v = c • v) (μ : ℝ)
    {d : ℝ} (hd : 0 < d)
    (hgap : ∀ c' : ℂ, Module.End.HasEigenvalue (A.restrict (orth_invariant hA hv)) c' →
      d ≤ ‖c' - μ‖) (k : 𝓔) :
    ‖((k : L2I ℓ) - ((ℂ ∙ v).starProjection k : 𝓔))‖ ≤ ‖A k - (μ : ℂ) • k‖ / d ∧
      ∀ b : ℝ, 0 ≤ b → ∀ z : ℂ, |z.im| ≤ b →
        ‖hat (k : L2I ℓ) z - hat (((ℂ ∙ v).starProjection k : 𝓔) : L2I ℓ) z‖ ≤
          C ℓ b * (‖A k - (μ : ℂ) • k‖ / d) := by
  have h1 := gap_l2 hA hv μ hd hgap k
  rw [← Submodule.norm_coe, Submodule.coe_sub] at h1
  refine ⟨h1, fun b hb z hz => ?_⟩
  rw [← hat_sub]
  refine (norm_hat_le hℓ.le hb _ hz).trans ?_
  have hC : 0 ≤ C ℓ b := by rw [C]; split_ifs <;> exact Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_left h1 hC

end Gap

end WeilRH
