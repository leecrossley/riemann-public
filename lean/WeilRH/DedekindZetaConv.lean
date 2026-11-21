import Mathlib
import WeilRH.CompactifiedNeg

/-!
# Convergence of the Dedekind zeta function on `Re s > 1`

Round 61 groundwork towards an Euler product for `NumberField.dedekindZeta`.

Mathlib (v4.34.1) defines `dedekindZeta K s` as the `L`-series whose `n`-th coefficient is the
number of integral ideals of absolute norm `n`, and proves the class number formula
(`tendsto_sub_one_mul_dedekindZeta_nhdsGT`). It does **not** state that this `L`-series
converges on `Re s > 1`, and it has no Euler product for it (the Euler-product machinery in
`Mathlib.NumberTheory.EulerProduct` is indexed by rational primes and needs a multiplicative
coefficient function).

This file proves what the existing ideal-counting asymptotics give directly:

* `sum_coeff_isBigO`: `∑_{k ≤ n} #{I : N I = k} = O(n)`;
* `LSeriesSummable_coeff`: the Dedekind `L`-series converges absolutely on `Re s > 1`;
* `abscissaOfAbsConv_coeff_le`: its abscissa of absolute convergence is `≤ 1`;
* `dedekindZeta_pos`, `dedekindZeta_ne_zero_of_real`: `ζ_K(x) > 0` for real `x > 1`.

**Not proved here (gap recorded in `lean/README.md`):** the Euler product
`ζ_K(s) = ∏_𝔭 (1 - N𝔭^{-s})⁻¹`, and hence `ζ_K(s) ≠ 0` for *complex* `s` with `Re s > 1`.
The missing input is the multiplicativity of `n ↦ #{I : N I = n}` (unique factorization of
ideals plus the Chinese remainder theorem), or an Euler product indexed by prime ideals.
-/

namespace WeilRH.DedekindZetaConv

open NumberField Filter Ideal Finset Asymptotics
open scoped Topology ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-- The coefficient `a_K(n) = #{I ⊆ 𝓞_K : N I = n}` of the Dedekind `L`-series. -/
noncomputable def coeff (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff K n := Nat.cast_nonneg _

/-- `a_K(1) = 1`: the only ideal of norm one is `𝓞_K`. -/
theorem coeff_one : coeff K 1 = 1 := by
  have : {I : Ideal (𝓞 K) // absNorm I = 1} ≃ Unit :=
    { toFun := fun _ => (), invFun := fun _ => ⟨⊤, absNorm_top⟩,
      left_inv := fun I => Subtype.ext (absNorm_eq_one_iff.mp I.2).symm,
      right_inv := fun _ => rfl }
  simp [coeff]

/-- `dedekindZeta` is the `L`-series of `coeff`. -/
theorem dedekindZeta_eq (s : ℂ) :
    dedekindZeta K s = LSeries (fun n => (coeff K n : ℂ)) s := by
  simp [dedekindZeta, coeff]

/-- The partial sums of the coefficients, divided by `n`, tend to the residue (this is the
counting input of Mathlib's class number formula). -/
theorem tendsto_sum_coeff_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, coeff K k) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue_def]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, coeff, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- `∑_{k ≤ n} a_K(k) = O(n)`. -/
theorem sum_coeff_isBigO :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, coeff K k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h := (tendsto_sum_coeff_div K).isBigO_one ℝ
  have hmul := h.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  simp only [one_mul] at hmul
  refine (hmul.congr' ?_ ?_)
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  · exact Eventually.of_forall fun n => (Real.rpow_one _).symm

/-- **The Dedekind `L`-series converges absolutely on `Re s > 1`.** -/
theorem LSeriesSummable_coeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff K n : ℂ)) s :=
  LSeriesSummable_of_sum_norm_bigO_and_nonneg (sum_coeff_isBigO K) (coeff_nonneg K)
    zero_le_one hs

/-- The abscissa of absolute convergence of the Dedekind `L`-series is at most `1`. -/
theorem abscissaOfAbsConv_coeff_le :
    LSeries.abscissaOfAbsConv (fun n => (coeff K n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_coeff K (by simpa using hy)

/-- **`ζ_K(x) > 0` for real `x > 1`** (as a complex number: real and positive). -/
theorem dedekindZeta_pos {x : ℝ} (hx : 1 < x) : 0 < dedekindZeta K x := by
  rw [dedekindZeta_eq]
  refine LSeries.positive (fun n => ?_) ?_ ?_
  · simpa using coeff_nonneg K n
  · simp [coeff_one]
  · exact (abscissaOfAbsConv_coeff_le K).trans_lt (by exact_mod_cast hx)

theorem dedekindZeta_ne_zero_of_real {x : ℝ} (hx : 1 < x) : dedekindZeta K x ≠ 0 :=
  (dedekindZeta_pos K hx).ne'

/-! ## Consequences for the completed function `ξ_K` -/

section Xi

open WeilRH WeilRH.Arakelov.ZetaOrder Complex

variable {K}

lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => h2pi h.1

/-- The archimedean and conductor factor `|d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` is nonzero on
`Re s > 0`. -/
lemma dedekindGammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : dedekindGammaFactor K s ≠ 0 := by
  unfold dedekindGammaFactor
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => hd h.1

/-- On `Re s > 1`, `ξ_K(s) ≠ 0` as soon as `ζ_K(s) ≠ 0`. -/
theorem xi_ne_zero_of_dedekindZeta_ne_zero {C : DedekindContinuation K} (P : C.SimplePoles)
    {s : ℂ} (hs : 1 < s.re) (hz : dedekindZeta K s ≠ 0) : P.ξ s ≠ 0 := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [Ne, P.xi_eq_zero_iff, C.eq_of_one_lt_re s hs]
  simp [h0, h1, hz, dedekindGammaFactor_ne_zero (by linarith : (0 : ℝ) < s.re)]

/-- **The `NonvanishingRight` hypothesis of rounds 50/60 reduces exactly to `ζ_K ≠ 0` on
`Re s > 1`** (the Euler-product statement still missing from Mathlib). -/
theorem nonvanishingRight_of_dedekindZeta_ne_zero {C : DedekindContinuation K}
    (P : C.SimplePoles) (H : ∀ s : ℂ, 1 < s.re → dedekindZeta K s ≠ 0) :
    NonvanishingRight P :=
  fun s hs => xi_ne_zero_of_dedekindZeta_ne_zero P hs (H s hs)

/-- **Unconditional on the real axis:** `ξ_K(x) ≠ 0` for every real `x > 1`. -/
theorem xi_ne_zero_of_real {C : DedekindContinuation K} (P : C.SimplePoles) {x : ℝ}
    (hx : 1 < x) : P.ξ x ≠ 0 :=
  xi_ne_zero_of_dedekindZeta_ne_zero P (by simpa using hx) (dedekindZeta_ne_zero_of_real K hx)

end Xi

end WeilRH.DedekindZetaConv
