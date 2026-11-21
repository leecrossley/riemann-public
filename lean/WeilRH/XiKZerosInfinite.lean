/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.XiKHadamard
import WeilRH.DedekindZetaConv

/-!
# `ξ_K` has infinitely many zeros (round 75)

Source: `latex/notes.tex`, `thm:kun-square` (`item:ks-mult`) and `prop:kun-AW6` use that `ξ_K` has
infinitely many zeros. Here: under B1 (`HeckePackage K`) and B3 (`HadamardOrderOne`, implied by B3'),
the zeros of `ξ_K` listed with multiplicity form an infinite type (`Hecke.zeroIdx_infinite`).

Proof. If there were finitely many zeros, the Hadamard product would be a finite product, so
`‖ξ_K(x)‖ ≤ e^{A + B x}` for real `x ≥ 0`. But at `x = 2n`,
`‖ξ_K(2n)‖ ≥ ‖Γ_ℝ(2n)‖^{r₁} ‖Γ_ℂ(2n)‖^{r₂} ≥ (n-1)!/(2π)^{2n}` once the right side is `≥ 1`
(`|d_K|^n ≥ 1`, `ζ_K(2n) ≥ 1`, `r₁ + r₂ ≥ 1`), and `(n-1)!` beats every exponential.
-/

open Complex Filter Topology NumberField
open scoped Nat

namespace WeilRH.Hecke

variable {K : Type} [Field K] [NumberField K]

/-- `Re ζ_K(x) ≥ 1` for real `x > 1` (the first term of the Dirichlet series is `1`, the others are
nonnegative). -/
lemma one_le_re_dedekindZeta {x : ℝ} (hx : 1 < x) : 1 ≤ (dedekindZeta K x).re := by
  have hs := DedekindZetaConv.LSeriesSummable_coeff K (s := (x : ℂ)) (by simpa using hx)
  have h := Complex.reCLM.hasSum hs.LSeriesHasSum
  rw [← DedekindZetaConv.dedekindZeta_eq] at h
  have hterm : ∀ n : ℕ, n ≠ 0 → LSeries.term (fun n => (DedekindZetaConv.coeff K n : ℂ)) x n =
      ((DedekindZetaConv.coeff K n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]
    simp
  have hnn : ∀ n : ℕ, 0 ≤ Complex.reCLM
      (LSeries.term (fun n => (DedekindZetaConv.coeff K n : ℂ)) x n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [hterm n hn, Complex.reCLM_apply, ofReal_re]
      exact div_nonneg (DedekindZetaConv.coeff_nonneg K n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) x)
  have h1 := le_hasSum h 1 (fun j _ => hnn j)
  rw [hterm 1 one_ne_zero, Complex.reCLM_apply, ofReal_re, DedekindZetaConv.coeff_one] at h1
  simpa using h1

/-- `r₁ + r₂ ≥ 1`. -/
lemma one_le_nrPlaces : 1 ≤ InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

/-- `c_n = (n-1)!/(2π)^{2n}`. -/
noncomputable def cfac (n : ℕ) : ℝ := ((n - 1)! : ℝ) / (2 * Real.pi) ^ (2 * n)

lemma cfac_le_norm_Gammaℝ {n : ℕ} (hn : 1 ≤ n) : cfac n ≤ ‖Gammaℝ (2 * n)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (-(2 * ((m + 1 : ℕ) : ℂ)) / 2) = -((m + 1 : ℕ) : ℂ) := by push_cast; ring
  have h2 : (2 * ((m + 1 : ℕ) : ℂ)) / 2 = (m : ℂ) + 1 := by push_cast; ring
  rw [Gammaℝ_def, h1, h2, Complex.Gamma_nat_eq_factorial, norm_mul, cpow_neg, cpow_natCast,
    norm_inv, norm_pow, norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, cfac]
  simp only [Nat.add_sub_cancel]
  rw [div_eq_mul_inv, mul_comm]
  gcongr
  calc Real.pi ^ (m + 1) ≤ Real.pi ^ (2 * (m + 1)) := pow_le_pow_right₀ hπ (by omega)
    _ ≤ (2 * Real.pi) ^ (2 * (m + 1)) := by gcongr; linarith

lemma cfac_le_norm_Gammaℂ {n : ℕ} (hn : 1 ≤ n) : cfac n ≤ ‖Gammaℂ (2 * n)‖ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (2 * ((m + 1 : ℕ) : ℂ)) = ((2 * m + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [Gammaℂ_def, h2, Complex.Gamma_nat_eq_factorial, norm_mul, norm_mul, cpow_neg,
    ← h2, show (2 * ((m + 1 : ℕ) : ℂ)) = ((2 * (m + 1) : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    norm_inv, norm_pow, norm_natCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, cfac]
  simp only [Nat.add_sub_cancel, norm_ofNat]
  have hf : ((m)! : ℝ) ≤ ((2 * m + 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hp : 0 < (2 * Real.pi) ^ (2 * (m + 1)) := by positivity
  rw [div_eq_mul_inv]
  calc (m ! : ℝ) * ((2 * Real.pi) ^ (2 * (m + 1)))⁻¹
      ≤ ((2 * m + 1)! : ℝ) * ((2 * Real.pi) ^ (2 * (m + 1)))⁻¹ := by gcongr
    _ ≤ 2 * ((2 * Real.pi) ^ (2 * (m + 1)))⁻¹ * ((2 * m + 1)! : ℝ) := by
        have : 0 ≤ ((2 * m + 1)! : ℝ) * ((2 * Real.pi) ^ (2 * (m + 1)))⁻¹ := by positivity
        nlinarith

variable (hB : HeckePackage K)

/-- Lower bound: `‖ξ_K(2n)‖ ≥ c_n` whenever `n ≥ 1` and `c_n ≥ 1`. -/
lemma cfac_le_norm_xi {n : ℕ} (hn : 1 ≤ n) (hc : 1 ≤ cfac n) :
    cfac n ≤ ‖hB.simplePoles.ξ (2 * n)‖ := by
  set s : ℂ := 2 * n
  have hs1 : 1 < s.re := by
    simp only [s, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : s ≠ 0 := fun h => by rw [h] at hs1; norm_num at hs1
  have h1 : s ≠ 1 := fun h => by rw [h] at hs1; norm_num at hs1
  rw [hB.simplePoles.eq_xiK s h0 h1, xiK, hB.continuation.eq_of_one_lt_re s hs1,
    dedekindGammaFactor]
  -- the factors
  have hss : 1 ≤ ‖s * (s - 1)‖ := by
    have : s * (s - 1) = (((2 * n * (2 * n - 1) : ℕ) : ℝ) : ℂ) := by
      simp only [s]; push_cast [Nat.cast_sub (show 1 ≤ 2 * n by omega)]; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : 1 ≤ 2 * n * (2 * n - 1) := Nat.one_le_iff_ne_zero.2 (by
      apply Nat.mul_ne_zero <;> omega)
    exact_mod_cast this
  have hd : 1 ≤ ‖((|discr K| : ℤ) : ℂ) ^ (s / 2)‖ := by
    have hsn : s / 2 = (n : ℂ) := by simp only [s]; ring
    rw [hsn, cpow_natCast, norm_pow]
    apply one_le_pow₀
    rw [norm_intCast]
    have : (1 : ℝ) ≤ |((discr K : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
    simpa [Int.cast_abs] using this
  have hζ : 1 ≤ ‖dedekindZeta K s‖ := by
    have := one_le_re_dedekindZeta (K := K) (x := 2 * n) (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    have hcast : ((2 * n : ℝ) : ℂ) = s := by simp [s]
    rw [hcast] at this
    exact this.trans (re_le_norm _)
  have hΓ : cfac n ≤ ‖Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
      Gammaℂ s ^ InfinitePlace.nrComplexPlaces K‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    have hR := cfac_le_norm_Gammaℝ hn
    have hC := cfac_le_norm_Gammaℂ hn
    have h1' := one_le_nrPlaces (K := K)
    have hc0 : 0 ≤ cfac n := by linarith
    calc cfac n ≤ cfac n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K) :=
          le_self_pow₀ hc (by omega)
      _ = cfac n ^ InfinitePlace.nrRealPlaces K * cfac n ^ InfinitePlace.nrComplexPlaces K :=
          pow_add _ _ _
      _ ≤ ‖Gammaℝ s‖ ^ InfinitePlace.nrRealPlaces K * ‖Gammaℂ s‖ ^
            InfinitePlace.nrComplexPlaces K := by
          gcongr
  have hrw : s * (s - 1) * (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^
      InfinitePlace.nrRealPlaces K * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K *
      dedekindZeta K s) = (s * (s - 1)) * ((|discr K| : ℤ) : ℂ) ^ (s / 2) *
      (Gammaℝ s ^ InfinitePlace.nrRealPlaces K * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K) *
      dedekindZeta K s := by ring
  rw [hrw, norm_mul, norm_mul, norm_mul]
  have hc0 : 0 ≤ cfac n := by linarith
  calc cfac n = 1 * 1 * cfac n * 1 := by ring
    _ ≤ _ := by gcongr

/-- Upper bound with finitely many zeros: `‖ξ_K(x)‖ ≤ e^{A + B x}` for real `x ≥ 0`. -/
lemma norm_xi_le_of_finite (hH : HadamardOrderOne) [Finite (ZeroIdx hB)] :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ x → ‖hB.simplePoles.ξ x‖ ≤ Real.exp (A + B * x) := by
  have := Fintype.ofFinite (ZeroIdx hB)
  obtain ⟨-, a, b, g, hg⟩ := xi_hadamard hB hH
  refine ⟨‖a‖, ‖b‖ + 2 * ∑ i, ‖zero hB i‖⁻¹, by positivity, fun x hx => ?_⟩
  have hgx : g x = ∏ i, (1 - (x : ℂ) / zero hB i) * exp ((x : ℂ) / zero hB i) :=
    ((hg x).1.unique (hasProd_fintype _)).symm ▸ rfl
  rw [(hg x).2, hgx, norm_mul, norm_prod]
  have hterm : ∀ i, ‖(1 - (x : ℂ) / zero hB i) * exp ((x : ℂ) / zero hB i)‖ ≤
      Real.exp (2 * (x * ‖zero hB i‖⁻¹)) := by
    intro i
    have hw : ‖(x : ℂ) / zero hB i‖ = x * ‖zero hB i‖⁻¹ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, div_eq_mul_inv]
    rw [norm_mul]
    have h1 : ‖1 - (x : ℂ) / zero hB i‖ ≤ Real.exp (x * ‖zero hB i‖⁻¹) := by
      calc ‖1 - (x : ℂ) / zero hB i‖ ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) / zero hB i‖ := norm_sub_le _ _
        _ = x * ‖zero hB i‖⁻¹ + 1 := by rw [norm_one, hw]; ring
        _ ≤ Real.exp (x * ‖zero hB i‖⁻¹) := Real.add_one_le_exp _
    have h2 : ‖exp ((x : ℂ) / zero hB i)‖ ≤ Real.exp (x * ‖zero hB i‖⁻¹) :=
      hw ▸ norm_exp_le_exp_norm _
    calc ‖1 - (x : ℂ) / zero hB i‖ * ‖exp ((x : ℂ) / zero hB i)‖
        ≤ Real.exp (x * ‖zero hB i‖⁻¹) * Real.exp (x * ‖zero hB i‖⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * (x * ‖zero hB i‖⁻¹)) := by rw [← Real.exp_add]; ring_nf
  have hprod : ∏ i, ‖(1 - (x : ℂ) / zero hB i) * exp ((x : ℂ) / zero hB i)‖ ≤
      Real.exp (∑ i, 2 * (x * ‖zero hB i‖⁻¹)) := by
    rw [Real.exp_sum]
    gcongr with i _
    exact hterm i
  have hexp : ‖exp (a + b * (x : ℂ))‖ ≤ Real.exp (‖a‖ + ‖b‖ * x) := by
    refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    calc ‖a + b * (x : ℂ)‖ ≤ ‖a‖ + ‖b * (x : ℂ)‖ := norm_add_le _ _
      _ = ‖a‖ + ‖b‖ * x := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  calc ‖exp (a + b * (x : ℂ))‖ * ∏ i, ‖(1 - (x : ℂ) / zero hB i) * exp ((x : ℂ) / zero hB i)‖
      ≤ Real.exp (‖a‖ + ‖b‖ * x) * Real.exp (∑ i, 2 * (x * ‖zero hB i‖⁻¹)) :=
        mul_le_mul hexp hprod (by positivity) (Real.exp_pos _).le
    _ = Real.exp (‖a‖ + (‖b‖ + 2 * ∑ i, ‖zero hB i‖⁻¹) * x) := by
        have hs : ∑ i, 2 * (x * ‖zero hB i‖⁻¹) = 2 * (∑ i, ‖zero hB i‖⁻¹) * x := by
          rw [Finset.mul_sum, Finset.sum_mul]; congr 1; ext i; ring
        rw [← Real.exp_add, hs]; congr 1; ring

/-- `(n-1)!` beats `D^n`: for every `D`, eventually `D^n < (n-1)!`. -/
lemma eventually_pow_lt_factorial (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, D ^ n < ((n - 1)! : ℝ) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop D).const_mul D
  rw [mul_zero] at h
  have h' : ∀ᶠ m : ℕ in atTop, D * (D ^ m / m !) < 1 := h.eventually (gt_mem_nhds one_pos)
  rw [Filter.eventually_atTop] at h' ⊢
  obtain ⟨N, hN⟩ := h'
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hN m (by omega)
  have hf : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [Nat.add_sub_cancel, pow_succ, mul_comm (D ^ m)]
  rw [mul_div_assoc', div_lt_one hf] at this
  linarith

/-- **`ξ_K` has infinitely many zeros** (with multiplicity). CONDITIONAL on B1 and B3. -/
theorem zeroIdx_infinite (hH : HadamardOrderOne) : Infinite (ZeroIdx hB) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  obtain ⟨A, B, hB0, hup⟩ := norm_xi_le_of_finite hB hH
  set D : ℝ := (2 * Real.pi) ^ 2 * Real.exp (2 * B) * (Real.exp A + 1)
  have hD : 0 < D := by positivity
  have hD1 : (2 * Real.pi) ^ 2 ≤ D := by
    have h1 : 1 ≤ Real.exp (2 * B) := Real.one_le_exp (by linarith)
    have h2 : 1 ≤ Real.exp A + 1 := by linarith [Real.exp_pos A]
    have h3 : 0 < (2 * Real.pi) ^ 2 := by positivity
    calc (2 * Real.pi) ^ 2 = (2 * Real.pi) ^ 2 * 1 * 1 := by ring
      _ ≤ (2 * Real.pi) ^ 2 * Real.exp (2 * B) * (Real.exp A + 1) := by gcongr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_pow_lt_factorial D)
  set n := max N 1
  have hn1 : 1 ≤ n := le_max_right _ _
  have hlt := hN n (le_max_left _ _)
  have hp : 0 < (2 * Real.pi) ^ (2 * n) := by positivity
  have hpow : (2 * Real.pi) ^ (2 * n) = ((2 * Real.pi) ^ 2) ^ n := by rw [pow_mul]
  -- `c_n ≥ 1`
  have hc : 1 ≤ cfac n := by
    rw [cfac, le_div_iff₀ hp, one_mul, hpow]
    have : ((2 * Real.pi) ^ 2) ^ n ≤ D ^ n := pow_le_pow_left₀ (by positivity) hD1 n
    linarith
  have hlow := cfac_le_norm_xi hB hn1 hc
  have hupn := hup (2 * n) (by positivity)
  have hcast : (((2 * n : ℕ) : ℝ) : ℂ) = 2 * (n : ℂ) := by push_cast; ring
  have hcast' : ((2 * (n : ℝ) : ℝ) : ℂ) = 2 * (n : ℂ) := by push_cast; ring
  rw [hcast'] at hupn
  -- `e^{A + 2Bn} < c_n`
  have hDn : D ^ n = ((2 * Real.pi) ^ 2) ^ n * Real.exp (2 * B) ^ n * (Real.exp A + 1) ^ n := by
    simp only [D]; rw [mul_pow, mul_pow]
  have hkey : Real.exp (A + B * (2 * n)) < cfac n := by
    rw [cfac, lt_div_iff₀ hp, hpow]
    have hEA : Real.exp A < (Real.exp A + 1) ^ n := by
      calc Real.exp A < Real.exp A + 1 := by linarith
        _ ≤ (Real.exp A + 1) ^ n := le_self_pow₀ (by linarith [Real.exp_pos A]) (by omega)
    have hEB : Real.exp (B * (2 * n)) = Real.exp (2 * B) ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [Real.exp_add, hEB]
    calc Real.exp A * Real.exp (2 * B) ^ n * ((2 * Real.pi) ^ 2) ^ n
        < (Real.exp A + 1) ^ n * Real.exp (2 * B) ^ n * ((2 * Real.pi) ^ 2) ^ n := by
          gcongr
      _ = D ^ n := by rw [hDn]; ring
      _ < _ := hlt
  linarith

end WeilRH.Hecke
