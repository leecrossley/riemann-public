/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Phantom Frobenius eigenvalues (`prop:ff-phantom`)

Source: `latex/notes.tex`, Definition `def:window-objects`(b),(c) and Proposition
`prop:ff-phantom`.

For `q > 1` and an integer `N ≥ 2` the phantom set is
`S_N = {√q · e^{iπ(2m+1)/N} : 0 ≤ m < N}` and the half-shifted coset is
`C_L = {1/2 + (2πi/L)(n + 1/2) : n ∈ ℤ}`. We encode `S_N` as the image `phantomSet q N` of
`m ↦ phantom q N m` on `Finset.range N` (the map is injective there, `phantom_injOn`), `C_L` as
`halfCoset L`, and the progression `Σ_q(α) = {ρ : q^ρ = α}` as `{ρ | exp(ρ log q) = α}`; the
spectrum of the logarithmic suspension of `(ℂ^{S_N}, diag(S_N))` is by Definition `def:log-susp`
the union of the `Σ_q(α)`, `α ∈ S_N` (the suspension itself is not built here).

## Main results (`prop:ff-phantom`)

* (i) `sum_phantomSet_pow_eq_zero`: `∑_{α ∈ S_N} α^k = 0` for `1 ≤ k < N`;
  `sum_phantomSet_pow_self`: `∑_{α ∈ S_N} α^N = -N q^{N/2}`;
  `norm_of_mem_phantomSet`: `|α| = √q`; `div_mem_phantomSet`, `div_eq_conj_of_mem_phantomSet`:
  `S_N` is stable under `α ↦ q/α`, and `q/α = ᾱ`.
* (ii) `spectrum_suspension_phantom`: `⋃_{α ∈ S_N} Σ_q(α) = C_{N log q}`.
-/

open Complex Finset Real
open scoped ComplexConjugate

namespace WeilRH

/-- The phantom eigenvalue `√q · e^{iπ(2m+1)/N}`. -/
noncomputable def phantom (q : ℝ) (N m : ℕ) : ℂ :=
  (Real.sqrt q : ℂ) * exp (π * I * (2 * m + 1) / N)

/-- The phantom set `S_N` (`def:window-objects`(c)). -/
noncomputable def phantomSet (q : ℝ) (N : ℕ) : Finset ℂ := (range N).image (phantom q N)

/-- The half-shifted coset `C_L` (`def:window-objects`(b)). -/
def halfCoset (L : ℝ) : Set ℂ :=
  {ρ | ∃ n : ℤ, ρ = 1 / 2 + 2 * π * I / L * (n + 1 / 2)}

/-- The progression `Σ_q(α) = {ρ ∈ ℂ : q^ρ = α}`. -/
def progression (q : ℝ) (α : ℂ) : Set ℂ := {ρ | exp (ρ * Real.log q) = α}

lemma phantom_eq_exp {q : ℝ} (hq : 0 < q) (N m : ℕ) :
    phantom q N m = exp (Real.log q / 2 + π * I * (2 * m + 1) / N) := by
  rw [phantom, Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, Complex.ofReal_exp]
  push_cast
  ring_nf

lemma phantom_pow (q : ℝ) (N m k : ℕ) :
    phantom q N m ^ k =
      ((Real.sqrt q : ℂ) ^ k * exp (π * I * k / N)) * (exp (2 * π * I / N) ^ k) ^ m := by
  rw [phantom, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    mul_assoc ((Real.sqrt q : ℂ) ^ k), ← Complex.exp_add]
  congr 2
  ring

lemma isPrimitiveRoot_phantom {N : ℕ} (hN : N ≠ 0) :
    IsPrimitiveRoot (exp (2 * π * I / N)) N := Complex.isPrimitiveRoot_exp N hN

/-- `m ↦ phantom q N m` is injective on `{0, …, N-1}` (for `q > 0`). -/
lemma phantom_injOn {q : ℝ} (hq : 0 < q) (N : ℕ) : Set.InjOn (phantom q N) (range N) := by
  intro m hm m' hm' h
  simp only [coe_range, Set.mem_Iio] at hm hm'
  have hN : N ≠ 0 := by omega
  have hs : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hζ := isPrimitiveRoot_phantom hN
  have e : ∀ n : ℕ, phantom q N n = (Real.sqrt q : ℂ) * exp (π * I / N) *
      exp (2 * π * I / N) ^ n := by
    intro n
    rw [phantom, mul_assoc (Real.sqrt q : ℂ), ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    ring
  rw [e, e] at h
  have h' := mul_left_cancel₀ (mul_ne_zero hs (Complex.exp_ne_zero _)) h
  exact hζ.pow_inj hm hm' h'

lemma sum_phantomSet (q : ℝ) (hq : 0 < q) (N : ℕ) (f : ℂ → ℂ) :
    ∑ α ∈ phantomSet q N, f α = ∑ m ∈ range N, f (phantom q N m) :=
  sum_image (phantom_injOn hq N)

/-- **`prop:ff-phantom`(i), vanishing power sums.** `∑_{α ∈ S_N} α^k = 0` for `1 ≤ k < N`. -/
theorem sum_phantomSet_pow_eq_zero {q : ℝ} (hq : 0 < q) {N k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ∑ α ∈ phantomSet q N, α ^ k = 0 := by
  rw [sum_phantomSet q hq N (· ^ k), sum_congr rfl (fun m _ => phantom_pow q N m k), ← mul_sum]
  have hζ := isPrimitiveRoot_phantom (N := N) (by omega)
  have hne : exp (2 * π * I / N) ^ k ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) hkN
  have hpow : (exp (2 * π * I / N) ^ k) ^ N = 1 := by
    rw [← pow_mul, mul_comm k N, pow_mul, hζ.pow_eq_one, one_pow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div, mul_zero]

/-- **`prop:ff-phantom`(i), the `N`-th power sum.** `∑_{α ∈ S_N} α^N = -N q^{N/2}`. -/
theorem sum_phantomSet_pow_self {q : ℝ} (hq : 0 < q) {N : ℕ} (hN : 2 ≤ N) :
    ∑ α ∈ phantomSet q N, α ^ N = -(N : ℂ) * ((q ^ ((N : ℝ) / 2) : ℝ) : ℂ) := by
  rw [sum_phantomSet q hq N (· ^ N), sum_congr rfl (fun m _ => phantom_pow q N m N), ← mul_sum]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hζ := isPrimitiveRoot_phantom (N := N) (by omega)
  rw [hζ.pow_eq_one]
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  have e1 : exp (π * I * N / N) = -1 := by
    rw [mul_div_assoc, div_self hN0, mul_one, Complex.exp_pi_mul_I]
  have e2 : (Real.sqrt q : ℂ) ^ N = ((q ^ ((N : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 2
    ring
  rw [e1, e2]
  ring

/-- **`prop:ff-phantom`(i), modulus.** Every `α ∈ S_N` has `|α| = √q`. -/
theorem norm_of_mem_phantomSet {q : ℝ} {N : ℕ} {α : ℂ} (hα : α ∈ phantomSet q N) :
    ‖α‖ = Real.sqrt q := by
  obtain ⟨m, -, rfl⟩ := mem_image.1 hα
  rw [phantom, norm_mul, Complex.norm_exp]
  have : (π * I * (2 * m + 1) / N : ℂ).re = 0 := by
    rw [show (π * I * (2 * m + 1) / N : ℂ) = ((π * (2 * m + 1) / N : ℝ) : ℂ) * I by
      push_cast; ring]
    simp
  rw [this, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg q)]

/-- **`prop:ff-phantom`(i), `q/α = ᾱ`.** -/
theorem div_eq_conj_of_mem_phantomSet {q : ℝ} (hq : 0 < q) {N : ℕ} {α : ℂ}
    (hα : α ∈ phantomSet q N) : (q : ℂ) / α = conj α := by
  have hn := norm_of_mem_phantomSet hα
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact (Real.sqrt_pos.2 hq).ne' hn.symm
  rw [div_eq_iff hα0, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn,
    Real.sq_sqrt hq.le]

/-- **`prop:ff-phantom`(i), symmetry.** `S_N` is stable under `α ↦ q/α`: explicitly
`q / (√q e^{iπ(2m+1)/N}) = √q e^{iπ(2(N-1-m)+1)/N}`. -/
theorem div_mem_phantomSet {q : ℝ} (hq : 0 < q) {N : ℕ} {α : ℂ} (hα : α ∈ phantomSet q N) :
    (q : ℂ) / α ∈ phantomSet q N := by
  rw [div_eq_conj_of_mem_phantomSet hq hα]
  obtain ⟨m, hm, rfl⟩ := mem_image.1 hα
  rw [mem_range] at hm
  refine mem_image.2 ⟨N - 1 - m, mem_range.2 (by omega), ?_⟩
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [phantom, phantom, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  have hcast : ((N - 1 - m : ℕ) : ℂ) = (N : ℂ) - 1 - m := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  have hc : conj (π * I * (2 * m + 1) / N : ℂ) = -(π * I * (2 * m + 1) / N) := by
    simp [map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [hc, show π * I * (2 * ((N : ℂ) - 1 - m) + 1) / N =
      -(π * I * (2 * m + 1) / N) + (2 * π * I) by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **`prop:ff-phantom`(ii).** The union over `α ∈ S_N` of the progressions
`Σ_q(α) = {ρ : q^ρ = α}` — the spectrum of the logarithmic suspension of
`(ℂ^{S_N}, diag(S_N))` — is the half-shifted coset `C_{N log q}`. -/
theorem spectrum_suspension_phantom {q : ℝ} (hq : 1 < q) {N : ℕ} (hN : 2 ≤ N) :
    {ρ | ∃ α ∈ phantomSet q N, ρ ∈ progression q α} = halfCoset (N * Real.log q) := by
  have hq0 : 0 < q := by linarith
  have hL : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  ext ρ
  simp only [Set.mem_ofPred_eq, progression, halfCoset, phantomSet, mem_image, mem_range]
  constructor
  · rintro ⟨α, ⟨m, hm, rfl⟩, hρ⟩
    rw [phantom_eq_exp hq0, Complex.exp_eq_exp_iff_exists_int] at hρ
    obtain ⟨n, hn⟩ := hρ
    refine ⟨m + n * N, ?_⟩
    push_cast
    field_simp
    have : ρ = (Real.log q / 2 + π * I * (2 * m + 1) / N + n * (2 * π * I)) / Real.log q := by
      rw [← hn]; field_simp
    rw [this]
    field_simp
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨phantom q N (Int.toNat (n % N)), ⟨_, ?_, rfl⟩, ?_⟩
    · have := Int.emod_lt_of_pos n (by omega : (0 : ℤ) < N)
      have := Int.emod_nonneg n hNz
      omega
    rw [phantom_eq_exp hq0, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n / N, ?_⟩
    have hdiv := Int.emod_add_mul_ediv n N
    have hnn : ((Int.toNat (n % N) : ℕ) : ℂ) = ((n % N : ℤ) : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n hNz)]
    rw [hnn]
    have hcast : (n : ℂ) = ((n % N : ℤ) : ℂ) + (N : ℂ) * ((n / N : ℤ) : ℂ) := by
      have h := congrArg (fun z : ℤ => (z : ℂ)) hdiv
      push_cast at h
      linear_combination -h
    rw [hcast]
    field_simp
    push_cast
    ring

end WeilRH
