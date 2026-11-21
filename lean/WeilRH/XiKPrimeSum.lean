import Mathlib
import WeilRH.DedekindZetaConv

/-!
# The prime sum of the standard branch of `log ξ_K`

`notes.tex`, `def:deninger-gamma` (e): the standard branch of `log ξ_K` contains the prime sum
`P(z) = ∑_𝔭 ∑_{k ≥ 1} N𝔭^{-kz}/k` over the nonzero prime ideals of `𝓞_K`. For
`prop:xiK-asymp` it is enough that this sum converges absolutely for `Re z ≥ 2` and decays
exponentially in `Re z`:

* `summable_idealNorm_rpow`: `∑_I N I^{-σ} < ∞` for `σ > 1` (fibres of the norm are finite and
  their sizes are the Dedekind coefficients, `DedekindZetaConv.LSeriesSummable_coeff`);
* `primePow_injective`: `(𝔭, k) ↦ 𝔭^{k+1}` is injective on nonzero primes (unique factorization);
* `norm_primeSum_le`: `‖P(z)‖ ≤ 2^{2 - Re z} S_K` for `Re z ≥ 2`, with `S_K = ∑_{𝔭,k} N(𝔭^{k+1})^{-2}`.
-/

namespace WeilRH.XiKPrimeSum

open NumberField Ideal Filter Asymptotics
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- Nonzero prime ideals of `𝓞_K`. -/
def Primes : Type := {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}

/-- The prime sum `P(z) = ∑_𝔭 ∑_{k ≥ 1} N𝔭^{-kz}/k`, indexed by `(𝔭, k - 1)`. -/
noncomputable def primeSum (z : ℂ) : ℂ :=
  ∑' q : Primes K × ℕ, (1 / ((q.2 : ℂ) + 1)) * ((absNorm q.1.1 : ℕ) : ℂ) ^ (-(((q.2 : ℂ) + 1) * z))

/-- `∑_I N I^{-σ} < ∞` for `σ > 1` (the zero ideal contributes `0^{-σ} = 0`). -/
theorem summable_idealNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) => ((absNorm I : ℕ) : ℝ) ^ (-σ)) := by
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => absNorm I)).summable_iff]
  have hnn : ∀ x : (n : ℕ) × {I : Ideal (𝓞 K) // absNorm I = n},
      0 ≤ ((absNorm ((Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => absNorm I)) x) : ℕ) : ℝ) ^ (-σ) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Function.comp_def, summable_sigma_of_nonneg hnn]
  haveI hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // absNorm I = n} := fun n =>
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine ⟨fun n => (Summable.of_finite), ?_⟩
  have key : ∀ n : ℕ, ∑' y : {I : Ideal (𝓞 K) // absNorm I = n},
      ((absNorm ((Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => absNorm I)) ⟨n, y⟩) : ℕ) : ℝ) ^ (-σ)
        = DedekindZetaConv.coeff K n * (n : ℝ) ^ (-σ) := by
    intro n
    have : ∀ y : {I : Ideal (𝓞 K) // absNorm I = n},
        ((absNorm ((Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => absNorm I)) ⟨n, y⟩) : ℕ) : ℝ)
          ^ (-σ) = (n : ℝ) ^ (-σ) := fun y => by
      simp [Equiv.sigmaFiberEquiv, y.2]
    simp_rw [this, tsum_const, DedekindZetaConv.coeff, nsmul_eq_mul]
  simp_rw [key]
  have hs := (DedekindZetaConv.LSeriesSummable_coeff K (s := (σ : ℂ)) (by simpa using hσ)).norm
  refine hs.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : (-σ) ≠ 0)]
  · rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.norm_real, Real.norm_of_nonneg
      (DedekindZetaConv.coeff_nonneg K n), Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _),
      div_eq_mul_inv]

/-- `(𝔭, k) ↦ 𝔭^{k+1}` is injective on nonzero prime ideals. -/
theorem primePow_injective :
    Function.Injective (fun q : Primes K × ℕ => q.1.1 ^ (q.2 + 1)) := by
  rintro ⟨⟨P, hP, hP0⟩, k⟩ ⟨⟨Q, hQ, hQ0⟩, j⟩ h
  simp only at h
  have hPi : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hQi : Irreducible Q := (Ideal.prime_of_isPrime hQ0 hQ).irreducible
  have hf := congrArg UniqueFactorizationMonoid.normalizedFactors h
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hPi,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hQi, normalize_eq, normalize_eq] at hf
  have hPQ : P = Q := by
    have hmem : P ∈ (j + 1) • ({Q} : Multiset (Ideal (𝓞 K))) := by
      rw [← hf]; exact Multiset.mem_nsmul.mpr ⟨Nat.succ_ne_zero k, Multiset.mem_singleton_self P⟩
    exact Multiset.mem_singleton.mp (Multiset.mem_of_mem_nsmul hmem)
  subst hPQ
  have hc := congrArg Multiset.card hf
  simp only [Multiset.card_nsmul, Multiset.card_singleton, mul_one, add_left_inj] at hc
  subst hc
  rfl

/-- A nonzero prime ideal has norm at least `2`. -/
theorem two_le_absNorm (𝔭 : Primes K) : 2 ≤ absNorm 𝔭.1 := by
  obtain ⟨P, hP, hP0⟩ := 𝔭
  have h0 : absNorm P ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  have h1 : absNorm P ≠ 1 := by rw [Ne, absNorm_eq_one_iff]; exact hP.ne_top
  change 2 ≤ absNorm P
  omega

/-- The constant `S_K = ∑_{𝔭,k} N(𝔭^{k+1})^{-2}`. -/
noncomputable def S : ℝ := ∑' q : Primes K × ℕ, ((absNorm (q.1.1 ^ (q.2 + 1)) : ℕ) : ℝ) ^ (-(2 : ℝ))

theorem summable_primePow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun q : Primes K × ℕ => ((absNorm (q.1.1 ^ (q.2 + 1)) : ℕ) : ℝ) ^ (-σ)) :=
  (summable_idealNorm_rpow K hσ).comp_injective (primePow_injective K)

/-- The norm of a term of the prime sum. -/
theorem norm_term_le (q : Primes K × ℕ) {z : ℂ} (hz : 2 ≤ z.re) :
    ‖(1 / ((q.2 : ℂ) + 1)) * ((absNorm q.1.1 : ℕ) : ℂ) ^ (-(((q.2 : ℂ) + 1) * z))‖ ≤
      (2 : ℝ) ^ (2 - z.re) * ((absNorm (q.1.1 ^ (q.2 + 1)) : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hN2 := two_le_absNorm K q.1
  set N : ℕ := absNorm q.1.1 with hNdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set k : ℝ := (q.2 : ℝ) + 1 with hk
  have hk1 : 1 ≤ k := by simp [hk]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  have hre : (-(((q.2 : ℂ) + 1) * z)).re = -(k * z.re) := by
    simp [hk, Complex.mul_re]
  rw [hre, map_pow, Nat.cast_pow]
  have h1 : ‖(1 : ℂ) / ((q.2 : ℂ) + 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have : (1 : ℝ) ≤ ‖((q.2 : ℂ) + 1)‖ := by
      have : ((q.2 : ℂ) + 1) = ((k : ℝ) : ℂ) := by simp [hk]
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact hk1
    exact div_le_one_of_le₀ this (by positivity)
  -- `N^{-kσ} = (N^k)^{-2} · N^{-k(σ-2)} ≤ (N^k)^{-2} 2^{-(σ-2)}`
  have hNk : ((N : ℝ) ^ (q.2 + 1)) ^ (-(2 : ℝ)) = (N : ℝ) ^ (-(2 * k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; simp [hk]; ring
  rw [hNk]
  have hsplit : (N : ℝ) ^ (-(k * z.re)) = (N : ℝ) ^ (-(2 * k)) * (N : ℝ) ^ (-(k * (z.re - 2))) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hle : (N : ℝ) ^ (-(k * (z.re - 2))) ≤ (2 : ℝ) ^ (2 - z.re) := by
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    calc (N : ℝ) ^ (-(k * (z.re - 2))) ≤ (N : ℝ) ^ (-(z.re - 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          nlinarith
      _ ≤ (2 : ℝ) ^ (-(z.re - 2)) := by
          apply Real.rpow_le_rpow_of_nonpos (by norm_num) h2N (by linarith)
      _ = (2 : ℝ) ^ (2 - z.re) := by ring_nf
  calc ‖(1 : ℂ) / ((q.2 : ℂ) + 1)‖ * (N : ℝ) ^ (-(k * z.re))
      ≤ 1 * ((N : ℝ) ^ (-(2 * k)) * (2 : ℝ) ^ (2 - z.re)) := by
        rw [hsplit]
        apply mul_le_mul h1 (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
          zero_le_one
    _ = (2 : ℝ) ^ (2 - z.re) * (N : ℝ) ^ (-(2 * k)) := by ring

/-- **The prime sum converges absolutely and is `≤ 2^{2 - Re z} S_K` for `Re z ≥ 2`.** -/
theorem norm_primeSum_le {z : ℂ} (hz : 2 ≤ z.re) :
    ‖primeSum K z‖ ≤ (2 : ℝ) ^ (2 - z.re) * S K := by
  have hsum := (summable_primePow K (σ := 2) (by norm_num)).mul_left ((2 : ℝ) ^ (2 - z.re))
  have hnorm : Summable (fun q : Primes K × ℕ =>
      ‖(1 / ((q.2 : ℂ) + 1)) * ((absNorm q.1.1 : ℕ) : ℂ) ^ (-(((q.2 : ℂ) + 1) * z))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_term_le K q hz) hsum
  calc ‖primeSum K z‖ ≤ ∑' q : Primes K × ℕ,
        ‖(1 / ((q.2 : ℂ) + 1)) * ((absNorm q.1.1 : ℕ) : ℂ) ^ (-(((q.2 : ℂ) + 1) * z))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : Primes K × ℕ, (2 : ℝ) ^ (2 - z.re) *
          ((absNorm (q.1.1 ^ (q.2 + 1)) : ℕ) : ℝ) ^ (-(2 : ℝ)) :=
        hnorm.tsum_le_tsum (fun q => norm_term_le K q hz) hsum
    _ = (2 : ℝ) ^ (2 - z.re) * S K := by rw [tsum_mul_left]; rfl

end WeilRH.XiKPrimeSum
