/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.R15Mellin

/-!
# `prop:R15` (iii): the tail of the truncated periodization

`latex/notes.tex`, `def:ccm-kernel` and `prop:R15` (iii). For `λ > 0` the truncation is
`k_{0,λ} = k₀ · 1_{(0, λ]}`. For `λ ≥ 1` and every `u > 0`,
`Σ_{n ≥ 1} k₀(nu) − Σ_{n ≥ 1} k_{0,λ}(nu) = Σ_{n > λ/u} k₀(nu) > 0`.

The sums are indexed by `n : ℕ`; the term `n = 0` vanishes because `k₀(0) = 0`
(`R15Tail.k0_zero`), so the `ℕ`-indexed sums are the manuscript's sums over `n ≥ 1`. The series
converge absolutely (`summable_k0`, `summable_k0trunc`).
-/

open Real Filter

namespace WeilRH
namespace R15Tail

open R15Mellin

/-- `def:ccm-kernel`: the truncation `k_{0,λ} = k₀ · 1_{(0,λ]}` (on `u > 0`). -/
noncomputable def k0trunc (lam u : ℝ) : ℝ := if u ≤ lam then k0 u else 0

theorem k0_zero : k0 0 = 0 := by simp [k0]

/-- `k₀(v) > 0` for `v ≥ 1` (indeed for `2πv² > 3`). -/
theorem k0_pos {v : ℝ} (hv : 1 ≤ v) : 0 < k0 v := by
  unfold k0
  have hv0 : 0 < v := by linarith
  have h1 : 1 ≤ v ^ 2 := by nlinarith
  have h2 : 0 < 2 * π * v ^ 2 - 3 := by nlinarith [Real.pi_gt_three]
  have := Real.exp_pos (-(π * v ^ 2))
  have := Real.pi_pos
  positivity

/-- A bound `|k₀(nu)| ≤ C (n⁴ + n²) e^{−πu² n}`, from `e^{−π(nu)²} ≤ e^{−πu² n}`. -/
theorem abs_k0_le {u : ℝ} (n : ℕ) :
    |k0 (n * u)| ≤ (π * π * u ^ 4) * ((n : ℝ) ^ 4 * Real.exp (-(π * u ^ 2) * n)) +
      (3 * π / 2 * u ^ 2) * ((n : ℝ) ^ 2 * Real.exp (-(π * u ^ 2) * n)) := by
  unfold k0
  have hpi := Real.pi_pos
  have hexp : Real.exp (-(π * ((n : ℝ) * u) ^ 2)) ≤ Real.exp (-(π * u ^ 2) * n) := by
    apply Real.exp_le_exp.2
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    have hu2 : 0 ≤ π * u ^ 2 := by positivity
    nlinarith
  have hE : 0 ≤ Real.exp (-(π * ((n : ℝ) * u) ^ 2)) := (Real.exp_pos _).le
  set E := Real.exp (-(π * ((n : ℝ) * u) ^ 2))
  set E' := Real.exp (-(π * u ^ 2) * n)
  have hA : |π / 2 * ((n : ℝ) * u) ^ 2 * (2 * π * ((n : ℝ) * u) ^ 2 - 3) * E| ≤
      π / 2 * ((n : ℝ) * u) ^ 2 * (2 * π * ((n : ℝ) * u) ^ 2 + 3) * E := by
    rw [abs_mul, abs_mul, abs_of_nonneg hE, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ π / 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ) * u) ^ 2)]
    gcongr
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ((n : ℝ) * u)]
  refine hA.trans ?_
  have hB : π / 2 * ((n : ℝ) * u) ^ 2 * (2 * π * ((n : ℝ) * u) ^ 2 + 3) * E ≤
      π / 2 * ((n : ℝ) * u) ^ 2 * (2 * π * ((n : ℝ) * u) ^ 2 + 3) * E' := by
    gcongr
  refine hB.trans (le_of_eq ?_)
  ring

theorem summable_k0 {u : ℝ} (hu : 0 < u) : Summable fun n : ℕ => k0 (n * u) := by
  have hr : 0 < π * u ^ 2 := by positivity
  have h4 := (Real.summable_pow_mul_exp_neg_nat_mul 4 hr).mul_left (π * π * u ^ 4)
  have h2 := (Real.summable_pow_mul_exp_neg_nat_mul 2 hr).mul_left (3 * π / 2 * u ^ 2)
  refine Summable.of_norm_bounded (h4.add h2) (fun n => ?_)
  rw [Real.norm_eq_abs]
  exact abs_k0_le n

theorem summable_k0trunc (lam : ℝ) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => k0trunc lam (n * u) := by
  refine Summable.of_norm_bounded (summable_k0 hu).abs (fun n => ?_)
  rw [Real.norm_eq_abs, k0trunc]
  split_ifs <;> simp

/-- The termwise difference `k₀(v) − k_{0,λ}(v)` is `k₀(v)` when `v > λ` and `0` otherwise. -/
theorem k0_sub_trunc (lam v : ℝ) :
    k0 v - k0trunc lam v = Set.indicator {v : ℝ | lam < v} k0 v := by
  unfold k0trunc
  by_cases h : v ≤ lam
  · rw [if_pos h, Set.indicator_of_notMem (by simpa using h)]; ring
  · rw [if_neg h, Set.indicator_of_mem (by simpa using h)]; ring

/-- **`prop:R15` (iii).** For `λ ≥ 1` and `u > 0`,
`Σ_{n ≥ 1} k₀(nu) − Σ_{n ≥ 1} k_{0,λ}(nu) = Σ_{n > λ/u} k₀(nu) > 0`. -/
theorem tail (lam u : ℝ) (hlam : 1 ≤ lam) (hu : 0 < u) :
    ∑' n : ℕ, k0 (n * u) - ∑' n : ℕ, k0trunc lam (n * u) =
        ∑' n : {n : ℕ // lam / u < n}, k0 ((n : ℕ) * u) ∧
      0 < ∑' n : {n : ℕ // lam / u < n}, k0 ((n : ℕ) * u) := by
  have hiff : ∀ n : ℕ, lam / u < n ↔ lam < (n : ℝ) * u := fun n => by
    rw [div_lt_iff₀ hu]
  have heq : ∑' n : {n : ℕ // lam / u < n}, k0 ((n : ℕ) * u) =
      ∑' n : ℕ, Set.indicator {n : ℕ | lam / u < n} (fun n : ℕ => k0 (n * u)) n :=
    tsum_subtype {n : ℕ | lam / u < n} (fun n : ℕ => k0 (n * u))
  have hsum := summable_k0 hu
  have hind : Summable fun n : ℕ => Set.indicator {n : ℕ | lam / u < n} (fun n : ℕ => k0 (n * u)) n := by
    refine Summable.of_norm_bounded hsum.abs (fun n => ?_)
    by_cases h : n ∈ {n : ℕ | lam / u < n}
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem h]; simp
  constructor
  · rw [heq, ← (summable_k0 hu).tsum_sub (summable_k0trunc lam hu)]
    refine tsum_congr (fun n => ?_)
    rw [k0_sub_trunc]
    by_cases h : lam < (n : ℝ) * u
    · rw [Set.indicator_of_mem (show (n : ℝ) * u ∈ {v : ℝ | lam < v} from h),
        Set.indicator_of_mem (show n ∈ {n : ℕ | lam / u < n} from (hiff n).2 h)]
    · rw [Set.indicator_of_notMem (show (n : ℝ) * u ∉ {v : ℝ | lam < v} from h),
        Set.indicator_of_notMem (show n ∉ {n : ℕ | lam / u < n} from fun h' => h ((hiff n).1 h'))]
  · rw [heq]
    obtain ⟨N, hN⟩ := exists_nat_gt (lam / u)
    refine hind.tsum_pos (fun n => ?_) N ?_
    · by_cases h : n ∈ {n : ℕ | lam / u < n}
      · rw [Set.indicator_of_mem h]
        exact (k0_pos (hlam.trans ((hiff n).1 h).le)).le
      · rw [Set.indicator_of_notMem h]
    · rw [Set.indicator_of_mem (show N ∈ {n : ℕ | lam / u < n} from hN)]
      exact k0_pos (hlam.trans ((hiff N).1 hN).le)

end R15Tail
end WeilRH
