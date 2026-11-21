/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.MultiplicativeForm

/-!
# Zeros on two lines for `X = E × ℙ¹` (`prop:N-lines`)

Source: `latex/notes.tex`, `prop:N-lines`, `def:hasse-weil-zeta`, `def:suspension`,
`eq:elliptic-zeta`.

`q^s` is `qpow q s = exp(s log q)` and `Σ_q(α)` is `WeilRH.progression q α`. The zeta function of
a variety with point counts `c_n = #X(𝔽_{qⁿ})` is `zetaOfCounts q c s = exp(Σ_n c_n q^{-ns}/n)`,
i.e. `Z(X, t) = exp(Σ c_n tⁿ/n)` evaluated at `t = q^{-s}`. The point counts are inputs: for `E`
they are `qⁿ + 1 - αⁿ - βⁿ` (`eq:elliptic-zeta`, the elliptic case of `thm:imp-deligne`), and for
`X = E × ℙ¹` they are `#E(𝔽_{qⁿ}) + qⁿ #E(𝔽_{qⁿ})` (proof of (i)).

## Main results

* `zetaOfCounts_product` (**(i)**): `ζ_X(s) = ζ_E(s) ζ_E(s-1)`, i.e. `Z(X,t) = Z(E,t) Z(E,qt)`.
* `zetaOfCounts_elliptic`: `ζ_E(s) = (1-αt)(1-βt)/((1-t)(1-qt))` for `Re s > 1`.
* `zetaOfCounts_eq_zetaX`: `ζ_X = num/den` (`zetaX`) on `Re s > 2`.
* `zeros_zetaX` (**(ii)**): the zeros of `zetaX` are `Σ_q(α) ∪ Σ_q(β) ∪ (1+Σ_q(α)) ∪ (1+Σ_q(β))`,
  all on `Re s = 1/2` or `Re s = 3/2`, with infinitely many on each line.
* `poles_zetaX` (**(iii)**): `zetaX` is holomorphic off `Re s ∈ {0, 1, 2}`, and the numerator is
  nonzero wherever the denominator vanishes.
-/

open Complex

namespace WeilRH.NLines

/-- `q^s = exp(s log q)` with `log q` real (`def:suspension`). -/
noncomputable def qpow (q : ℝ) (s : ℂ) : ℂ := exp (s * Real.log q)

lemma qpow_ne_zero (q : ℝ) (s : ℂ) : qpow q s ≠ 0 := exp_ne_zero _

lemma qpow_neg (q : ℝ) (s : ℂ) : qpow q (-s) = (qpow q s)⁻¹ := by
  rw [qpow, qpow, neg_mul, exp_neg]

/-- `1 - α q^{-s} = 0` iff `s ∈ Σ_q(α)`. -/
lemma one_sub_mul_qpow_neg_eq_zero_iff (q : ℝ) (α s : ℂ) :
    1 - α * qpow q (-s) = 0 ↔ s ∈ progression q α := by
  simp only [progression, Set.mem_ofPred_eq, qpow_neg]
  rw [sub_eq_zero, eq_comm, ← div_eq_mul_inv, div_eq_one_iff_eq (qpow_ne_zero q s), eq_comm]
  rfl

/-- The numerator `(1-αq^{-s})(1-βq^{-s})(1-αq^{1-s})(1-βq^{1-s})` of `ζ_X`. -/
noncomputable def num (q : ℝ) (α β s : ℂ) : ℂ :=
  (1 - α * qpow q (-s)) * (1 - β * qpow q (-s)) * (1 - α * qpow q (-(s - 1))) *
    (1 - β * qpow q (-(s - 1)))

/-- The denominator `(1-q^{-s})(1-q^{1-s})(1-q^{1-s})(1-q^{2-s})` of `ζ_X`. -/
noncomputable def den (q : ℝ) (s : ℂ) : ℂ :=
  (1 - qpow q (-s)) * (1 - qpow q (-(s - 1))) * (1 - qpow q (-(s - 1))) *
    (1 - qpow q (-(s - 2)))

/-- The rational expression for `ζ_X(s)`, `X = E × ℙ¹` (proof of `prop:N-lines`). -/
noncomputable def zetaX (q : ℝ) (α β s : ℂ) : ℂ := num q α β s / den q s

/-- The shifted progression `1 + Σ_q(α)`. -/
def shift1 (A : Set ℂ) : Set ℂ := {s | s - 1 ∈ A}

theorem num_eq_zero_iff (q : ℝ) (α β s : ℂ) :
    num q α β s = 0 ↔ s ∈ progression q α ∪ progression q β ∪
      shift1 (progression q α) ∪ shift1 (progression q β) := by
  simp only [num, mul_eq_zero, one_sub_mul_qpow_neg_eq_zero_iff, shift1, Set.mem_union,
    Set.mem_ofPred_eq]

lemma mem_progression_one (q : ℝ) (hq : 1 < q) (n : ℕ) (s : ℂ) :
    s ∈ progression q ((q : ℂ) ^ n) → s.re = n := by
  intro hs
  have hn : ‖((q : ℂ) ^ n)‖ = q ^ ((2 * n : ℝ) / 2) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      show (2 * n : ℝ) / 2 = n by ring, Real.rpow_natCast]
  have := re_of_mem_progression hq hs hn
  linarith

lemma qpow_neg_sub_natCast {q : ℝ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    qpow q (-(s - n)) = (q : ℂ) ^ n * qpow q (-s) := by
  rw [qpow, qpow, show -(s - n) * (Real.log q : ℂ) = n * Real.log q + -s * Real.log q by ring,
    exp_add, exp_nat_mul, ← ofReal_exp, Real.exp_log hq]

lemma one_sub_qpow_eq_zero_iff {q : ℝ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    1 - qpow q (-(s - n)) = 0 ↔ s ∈ progression q ((q : ℂ) ^ n) := by
  rw [qpow_neg_sub_natCast hq, one_sub_mul_qpow_neg_eq_zero_iff]

/-- The denominator vanishes exactly where `q^s ∈ {1, q, q²}`. -/
theorem den_eq_zero_iff {q : ℝ} (hq : 0 < q) (s : ℂ) :
    den q s = 0 ↔ s ∈ progression q 1 ∪ progression q q ∪ progression q ((q : ℂ) ^ 2) := by
  have h0 := one_sub_qpow_eq_zero_iff hq s 0
  have h1 := one_sub_qpow_eq_zero_iff hq s 1
  have h2 := one_sub_qpow_eq_zero_iff hq s 2
  simp only [Nat.cast_zero, sub_zero, pow_zero, Nat.cast_one, pow_one, Nat.cast_ofNat] at h0 h1 h2
  simp only [den, mul_eq_zero, h0, h1, h2, Set.mem_union]
  tauto

/-- **`prop:N-lines` (iii), location.** The denominator vanishes only on `Re s ∈ {0, 1, 2}`. -/
theorem re_of_den_eq_zero {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : den q s = 0) :
    s.re = 0 ∨ s.re = 1 ∨ s.re = 2 := by
  rw [den_eq_zero_iff (by linarith)] at hs
  rcases hs with (hs | hs) | hs
  · left; have := mem_progression_one q hq 0 s (by simpa using hs); simpa using this
  · right; left; have := mem_progression_one q hq 1 s (by simpa using hs); simpa using this
  · right; right; have := mem_progression_one q hq 2 s (by simpa using hs); simpa using this

/-- Zeros of the numerator lie on `Re s = 1/2` or `Re s = 3/2` when `|α| = |β| = q^{1/2}`. -/
theorem re_of_num_eq_zero {q : ℝ} (hq : 1 < q) {α β : ℂ} (hα : ‖α‖ = q ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ} (hs : num q α β s = 0) :
    s.re = 1 / 2 ∨ s.re = 3 / 2 := by
  rw [num_eq_zero_iff] at hs
  rcases hs with ((hs | hs) | hs) | hs
  · exact Or.inl (re_of_mem_progression hq hs hα)
  · exact Or.inl (re_of_mem_progression hq hs hβ)
  · right; have := re_of_mem_progression hq hs hα; simp at this; linarith
  · right; have := re_of_mem_progression hq hs hβ; simp at this; linarith

/-- Numerator and denominator have no common zero. -/
theorem den_ne_zero_of_num_eq_zero {q : ℝ} (hq : 1 < q) {α β : ℂ}
    (hα : ‖α‖ = q ^ ((1 : ℝ) / 2)) (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ}
    (hs : num q α β s = 0) : den q s ≠ 0 := by
  intro hd
  rcases re_of_num_eq_zero hq hα hβ hs with h | h <;>
    rcases re_of_den_eq_zero hq hd with h' | h' | h' <;> (rw [h] at h'; norm_num at h')

/-- `Σ_q(α)` is infinite (an arithmetic progression `ρ_k(α)`, `k ∈ ℤ`). -/
theorem progression_infinite {q : ℝ} (hq : 1 < q) {α : ℂ} (hα : α ≠ 0) :
    (progression q α).Infinite := by
  have hL : (Real.log q : ℂ) ≠ 0 := log_ne_zero_of_one_lt hq
  have hinj : Function.Injective fun k : ℤ => suspEigen q k α := by
    intro k k' hkk'
    simp only [suspEigen] at hkk'
    rw [div_left_inj' hL, add_right_inj] at hkk'
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact_mod_cast mul_left_cancel₀ hpi hkk'
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  show exp (suspEigen q k α * Real.log q) = α
  rw [mul_comm]; exact exp_suspEigen hq k hα

lemma shift1_infinite {A : Set ℂ} (hA : A.Infinite) : (shift1 A).Infinite := by
  have : shift1 A = (· + 1) '' A := by
    ext s; simp only [shift1, Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun h => ⟨s - 1, h, by ring⟩, fun ⟨t, ht, hts⟩ => by rw [← hts]; simpa using ht⟩
  rw [this]; exact hA.image (add_left_injective 1).injOn

/-- **`prop:N-lines` (ii).** For `|α| = |β| = q^{1/2}`: the zeros of `ζ_X = num/den` (at points
where `den ≠ 0`) form `Σ_q(α) ∪ Σ_q(β) ∪ (1+Σ_q(α)) ∪ (1+Σ_q(β))`; every zero lies on
`Re s = 1/2` or `Re s = 3/2`; and each line contains infinitely many zeros. -/
theorem zeros_zetaX {q : ℝ} (hq : 1 < q) {α β : ℂ} (hα : ‖α‖ = q ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) :
    {s | den q s ≠ 0 ∧ zetaX q α β s = 0} = progression q α ∪ progression q β ∪
        shift1 (progression q α) ∪ shift1 (progression q β) ∧
      (∀ s, den q s ≠ 0 → zetaX q α β s = 0 → s.re = 1 / 2 ∨ s.re = 3 / 2) ∧
      {s | den q s ≠ 0 ∧ zetaX q α β s = 0 ∧ s.re = 1 / 2}.Infinite ∧
      {s | den q s ≠ 0 ∧ zetaX q α β s = 0 ∧ s.re = 3 / 2}.Infinite := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hα0 : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hα; exact (Real.rpow_pos_of_pos hq0 _).ne' hα.symm
  have hzero : ∀ s, den q s ≠ 0 ∧ zetaX q α β s = 0 ↔ num q α β s = 0 := by
    intro s
    refine ⟨fun ⟨hd, hz⟩ => (div_eq_zero_iff.1 hz).resolve_right hd, fun hn =>
      ⟨den_ne_zero_of_num_eq_zero hq hα hβ hn, by rw [zetaX, hn, zero_div]⟩⟩
  refine ⟨?_, fun s hd hz => re_of_num_eq_zero hq hα hβ ((hzero s).1 ⟨hd, hz⟩), ?_, ?_⟩
  · ext s; rw [Set.mem_ofPred_eq, hzero, num_eq_zero_iff]
  · refine (progression_infinite hq hα0).mono fun s hs => ?_
    have hn : num q α β s = 0 := (num_eq_zero_iff q α β s).2 (Or.inl (Or.inl (Or.inl hs)))
    exact ⟨((hzero s).2 hn).1, ((hzero s).2 hn).2, re_of_mem_progression hq hs hα⟩
  · refine (shift1_infinite (progression_infinite hq hα0)).mono fun s hs => ?_
    have hn : num q α β s = 0 := (num_eq_zero_iff q α β s).2 (Or.inl (Or.inr hs))
    have := re_of_mem_progression hq hs hα
    simp at this
    exact ⟨((hzero s).2 hn).1, ((hzero s).2 hn).2, by linarith⟩

lemma differentiable_qpow (q : ℝ) : Differentiable ℂ (qpow q) := fun _ =>
  ((differentiableAt_id.mul_const _).cexp)

/-- **`prop:N-lines` (iii).** `ζ_X` is holomorphic off the lines `Re s ∈ {0, 1, 2}`; on them the
numerator does not vanish where the denominator does, so its poles are exactly the zeros of the
denominator, all on these lines. -/
theorem poles_zetaX {q : ℝ} (hq : 1 < q) {α β : ℂ} (hα : ‖α‖ = q ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) :
    (∀ s : ℂ, s.re ≠ 0 → s.re ≠ 1 → s.re ≠ 2 → DifferentiableAt ℂ (zetaX q α β) s) ∧
      ∀ s, den q s = 0 → num q α β s ≠ 0 ∧ (s.re = 0 ∨ s.re = 1 ∨ s.re = 2) := by
  refine ⟨fun s h0 h1 h2 => ?_, fun s hd => ⟨fun hn => den_ne_zero_of_num_eq_zero hq hα hβ hn hd,
    re_of_den_eq_zero hq hd⟩⟩
  have hd : den q s ≠ 0 := fun hd => by
    rcases re_of_den_eq_zero hq hd with h | h | h <;> contradiction
  have hQ := differentiable_qpow q
  have hnum : Differentiable ℂ (num q α β) := by
    unfold num; fun_prop
  have hden : Differentiable ℂ (den q) := by
    unfold den; fun_prop
  exact (hnum s).div (hden s) hd

/-! ### The zeta function from point counts (`def:hasse-weil-zeta`) -/

/-- `ζ(s) = Z(q^{-s})` for `Z(t) = exp(Σ_{n ≥ 1} c_n t^n / n)` (`def:hasse-weil-zeta`(a)), with the
series evaluated at `t = q^{-s}` (the `n = 0` term is `c_0 · 1/0 = 0`). -/
noncomputable def zetaOfCounts (q : ℝ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  exp (∑' n : ℕ, c n * qpow q (-s) ^ n / n)

lemma qpow_neg_sub_one_pow {q : ℝ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    qpow q (-(s - 1)) ^ n = (q : ℂ) ^ n * qpow q (-s) ^ n := by
  have := qpow_neg_sub_natCast hq s 1
  simp only [Nat.cast_one, pow_one] at this
  rw [this, mul_pow]

/-- **`prop:N-lines` (i)**, `Z(X, t) = Z(E, t) Z(E, qt)` at `t = q^{-s}`: if
`#X(𝔽_{qⁿ}) = #E(𝔽_{qⁿ}) + qⁿ #E(𝔽_{qⁿ})` and the series for `E` converge at `s` and `s - 1`,
then `ζ_X(s) = ζ_E(s) ζ_E(s - 1)`. -/
theorem zetaOfCounts_product {q : ℝ} (hq : 0 < q) (cE cX : ℕ → ℂ)
    (hX : ∀ n, cX n = cE n + (q : ℂ) ^ n * cE n) {s : ℂ}
    (h1 : Summable fun n : ℕ => cE n * qpow q (-s) ^ n / n)
    (h2 : Summable fun n : ℕ => cE n * qpow q (-(s - 1)) ^ n / n) :
    zetaOfCounts q cX s = zetaOfCounts q cE s * zetaOfCounts q cE (s - 1) := by
  rw [zetaOfCounts, zetaOfCounts, zetaOfCounts, ← exp_add, ← h1.tsum_add h2]
  congr 1
  refine tsum_congr fun n => ?_
  rw [hX, qpow_neg_sub_one_pow hq]
  ring

/-- The same product formula needs the point-count identity only in positive degree. The `n = 0`
term of the defining series is zero regardless of the supplied count. -/
theorem zetaOfCounts_product_pos {q : ℝ} (hq : 0 < q) (cE cX : ℕ → ℂ)
    (hX : ∀ n, 0 < n → cX n = cE n + (q : ℂ) ^ n * cE n) {s : ℂ}
    (h1 : Summable fun n : ℕ => cE n * qpow q (-s) ^ n / n)
    (h2 : Summable fun n : ℕ => cE n * qpow q (-(s - 1)) ^ n / n) :
    zetaOfCounts q cX s = zetaOfCounts q cE s * zetaOfCounts q cE (s - 1) := by
  rw [zetaOfCounts, zetaOfCounts, zetaOfCounts, ← exp_add, ← h1.tsum_add h2]
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp
  · rw [hX n (Nat.pos_of_ne_zero hn), qpow_neg_sub_one_pow hq]
    ring

lemma norm_qpow {q : ℝ} (hq : 0 < q) (s : ℂ) : ‖qpow q s‖ = q ^ s.re := by
  rw [qpow, norm_exp, Real.rpow_def_of_pos hq]
  simp [mul_comm]

lemma hasSum_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / n) (-log (1 - z)) := hasSum_taylorSeries_neg_log hz

lemma one_sub_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hz; exact lt_irrefl _ hz

/-- The elliptic-curve zeta function (`eq:elliptic-zeta`): if
`#E(𝔽_{qⁿ}) = qⁿ + 1 - αⁿ - βⁿ` with `|α| = |β| = q^{1/2}`, then for `Re s > 1`,
`ζ_E(s) = (1 - αt)(1 - βt)/((1 - t)(1 - qt))`, `t = q^{-s}`; the defining series converges. -/
theorem zetaOfCounts_elliptic {q : ℝ} (hq : 1 < q) {α β : ℂ} (hα : ‖α‖ = q ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => ((q : ℂ) ^ n + 1 - α ^ n - β ^ n) * qpow q (-s) ^ n / n)
        (log (1 - α * qpow q (-s)) + log (1 - β * qpow q (-s)) - log (1 - qpow q (-s)) -
          log (1 - q * qpow q (-s))) ∧
      zetaOfCounts q (fun n => (q : ℂ) ^ n + 1 - α ^ n - β ^ n) s =
        (1 - α * qpow q (-s)) * (1 - β * qpow q (-s)) /
          ((1 - qpow q (-s)) * (1 - q * qpow q (-s))) := by
  have hq0 : (0 : ℝ) < q := by linarith
  set t := qpow q (-s)
  have ht : ‖t‖ = q ^ (-s.re) := by rw [norm_qpow hq0]; simp
  have hpow : ∀ x : ℝ, x < 0 → q ^ x < 1 := fun x hx => Real.rpow_lt_one_of_one_lt_of_neg hq hx
  have h1 : ‖t‖ < 1 := by rw [ht]; exact hpow _ (by linarith)
  have hqt : ‖(q : ℂ) * t‖ < 1 := by
    rw [norm_mul, ht, Complex.norm_real, Real.norm_of_nonneg hq0.le,
      ← Real.rpow_one_add' hq0.le (by linarith)]
    exact hpow _ (by linarith)
  have hγ : ∀ γ : ℂ, ‖γ‖ = q ^ ((1 : ℝ) / 2) → ‖γ * t‖ < 1 := by
    intro γ hγ
    rw [norm_mul, ht, hγ, ← Real.rpow_add hq0]
    exact hpow _ (by linarith)
  have hsum := (((hasSum_log hqt).add (hasSum_log h1)).sub (hasSum_log (hγ α hα))).sub
    (hasSum_log (hγ β hβ))
  have key : HasSum (fun n : ℕ => ((q : ℂ) ^ n + 1 - α ^ n - β ^ n) * t ^ n / n)
      (log (1 - α * t) + log (1 - β * t) - log (1 - t) - log (1 - q * t)) := by
    convert hsum using 1
    · funext n; simp only [mul_pow]; ring
    · ring
  refine ⟨key, ?_⟩
  rw [zetaOfCounts, key.tsum_eq, exp_sub, exp_sub, exp_add, exp_log (one_sub_ne_zero_of_norm_lt
    (hγ α hα)), exp_log (one_sub_ne_zero_of_norm_lt (hγ β hβ)),
    exp_log (one_sub_ne_zero_of_norm_lt h1), exp_log (one_sub_ne_zero_of_norm_lt hqt)]
  field_simp

/-- **`ζ_X` is the rational function `zetaX`** on `Re s > 2` (proof of `prop:N-lines` (ii)–(iii)):
with `#E(𝔽_{qⁿ}) = qⁿ + 1 - αⁿ - βⁿ`, `|α| = |β| = q^{1/2}` and
`#X(𝔽_{qⁿ}) = (1 + qⁿ) #E(𝔽_{qⁿ})` for `n > 0`, `ζ_X(s) = num(s)/den(s)`.
The degree-zero count is arbitrary. -/
theorem zetaOfCounts_eq_zetaX {q : ℝ} (hq : 1 < q) {α β : ℂ} (hα : ‖α‖ = q ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = q ^ ((1 : ℝ) / 2)) (cX : ℕ → ℂ)
    (hX : ∀ n, 0 < n → cX n = ((q : ℂ) ^ n + 1 - α ^ n - β ^ n) +
      (q : ℂ) ^ n * ((q : ℂ) ^ n + 1 - α ^ n - β ^ n)) {s : ℂ} (hs : 2 < s.re) :
    zetaOfCounts q cX s = zetaX q α β s := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hs1 : 1 < (s - 1).re := by simp; linarith
  obtain ⟨hE1, hZ1⟩ := zetaOfCounts_elliptic hq hα hβ (s := s) (by linarith)
  obtain ⟨hE2, hZ2⟩ := zetaOfCounts_elliptic hq hα hβ hs1
  rw [zetaOfCounts_product_pos hq0 _ cX hX hE1.summable hE2.summable, hZ1, hZ2, zetaX,
    num, den]
  have e1 := qpow_neg_sub_natCast hq0 s 1
  have e2 := qpow_neg_sub_natCast hq0 s 2
  simp only [Nat.cast_one, pow_one, Nat.cast_ofNat] at e1 e2
  rw [e2, e1, div_mul_div_comm]
  congr 1 <;> ring

end WeilRH.NLines
