/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Lefschetz numbers determine the alternating divisor (`thm:ff-lefschetz`, finite-dimensional core)

Source: `latex/notes.tex`, Definition `def:lefschetz-numbers` and Theorem `thm:ff-lefschetz`.

## What is formalized

The finite-dimensional content of the calibration: the Frobenius data of a variety over `𝔽_q` is,
degree by degree (`j = 0, …, n-1`), a finite multiset `M j` of eigenvalues counted with algebraic
multiplicity (the roots of the characteristic polynomial of `F` on `V^j`). Its Lefschetz numbers
are `N_k = ∑_j (-1)^j ∑_{α ∈ M j} α^k` (`lefschetzNumber`; this is `∑_j (-1)^j Tr(F^k | V^j)` once
`Tr(F^k | V^j) = ∑_{α ∈ M j} α^k`, which is how the notes' proofs use it), its alternating
multiplicity function is `α ↦ ∑_j (-1)^j m_j(α)` (`altCount`), and its zeta function is the
rational function `∏_j det(1 - F T | V^j)^{(-1)^{j+1}} = ∏_j (∏_{α ∈ M j} (1 - αT))^{(-1)^{j+1}}`
(`zetaRat`, in `RatFunc ℂ`).

* `sum_mul_pow_eq_zero` (uniqueness of finite exponential sums, Dedekind/Artin independence of
  the characters `k ↦ α^k`): if `∑_{α ∈ s} c(α) α^k = 0` for all `k ≥ 1`, then `c(α) = 0` for all
  `α ≠ 0`.
* `altCount_eq_of_lefschetzNumber_eq` (**Lefschetz data for all `k ≥ 1` determine the
  alternating divisor**): equal Lefschetz numbers `N_k` for every `k ≥ 1` force equal alternating
  multiplicities at every `α ≠ 0`.
* `zetaRat_eq_of_altCount_eq`, `zetaRat_eq_of_lefschetzNumber_eq` (**rationality**): hence the
  rational functions `∏_j det(1 - F_j T)^{(-1)^{j+1}}` coincide.
* `zetaRat_eq_prod`: `zetaRat M = ∏_α (1 - αT)^{-altCount M α}`, the rational function whose
  divisor is the alternating divisor.

## What is not formalized

Item (i) (point counts `N_k = #X(𝔽_{q^k})` via the Grothendieck–Lefschetz trace formula, `N_0`,
and duality `N_{-k} = q^{-dk} N_k`), item (ii) (the Poisson-summation identity on the suspended
datum) and item (iii) for an infinite spectrum and a one-sided tail of test functions (it rests on
`prop:exp-unique`). The theorem here is the finite analogue of (iii): the Lefschetz numbers for
all `k ≥ 1` determine `∑_j (-1)^{j+1} Sp_j` among finite data, and hence the zeta function.
-/

open Polynomial Finset

namespace WeilRH

namespace Lefschetz

/-- **Uniqueness of finite exponential sums.** If `∑_{α ∈ s} c(α) α^k = 0` for every `k ≥ 1`,
then `c(α) = 0` for every nonzero `α ∈ s`. -/
theorem sum_mul_pow_eq_zero {s : Finset ℂ} {c : ℂ → ℂ}
    (h : ∀ k : ℕ, 1 ≤ k → ∑ α ∈ s, c α * α ^ k = 0) {α : ℂ} (hα : α ∈ s) (hα0 : α ≠ 0) :
    c α = 0 := by
  -- characters `k ↦ β^k` of `Multiplicative ℕ` are linearly independent
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp
    (fun β : ℂ => powersHom ℂ β) (powersHom ℂ).injective
  have key := linearIndependent_iff'.1 hli s (fun β => c β * β) ?_ α hα
  · exact (mul_eq_zero.1 key).resolve_right hα0
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
  have := h (Multiplicative.toAdd k + 1) (by omega)
  rw [← this]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp [powersHom_apply, pow_succ]
  ring

variable {n : ℕ}

/-- The Lefschetz number `N_k = ∑_j (-1)^j ∑_{α ∈ M j} α^k` of degreewise eigenvalue data
`M : ℕ → Multiset ℂ` in degrees `j < n` (`def:lefschetz-numbers`). -/
noncomputable def lefschetzNumber (n : ℕ) (M : ℕ → Multiset ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range n, (-1) ^ j * ((M j).map (· ^ k)).sum

/-- The alternating multiplicity `∑_j (-1)^j m_j(α)`, the coefficient of `α` in the alternating
divisor `∑_j (-1)^j Sp_j`. -/
noncomputable def altCount (n : ℕ) (M : ℕ → Multiset ℂ) (α : ℂ) : ℤ :=
  ∑ j ∈ range n, (-1) ^ j * ((M j).count α : ℤ)

/-- All eigenvalues occurring in some degree `j < n`. -/
noncomputable def support (n : ℕ) (M : ℕ → Multiset ℂ) : Finset ℂ :=
  (range n).biUnion fun j => (M j).toFinset

lemma count_eq_zero_of_not_mem_support {M : ℕ → Multiset ℂ} {α : ℂ} (hα : α ∉ support n M)
    {j : ℕ} (hj : j ∈ range n) : (M j).count α = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  exact hα (mem_biUnion.2 ⟨j, hj, Multiset.mem_toFinset.2 h⟩)

lemma altCount_eq_zero_of_not_mem {M : ℕ → Multiset ℂ} {α : ℂ} (hα : α ∉ support n M) :
    altCount n M α = 0 :=
  sum_eq_zero fun j hj => by rw [count_eq_zero_of_not_mem_support hα hj]; simp

/-- `N_k = ∑_α (∑_j (-1)^j m_j(α)) α^k`, the sum running over any finite set containing the
eigenvalues. -/
theorem lefschetzNumber_eq_sum (M : ℕ → Multiset ℂ) {s : Finset ℂ} (hs : support n M ⊆ s)
    (k : ℕ) : lefschetzNumber n M k = ∑ α ∈ s, (altCount n M α : ℂ) * α ^ k := by
  simp only [lefschetzNumber, altCount, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [Finset.sum_multiset_map_count]
  have hsub : (M j).toFinset ⊆ s := fun α hα => hs (mem_biUnion.2 ⟨j, hj, hα⟩)
  rw [← sum_subset hsub, mul_sum]
  · refine sum_congr rfl fun α _ => ?_
    rw [nsmul_eq_mul]
    ring
  · intro α _ hα
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hα
    simp [hα]

/-- **`thm:ff-lefschetz`, finite-dimensional core.** If two degreewise eigenvalue data have the
same Lefschetz numbers `N_k` for every `k ≥ 1`, their alternating multiplicity functions agree at
every nonzero `α`: the Lefschetz numbers determine the alternating divisor. -/
theorem altCount_eq_of_lefschetzNumber_eq {M M' : ℕ → Multiset ℂ}
    (h : ∀ k : ℕ, 1 ≤ k → lefschetzNumber n M k = lefschetzNumber n M' k) {α : ℂ} (hα : α ≠ 0) :
    altCount n M α = altCount n M' α := by
  set s := support n M ∪ support n M'
  by_cases hs : α ∈ s
  · have hk : ∀ k : ℕ, 1 ≤ k →
        ∑ β ∈ s, ((altCount n M β : ℂ) - altCount n M' β) * β ^ k = 0 := by
      intro k hk
      simp_rw [sub_mul, sum_sub_distrib]
      rw [← lefschetzNumber_eq_sum M subset_union_left, ← lefschetzNumber_eq_sum M' subset_union_right,
        h k hk, sub_self]
    have := sum_mul_pow_eq_zero hk hs hα
    exact_mod_cast sub_eq_zero.1 this
  · rw [altCount_eq_zero_of_not_mem (fun h => hs (mem_union_left _ h)),
      altCount_eq_zero_of_not_mem (fun h => hs (mem_union_right _ h))]

/-! ### The zeta function as a rational function -/

lemma prod_zpow_eq_zpow_sum {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add]

/-- `1 - αT` as a unit of `RatFunc ℂ`. -/
noncomputable def linFactor (α : ℂ) : (RatFunc ℂ)ˣ :=
  Units.mk0 (algebraMap ℂ[X] (RatFunc ℂ) (1 - C α * X)) (by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h
    have := congrArg (coeff · 0) h
    simp at this)

@[simp] lemma linFactor_zero : linFactor 0 = 1 := by
  ext
  simp [linFactor]

/-- `det(1 - F T | V^j) = ∏_{α ∈ M j} (1 - αT)`, as a unit of `RatFunc ℂ`. -/
noncomputable def detFactor (m : Multiset ℂ) : (RatFunc ℂ)ˣ := (m.map linFactor).prod

/-- The zeta function `∏_{j<n} det(1 - F T | V^j)^{(-1)^{j+1}}` (a rational function). -/
noncomputable def zetaRat (n : ℕ) (M : ℕ → Multiset ℂ) : (RatFunc ℂ)ˣ :=
  ∏ j ∈ range n, detFactor (M j) ^ ((-1 : ℤ) ^ (j + 1))

lemma detFactor_eq_prod (m : Multiset ℂ) {s : Finset ℂ} (hs : m.toFinset ⊆ s) :
    detFactor m = ∏ α ∈ s, linFactor α ^ (m.count α : ℤ) := by
  rw [detFactor, Finset.prod_multiset_map_count, ← prod_subset hs]
  · simp
  · intro α _ hα
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hα
    simp [hα]

/-- `zetaRat M = ∏_{α ∈ s} (1 - αT)^{-∑_j (-1)^j m_j(α)}`: the divisor of the zeta function is
minus the alternating divisor. -/
theorem zetaRat_eq_prod (M : ℕ → Multiset ℂ) {s : Finset ℂ} (hs : support n M ⊆ s) :
    zetaRat n M = ∏ α ∈ s, linFactor α ^ (-altCount n M α) := by
  rw [zetaRat]
  have : ∀ j ∈ range n, detFactor (M j) ^ ((-1 : ℤ) ^ (j + 1)) =
      ∏ α ∈ s, linFactor α ^ ((-1 : ℤ) ^ (j + 1) * (M j).count α) := by
    intro j hj
    rw [detFactor_eq_prod (M j) (fun α hα => hs (mem_biUnion.2 ⟨j, hj, hα⟩)), ← prod_zpow]
    refine prod_congr rfl fun α _ => ?_
    rw [← zpow_mul, mul_comm]
  rw [prod_congr rfl this, prod_comm]
  refine prod_congr rfl fun α _ => ?_
  rw [prod_zpow_eq_zpow_sum, altCount, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **Rationality: the alternating divisor determines the zeta function.** -/
theorem zetaRat_eq_of_altCount_eq {M M' : ℕ → Multiset ℂ}
    (h : ∀ α : ℂ, α ≠ 0 → altCount n M α = altCount n M' α) : zetaRat n M = zetaRat n M' := by
  rw [zetaRat_eq_prod M (subset_union_left (s₂ := support n M')),
    zetaRat_eq_prod M' (subset_union_right (s₁ := support n M))]
  refine prod_congr rfl fun α _ => ?_
  rcases eq_or_ne α 0 with rfl | hα
  · simp
  · rw [h α hα]

/-- **`thm:ff-lefschetz`, finite-dimensional core (zeta form).** Equal Lefschetz numbers for all
`k ≥ 1` give equal rational functions `∏_j det(1 - F_j T)^{(-1)^{j+1}}`. -/
theorem zetaRat_eq_of_lefschetzNumber_eq {M M' : ℕ → Multiset ℂ}
    (h : ∀ k : ℕ, 1 ≤ k → lefschetzNumber n M k = lefschetzNumber n M' k) :
    zetaRat n M = zetaRat n M' :=
  zetaRat_eq_of_altCount_eq fun _ hα => altCount_eq_of_lefschetzNumber_eq h hα

end Lefschetz

end WeilRH
