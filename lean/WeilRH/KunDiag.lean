/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# `prop:kun-diag` (iii)–(v): counting eigenvalues of a tensor sum of diagonal operators

`latex/notes.tex`, `def:tensor-diag` and `prop:kun-diag`. For real diagonal operators
`T₁ = diag(τ_i)` and `T₂ = diag(τ'_k)` the tensor sum `T = T₁ ⊞ T₂` is `diag(τ_i + τ'_k)` on the
basis `e_i ⊗ f_k`. A diagonal operator's eigenvalues, with multiplicity, are its diagonal entries,
so its counting function `N_T(R)` (eigenvalues of absolute value `≤ R`, with multiplicity) is the
number of indices with `|entry| ≤ R`.

**Representation.** This module works with the diagonal entries only: `N τ R` is the cardinality
(in `ℕ∞`, so infinite counts are allowed) of `{i | |τ i| ≤ R}`, and `Nsum τ τ' R` that of the pairs
`{(i,k) | |τ i + τ' k| ≤ R}`, which is `N_{T₁ ⊞ T₂}(R)`. The Hilbert tensor product, self-adjointness
and compact resolvent are not modelled; "compact resolvent" enters only through its spectral
characterization for diagonal operators, finiteness of every `N(R)` (the content of (ii), which is
not proved here).

* (iii) `KunDiag.Nsum_le`: if `τ_i ≥ −c₁`, `τ'_k ≥ −c₂` with `c₁, c₂ ≥ 0`, then
  `N_T(R) ≤ N_{T₁}(R+c) N_{T₂}(R+c)`, `c = c₁ + c₂`, for every `R ≥ 0`; and `Nsum_finite`: if every
  `N_{T₁}(R)`, `N_{T₂}(R)` is finite then so is every `N_T(R)`.
* (iv) `KunDiag.zero_infinite`: infinitely many pairs with `τ_i + τ'_k = 0` give infinitely many
  basis eigenvectors for `0`, and `N_T(0) = ⊤`.
* (v) `KunDiag.sharp_one`, `KunDiag.sharp_two`: the manuscript's two counterexamples.
* (i), (ii) are not formalized.
-/

namespace WeilRH
namespace KunDiag

variable {I I' : Type*}

/-- `N_{diag(τ)}(R)`: indices with `|τ i| ≤ R`, counted in `ℕ∞`. -/
noncomputable def N (τ : I → ℝ) (R : ℝ) : ℕ∞ := {i | |τ i| ≤ R}.encard

/-- `N_{T₁ ⊞ T₂}(R)`: pairs `(i,k)` with `|τ i + τ' k| ≤ R`. -/
noncomputable def Nsum (τ : I → ℝ) (τ' : I' → ℝ) (R : ℝ) : ℕ∞ :=
  {p : I × I' | |τ p.1 + τ' p.2| ≤ R}.encard

theorem pairs_subset {τ : I → ℝ} {τ' : I' → ℝ} {c₁ c₂ R : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hR : 0 ≤ R) (h₁ : ∀ i, -c₁ ≤ τ i) (h₂ : ∀ k, -c₂ ≤ τ' k) :
    {p : I × I' | |τ p.1 + τ' p.2| ≤ R} ⊆
      {i | |τ i| ≤ R + (c₁ + c₂)} ×ˢ {k | |τ' k| ≤ R + (c₁ + c₂)} := by
  rintro ⟨i, k⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  have hp' := abs_le.1 hp
  have hi := h₁ i
  have hk := h₂ k
  refine ⟨?_, ?_⟩ <;> simp only [Set.mem_ofPred_eq] <;> rw [abs_le] <;> constructor <;> linarith

/-- **`prop:kun-diag` (iii), counting bound.** -/
theorem Nsum_le {τ : I → ℝ} {τ' : I' → ℝ} {c₁ c₂ R : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hR : 0 ≤ R) (h₁ : ∀ i, -c₁ ≤ τ i) (h₂ : ∀ k, -c₂ ≤ τ' k) :
    Nsum τ τ' R ≤ N τ (R + (c₁ + c₂)) * N τ' (R + (c₁ + c₂)) := by
  unfold Nsum N
  calc {p : I × I' | |τ p.1 + τ' p.2| ≤ R}.encard
      ≤ ({i | |τ i| ≤ R + (c₁ + c₂)} ×ˢ {k | |τ' k| ≤ R + (c₁ + c₂)}).encard :=
        Set.encard_le_encard (pairs_subset hc₁ hc₂ hR h₁ h₂)
    _ = _ := Set.encard_prod

/-- **`prop:kun-diag` (iii), finiteness.** If every `N_{T₁}(R)` and `N_{T₂}(R)` is finite (compact
resolvent, for diagonal operators), then every `N_T(R)` is finite. -/
theorem Nsum_finite {τ : I → ℝ} {τ' : I' → ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h₁ : ∀ i, -c₁ ≤ τ i) (h₂ : ∀ k, -c₂ ≤ τ' k)
    (hT₁ : ∀ R, {i | |τ i| ≤ R}.Finite) (hT₂ : ∀ R, {k | |τ' k| ≤ R}.Finite) :
    ∀ R, {p : I × I' | |τ p.1 + τ' p.2| ≤ R}.Finite := by
  intro R
  rcases lt_or_ge R 0 with hR | hR
  · refine Set.Finite.subset Set.finite_empty (fun p hp => ?_)
    have := abs_nonneg (τ p.1 + τ' p.2)
    simp only [Set.mem_ofPred_eq] at hp; linarith
  · exact ((hT₁ _).prod (hT₂ _)).subset (pairs_subset hc₁ hc₂ hR h₁ h₂)

/-- **`prop:kun-diag` (iv).** If infinitely many pairs have `τ_i + τ'_k = 0`, the eigenvalue `0`
of `T` has infinitely many basis eigenvectors `e_i ⊗ f_k`, so `N_T(0) = ⊤` and `T` does not have
compact resolvent in the sense of finite counting functions. -/
theorem zero_infinite {τ : I → ℝ} {τ' : I' → ℝ}
    (h : {p : I × I' | τ p.1 + τ' p.2 = 0}.Infinite) :
    Nsum τ τ' 0 = ⊤ ∧ ¬ {p : I × I' | |τ p.1 + τ' p.2| ≤ 0}.Finite := by
  have hset : {p : I × I' | |τ p.1 + τ' p.2| ≤ 0} = {p : I × I' | τ p.1 + τ' p.2 = 0} := by
    ext p; simp [abs_nonpos_iff]
  refine ⟨?_, ?_⟩
  · unfold Nsum; rw [hset]; exact Set.Infinite.encard_eq h
  · rw [hset]; exact h

/-- First counterexample of (v): `{τ_i} = {−10} ∪ {1, 2, 3, …}`. -/
noncomputable def τA : ℕ → ℝ := fun n => if n = 0 then -10 else n

/-- First counterexample of (v): `{τ'_k} = {10, 11, 12, …}`. -/
noncomputable def τA' : ℕ → ℝ := fun n => 10 + n

/-- **`prop:kun-diag` (v), first bound.** With `c₁ = 10`, `c₂ = 0`, the bound
`N_T(R) ≤ N_{T₁}(R+c₂) N_{T₂}(R+c₁)` fails at `R = 0`. -/
theorem sharp_one : (∀ i, -10 ≤ τA i) ∧ (∀ k, -0 ≤ τA' k) ∧
    ¬ Nsum τA τA' 0 ≤ N τA (0 + 0) * N τA' (0 + 10) := by
  refine ⟨fun i => ?_, fun k => ?_, ?_⟩
  · unfold τA; split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ i := by positivity
      linarith
  · unfold τA'; simp; positivity
  · have hN1 : N τA (0 + 0) = 0 := by
      unfold N; rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [Set.mem_ofPred_eq, add_zero, abs_nonpos_iff, τA] at hi
      split_ifs at hi with h
      · norm_num at hi
      · exact h (by exact_mod_cast hi)
    have hpos : (0 : ℕ∞) < Nsum τA τA' 0 := by
      unfold Nsum
      rw [Set.encard_pos]
      exact ⟨(0, 0), by simp [τA, τA']⟩
    rw [hN1, zero_mul]
    exact not_le.2 hpos

/-- Second counterexample of (v): `{τ_i} = {10, 11, …}`. -/
noncomputable def τB : ℕ → ℝ := fun n => 10 + n

/-- Second counterexample of (v): `{τ'_k} = {0, 1, 2, …}`. -/
noncomputable def τB' : ℕ → ℝ := fun n => n

/-- **`prop:kun-diag` (v), second bound.** With `c₁ = −10`, `c₂ = 0` (so `c = −10`), the bound
`N_T(R) ≤ N_{T₁}(R+c) N_{T₂}(R+c)` fails at `R = 10`. -/
theorem sharp_two : (∀ i, -(-10) ≤ τB i) ∧ (∀ k, -0 ≤ τB' k) ∧
    ¬ Nsum τB τB' 10 ≤ N τB (10 + (-10 + 0)) * N τB' (10 + (-10 + 0)) := by
  refine ⟨fun i => ?_, fun k => ?_, ?_⟩
  · unfold τB; simp
  · unfold τB'; simp
  · have hN1 : N τB (10 + (-10 + 0)) = 0 := by
      unfold N; rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [Set.mem_ofPred_eq, τB] at hi
      have : (0 : ℝ) ≤ i := by positivity
      have := (abs_le.1 hi).2
      linarith
    have hpos : (0 : ℕ∞) < Nsum τB τB' 10 := by
      unfold Nsum
      rw [Set.encard_pos]
      exact ⟨(0, 0), by simp [τB, τB']⟩
    rw [hN1, zero_mul]
    exact not_le.2 hpos

end KunDiag
end WeilRH
