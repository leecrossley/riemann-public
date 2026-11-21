/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.KunFq
import WeilRH.WeightedAlgebra

/-!
# A single branch destroys the divisor (`prop:one-branch`)

`prop:one-branch`: suspending `(ℂ, α)` with one logarithm `ρ₀ ∈ Σ_q(α)` gives `(ℂ, ρ₀)`, whose
spectral divisor is `[ρ₀]`, not the divisor of `1 - α q^{-s}`. The determinant clause needs the
regularized determinant of `def:regdet`, which is not formalized; we prove the rest and that
`(s - ρ₀) / 2π` is not a function of `q^{-s}`.

## Main results

* `OneBranch.one_branch`.
* `OneBranch.spec_scalar`, `OneBranch.mult_scalar`: spectrum and multiplicities of `(ℂ, ρ₀)`.
-/

open Module Complex WeilRH.Spectral WeilRH.Suspension WeilRH.KunFq

namespace WeilRH.OneBranch

/-- For `ρ ≠ ρ₀` the generalized `ρ`-eigenspace of `ρ₀ • 1` on `ℂ` is zero. -/
lemma maxGen_scalar_eq_bot {ρ₀ ρ : ℂ} (h : ρ ≠ ρ₀) :
    (ρ₀ • (1 : Module.End ℂ ℂ)).maxGenEigenspace ρ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  have : (ρ₀ • (1 : Module.End ℂ ℂ) - ρ • 1) = (ρ₀ - ρ) • 1 := by rw [sub_smul]
  rw [this, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at hk
  have hne : (ρ₀ - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (Ne.symm h))
  simpa [hne] using hk

/-- The generalized `ρ₀`-eigenspace of `ρ₀ • 1` on `ℂ` is everything. -/
lemma maxGen_scalar_self (ρ₀ : ℂ) :
    (ρ₀ • (1 : Module.End ℂ ℂ)).maxGenEigenspace ρ₀ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp⟩


/-- `spec (ρ₀ • 1) = {ρ₀}`. -/
lemma spec_scalar (ρ₀ : ℂ) : spec (ρ₀ • (1 : Module.End ℂ ℂ)) = {ρ₀} := by
  ext ρ
  simp only [spec, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h; by_contra hne; exact h (maxGen_scalar_eq_bot hne)
  · rintro rfl; rw [maxGen_scalar_self]; exact top_ne_bot

/-- The spectral divisor of `(ℂ, ρ₀)` is `[ρ₀]`. -/
lemma mult_scalar (ρ₀ ρ : ℂ) :
    mult (ρ₀ • (1 : Module.End ℂ ℂ)) ρ = if ρ = ρ₀ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [mult, maxGen_scalar_self, finrank_top, Module.finrank_self]
  · rw [mult, maxGen_scalar_eq_bot h, finrank_bot]

/-- **`prop:one-branch`, without the determinant clause.** For `q > 1` and `ρ₀ ∈ Σ_q(α)`, the
one-dimensional `(ℂ, ρ₀)` is a spectral core with spectrum `{ρ₀}`; `Σ_q(α)` is infinite; its
spectral divisor `[ρ₀]` differs from the divisor `Σ_{ρ ∈ Σ_q(α)} [ρ]` of `1 - α q^{-s}` (all of
whose zeros are simple, `prop:suspension` (i)); and the polynomial `(s - ρ₀) / 2π` is not a
function of `q^{-s}`. That `detreg((s - Θ)/2π) = (s - ρ₀)/2π` needs `def:regdet` (obligation 1). -/
theorem one_branch {q : ℝ} (hq : 1 < q) {α ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ logSusp q α) :
    SpectralCore (ρ₀ • (1 : Module.End ℂ ℂ)) ∧
    spec (ρ₀ • (1 : Module.End ℂ ℂ)) = {ρ₀} ∧
    (logSusp q α).Infinite ∧
    (fun ρ => (mult (ρ₀ • (1 : Module.End ℂ ℂ)) ρ : ℕ)) ≠ (logSusp q α).indicator 1 ∧
    ¬ ∃ g : ℂ → ℂ, ∀ s, (s - ρ₀) / (2 * Real.pi) = g (qpow q (-s)) := by
  have hmem : ∀ k : ℤ, ρ₀ + shift q k ∈ logSusp q α := fun k => by
    simp only [logSusp, Set.mem_ofPred_eq] at hρ₀ ⊢; rw [qpow_add_shift hq, hρ₀]
  have h0 : shift q 0 = 0 := by simp [shift]
  have h1 : shift q 1 ≠ 0 := fun h => by
    have := shift_injective hq (h.trans h0.symm); norm_num at this
  refine ⟨spectralCore_of_finiteDimensional _, spec_scalar ρ₀,
    Set.infinite_of_injective_forall_mem (fun a b hab => shift_injective hq (add_left_cancel hab))
      hmem, ?_, ?_⟩
  · intro hfun
    have := congrFun hfun (ρ₀ + shift q 1)
    rw [mult_scalar, Set.indicator_of_mem (hmem 1)] at this
    simp [h1] at this
  · rintro ⟨g, hg⟩
    have e1 := hg ρ₀
    have e2 := hg (ρ₀ + shift q 1)
    have hqp : qpow q (-(ρ₀ + shift q 1)) = qpow q (-ρ₀) := by
      rw [neg_add, ← sub_eq_add_neg, qpow_sub_shift hq]
    rw [hqp, ← e1] at e2
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    simp only [sub_self, zero_div, add_sub_cancel_left, div_eq_zero_iff, hπ, or_false] at e2
    exact h1 e2

end WeilRH.OneBranch
