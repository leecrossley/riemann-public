/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.Suspension

/-!
# `prop:kun-Fq-C`: the tensor product of two suspensions over `ℂ`

Round 21 formalization of `latex/notes.tex`, `prop:kun-Fq-C` (claim K-N5).

For `q > 1` and endomorphisms `F`, `G` of finite-dimensional complex spaces `V`, `W`, let
`V̂`, `Ŵ` be the logarithmic suspensions of `def:log-susp` (`Suspension.SuspSpace`, flow
`Suspension.theta`). Every generalized eigenspace of `Θ ⊗ 1 + 1 ⊗ Θ` (`Spectral.tensorSum`) on
`V̂ ⊗_ℂ Ŵ` is either zero or infinite-dimensional (`maxGenEigenspace_eq_bot_or_infinite`).

The proof is the manuscript's: a nonzero block `V̂_{ρ₁} ⊗ Ŵ_{ρ₂}` gives the nonzero blocks
`V̂_{ρ₁ + 2πik/log q} ⊗ Ŵ_{ρ₂ - 2πik/log q}`, `k ∈ ℤ`, all inside the generalized eigenspace at
`ρ₁ + ρ₂` (`prop:tensor-eigen`), and these are independent.
-/

open Module Complex TensorProduct

namespace WeilRH.KunFq

open WeilRH.Spectral WeilRH.Suspension

universe u

/-- The period shift `2πik / log q`. -/
noncomputable def shift (q : ℝ) (k : ℤ) : ℂ := 2 * Real.pi * I * k / Real.log q

lemma qpow_add_shift {q : ℝ} (hq : 1 < q) (ρ : ℂ) (k : ℤ) :
    qpow q (ρ + shift q k) = qpow q ρ := by
  have hL := WeilRH.log_ne_zero_of_one_lt hq
  have : (Real.log q : ℂ) * (ρ + shift q k) = Real.log q * ρ + k * (2 * Real.pi * I) := by
    rw [shift]; field_simp
  rw [qpow, qpow, this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma qpow_sub_shift {q : ℝ} (hq : 1 < q) (ρ : ℂ) (k : ℤ) :
    qpow q (ρ - shift q k) = qpow q ρ := by
  have : ρ - shift q k = ρ + shift q (-k) := by simp [shift, sub_eq_add_neg, neg_div]
  rw [this, qpow_add_shift hq]

lemma shift_injective {q : ℝ} (hq : 1 < q) : Function.Injective (shift q) := by
  intro a b h
  have hL := WeilRH.log_ne_zero_of_one_lt hq
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [shift] at h
  rw [div_left_inj' hL, mul_right_inj' h2] at h
  exact_mod_cast h

/-- A block of two nonzero finite-dimensional generalized eigenspaces is nonzero. -/
lemma block_ne_bot {V W : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) {ρ ρ' : ℂ}
    [FiniteDimensional ℂ (ΘV.maxGenEigenspace ρ)] [FiniteDimensional ℂ (ΘW.maxGenEigenspace ρ')]
    (h1 : ΘV.maxGenEigenspace ρ ≠ ⊥) (h2 : ΘW.maxGenEigenspace ρ' ≠ ⊥) :
    block ΘV ΘW ρ ρ' ≠ ⊥ := by
  intro hb
  have h0 : finrank ℂ (block ΘV ΘW ρ ρ') = 0 := by rw [hb]; exact finrank_bot ℂ _
  rw [← (blockEquiv ΘV ΘW ρ ρ').finrank_eq, Module.finrank_tensorProduct] at h0
  have := Submodule.nontrivial_iff_ne_bot.2 h1
  have := Submodule.nontrivial_iff_ne_bot.2 h2
  exact Nat.mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne' h0

/-- The core of `prop:kun-Fq-C` for abstract spectral cores. If `spec Θ_V` is stable under
`ρ ↦ ρ + c k` and `spec Θ_W` under `ρ ↦ ρ - c k` for an injective `c : ℤ → ℂ`, every generalized
eigenspace of `Θ_V ⊗ 1 + 1 ⊗ Θ_W` on `V ⊗ W` is zero or infinite-dimensional. -/
theorem maxGenEigenspace_eq_bot_or_infinite_of_shift {V W : Type u} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}
    (hV : SpectralCore ΘV) (hW : SpectralCore ΘW) {c : ℤ → ℂ} (hc : Function.Injective c)
    (hVs : ∀ ρ ∈ spec ΘV, ∀ k, ρ + c k ∈ spec ΘV) (hWs : ∀ ρ ∈ spec ΘW, ∀ k, ρ - c k ∈ spec ΘW)
    (lam : ℂ) :
    (tensorSum ΘV ΘW).maxGenEigenspace lam = ⊥ ∨
      ¬ Module.Finite ℂ ((tensorSum ΘV ΘW).maxGenEigenspace lam) := by
  classical
  rw [or_iff_not_imp_left]
  intro hne hfin
  set E := (tensorSum ΘV ΘW).maxGenEigenspace lam
  have := hV.finiteDimensional
  have := hW.finiteDimensional
  -- a nonzero block with `ρ₁ + ρ₂ = λ`
  obtain ⟨p, hp, hpb⟩ : ∃ p : ℂ × ℂ, p.1 + p.2 = lam ∧ block ΘV ΘW p.1 p.2 ≠ ⊥ := by
    by_contra! hall
    exact hne (by
      have hE : E = _ := maxGenEigenspace_tensorSum_eq ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top lam
      rw [hE]
      exact iSup₂_eq_bot.2 hall)
  have h1 : p.1 ∈ spec ΘV := fun h => hpb (block_eq_bot_of_left ΘV ΘW p.2 h)
  have h2 : p.2 ∈ spec ΘW := fun h => hpb (block_eq_bot_of_right ΘV ΘW p.1 h)
  -- the shifted pairs
  let s : ℤ → {p : ℂ × ℂ // p.1 + p.2 = lam} := fun k =>
    ⟨(p.1 + c k, p.2 - c k), by simp only; rw [← hp]; ring⟩
  -- the independent family of blocks inside `E`
  let f : {p : ℂ × ℂ // p.1 + p.2 = lam} → Submodule ℂ E := fun p =>
    (block ΘV ΘW p.1.1 p.1.2).comap E.subtype
  have hind : iSupIndep f :=
    (isInternal_block_maxGenEigenspace ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top
      lam).submodule_iSupIndep
  have hs : ∀ k, f (s k) ≠ ⊥ := by
    intro k
    have hb : block ΘV ΘW (s k).1.1 (s k).1.2 ≠ ⊥ :=
      block_ne_bot ΘV ΘW (hVs _ h1 k) (hWs _ h2 k)
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hb
    have hle : x ∈ E := by
      have := block_le ΘV ΘW (s k).1.1 (s k).1.2 hx
      rwa [(s k).2] at this
    exact (Submodule.ne_bot_iff _).2 ⟨⟨x, hle⟩, hx, fun h => hx0 (congrArg Subtype.val h)⟩
  let := hind.fintypeNeBotOfFiniteDimensional
  refine not_injective_infinite_finite (fun k : ℤ => (⟨s k, hs k⟩ : {i // f i ≠ ⊥})) ?_
  intro a b hab
  have := congrArg (fun x : {i // f i ≠ ⊥} => x.1.1.1) hab
  simp only [s, add_right_inj] at this
  exact hc this

variable {V W : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

lemma mem_spec_theta_add_shift {q : ℝ} (hq : 1 < q) (F : Module.End ℂ V) {ρ : ℂ}
    (h : ρ ∈ spec (theta F q)) (k : ℤ) : ρ + shift q k ∈ spec (theta F q) := by
  rw [spec_theta] at h ⊢
  simpa [qpow_add_shift hq] using h

lemma mem_spec_theta_sub_shift {q : ℝ} (hq : 1 < q) (F : Module.End ℂ V) {ρ : ℂ}
    (h : ρ ∈ spec (theta F q)) (k : ℤ) : ρ - shift q k ∈ spec (theta F q) := by
  rw [spec_theta] at h ⊢
  simpa [qpow_sub_shift hq] using h

/-- **`prop:kun-Fq-C`.** For `q > 1` and endomorphisms `F`, `G` of finite-dimensional complex
spaces, every generalized eigenspace of `Θ ⊗ 1 + 1 ⊗ Θ` on the tensor product `V̂ ⊗_ℂ Ŵ` of the
logarithmic suspensions is either zero or infinite-dimensional. The source's hypotheses that
`V`, `W` are nonzero and `F`, `G` invertible are not needed. -/
theorem maxGenEigenspace_eq_bot_or_infinite {q : ℝ} (hq : 1 < q) (F : Module.End ℂ V)
    (G : Module.End ℂ W) (lam : ℂ) :
    Module.End.maxGenEigenspace (R := ℂ) (M := SuspSpace F q ⊗[ℂ] SuspSpace G q)
        (tensorSum (theta F q) (theta G q)) lam = ⊥ ∨
      ¬ Module.Finite ℂ (Module.End.maxGenEigenspace (R := ℂ)
        (M := SuspSpace F q ⊗[ℂ] SuspSpace G q) (tensorSum (theta F q) (theta G q)) lam) :=
  maxGenEigenspace_eq_bot_or_infinite_of_shift (spectralCore_theta F hq) (spectralCore_theta G hq)
    (shift_injective hq) (fun _ h k => mem_spec_theta_add_shift hq F h k)
    (fun _ h k => mem_spec_theta_sub_shift hq G h k) lam

end WeilRH.KunFq
