/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Completed
import WeilRH.KunOrbits

/-!
# Local spectral cores (`prop:R7`)

Source: the manuscript `latex/notes.tex`, `def:R7-local` and `prop:R7`. The local spectral core at
a prime `p` is the logarithmic suspension of `(ℂ, 1)` at `q = p`, which is `KunOrbits.unitTheta p`.

## Main results

* `WeilRH.R7.spec_local`, `WeilRH.R7.shift_eq_shift_iff`: **`prop:R7` (i)** for each local core,
  and the unique-factorization step that makes the nonzero eigenvalues of `V_𝒬` simple.
* `WeilRH.R7.completedXi_ne_zero_of_re_eq_zero`, `WeilRH.R7.completedXi_ne_zero_of_mem_spec`:
  **`prop:R7` (iii)**.
* `WeilRH.R7.summable_iff`: **`prop:R7` (iv)**.

* `WeilRH.R7.VQ`, `WeilRH.R7.thetaQ`: **`def:R7-local`**, `V_𝒬 = ⨁_{p ∈ 𝒬} V_p` with
  `Θ_𝒬 = ⨁_p Θ_p`.
* `WeilRH.R7.mem_spec_thetaQ`, `WeilRH.R7.re_eq_zero_of_mem_spec`,
  `WeilRH.R7.rank_maxGenEigenspace_zero`, `WeilRH.R7.mult_zero`, `WeilRH.R7.mult_eq_one`:
  **`prop:R7` (i)** for `V_𝒬`: `spec Θ_𝒬 = ⋃_p (2πi / log p) ℤ ⊂ iℝ`, the eigenvalue `0` has
  multiplicity `#𝒬` (as a cardinal), and every nonzero eigenvalue is simple.
* `WeilRH.R7.not_spectralCore`: **`prop:R7` (ii)**.
* `WeilRH.R7.completedXi_ne_zero_of_mem_specQ`: **`prop:R7` (iii)** for `V_𝒬`.

The generic facts about `⨁ T_i` used here (`mem_maxGenEigenspace_diag_iff`, `spec_diag`,
`maxGenEquiv`, `rank_maxGenEigenspace_diag`, `maxGenEquivSingle`) need no injectivity of the
eigenvalue labels, unlike `Suspension.mem_maxGenEigenspace_diag`.

`thetaQ` is a `def` whose type names the `AddCommGroup`-derived `AddCommMonoid` instance, and the
statements pass `(V := VQ 𝒬)` explicitly: without it, elaboration of `spec (thetaQ 𝒬)` fails to
unify the two `AddCommMonoid` instances on the nested direct sum.
-/

open Module Complex
open scoped DirectSum

namespace WeilRH.R7

open WeilRH.Spectral WeilRH.Suspension WeilRH.KunFq WeilRH.KunOrbits

/-- **`prop:R7` (i)**, eigenvalues of one local core: `spec Θ_p = (2πi / log p) ℤ ⊂ iℝ`, and each
eigenvalue is simple. -/
theorem spec_local (p : ℕ) (hp : p.Prime) :
    (∀ ρ, ρ ∈ spec (unitTheta p) ↔ ∃ n : ℤ, ρ = shift p n) ∧
      (∀ ρ ∈ spec (unitTheta p), ρ.re = 0) ∧ ∀ n : ℤ, mult (unitTheta p) (shift p n) = 1 := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨mem_spec_unit_iff hq, fun ρ hρ => ?_, mult_unit hq⟩
  obtain ⟨n, rfl⟩ := (mem_spec_unit_iff hq ρ).1 hρ
  rw [shift_eq, mul_I_re, ofReal_im, neg_zero]

/-- **`prop:R7` (i)**, across primes: for distinct primes the local spectra meet only in `0`, so
in `V_𝒬` the nonzero eigenvalues are simple. -/
theorem shift_eq_shift_iff {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') (n m : ℤ) :
    shift p n = shift p' m ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    have := @shift_add_shift_injective p p' hp hp' hne (n, -m) (0, 0) (by
      simp only [shift, Int.cast_neg, Int.cast_zero, mul_zero, zero_div, add_zero] at h ⊢
      rw [h]; ring)
    simp only [Prod.mk.injEq, neg_eq_zero] at this
    exact this
  · rintro ⟨rfl, rfl⟩; simp [shift]


/-- **`prop:R7` (iii)**, analytic part: `ξ` has no zero on `Re s = 0`. -/
theorem completedXi_ne_zero_of_re_eq_zero {ρ : ℂ} (hρ : ρ.re = 0) : completedXi ρ ≠ 0 := by
  intro h
  rw [← completedXi_one_sub, completedXi_eq_zero_iff] at h
  exact riemannZeta_ne_zero_of_one_le_re (by simp [hρ]) h.1

lemma norm_cpow_neg (p : Nat.Primes) (s : ℂ) : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  simpa using Complex.norm_natCast_cpow_of_pos p.2.pos (-s)

lemma one_sub_ne_zero (p : Nat.Primes) {s : ℂ} (hs : (p : ℂ) ^ s ≠ 1) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  rw [sub_ne_zero, cpow_neg]; intro h; exact hs (by simpa using congrArg (·⁻¹) h.symm)

lemma norm_term (p : Nat.Primes) {s : ℂ} (hs : (p : ℂ) ^ s ≠ 1) :
    ‖(1 - (p : ℂ) ^ (-s))⁻¹ - 1‖ = (p : ℝ) ^ (-s.re) / ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h1 := one_sub_ne_zero p hs
  have : (1 - (p : ℂ) ^ (-s))⁻¹ - 1 = (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) := by
    field_simp; ring
  rw [this, norm_div, norm_cpow_neg]

/-- **`prop:R7` (iv).** -/
theorem summable_iff (s : ℂ) (hs : ∀ p : Nat.Primes, (p : ℂ) ^ s ≠ 1) :
    Summable (fun p : Nat.Primes => ‖(1 - (p : ℂ) ^ (-s))⁻¹ - 1‖) ↔ 1 < s.re := by
  have hp : ∀ p : Nat.Primes, (2 : ℝ) ≤ p := fun p => by exact_mod_cast p.2.two_le
  have hinv : ∀ p : Nat.Primes, ((p : ℝ))⁻¹ ≤ 1 / 2 := fun p => by
    rw [inv_le_comm₀ (by linarith [hp p]) (by norm_num)]; linarith [hp p]
  have hup : ∀ p : Nat.Primes, ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-s.re) := fun p => by
    simpa [norm_cpow_neg] using norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
  constructor
  · intro hsum
    by_contra hle
    push Not at hle
    apply (Nat.Primes.summable_rpow (r := -1)).not.mpr (lt_irrefl _)
    refine (hsum.mul_left 2).of_nonneg_of_le (fun p => by positivity) fun p => ?_
    have h0 : (0 : ℝ) < p := by linarith [hp p]
    have hpow : (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hp p]) (by linarith)
    rw [Real.rpow_neg_one] at hpow ⊢
    have hd : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := norm_pos_iff.2 (one_sub_ne_zero p (hs p))
    rw [norm_term p (hs p), mul_div_assoc', le_div_iff₀ hd]
    have := hinv p
    calc (p : ℝ)⁻¹ * ‖1 - (p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ * (1 + (p : ℝ) ^ (-s.re)) :=
          mul_le_mul_of_nonneg_left (hup p) (by positivity)
      _ ≤ 2 * (p : ℝ) ^ (-s.re) := by
          have hr0 : 0 ≤ (p : ℝ) ^ (-s.re) := (Real.rpow_pos_of_pos h0 _).le
          have := mul_le_mul_of_nonneg_right this hr0
          nlinarith
  · intro hσ
    refine (((Nat.Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left 2).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun p => ?_
    have h0 : (0 : ℝ) < p := by linarith [hp p]
    have hpos : 0 < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos h0 _
    have hsmall : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
      calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [hp p]) (by linarith)
        _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := hinv p
    have hlow : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
      rw [norm_one, norm_cpow_neg] at this; linarith
    rw [norm_term p (hs p), div_le_iff₀ (by linarith)]
    nlinarith

/-- **`prop:R7` (iii).** No eigenvalue of a local core `Θ_p` is a zero of `ξ`. -/
theorem completedXi_ne_zero_of_mem_spec (p : ℕ) (hp : p.Prime) {ρ : ℂ}
    (hρ : ρ ∈ spec (unitTheta p)) : completedXi ρ ≠ 0 :=
  completedXi_ne_zero_of_re_eq_zero ((spec_local p hp).2.1 ρ hρ)


section DiagSum

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module ℂ (M i)] (T : ∀ i, Module.End ℂ (M i))

/-- A vector of `⨁ M_i` is a generalized `ρ`-eigenvector of `⨁ T_i` iff each component is one of
`T_i`. -/
theorem mem_maxGenEigenspace_diag_iff (ρ : ℂ) (x : ⨁ i, M i) :
    x ∈ (diag T).maxGenEigenspace ρ ↔ ∀ i, x i ∈ (T i).maxGenEigenspace ρ := by
  simp only [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩ i
    exact ⟨k, by rw [← diag_sub_pow_apply, hk, DirectSum.zero_apply]⟩
  · intro h
    classical
    choose k hk using h
    refine ⟨x.support.sup k, ?_⟩
    ext i
    rw [diag_sub_pow_apply, DirectSum.zero_apply]
    by_cases hi : i ∈ x.support
    · have hle : k i ≤ x.support.sup k := Finset.le_sup hi
      rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hk, map_zero]
    · rw [DFinsupp.notMem_support_iff.1 hi, map_zero]

/-- `spec (⨁ T_i) = ⋃ spec T_i`. -/
theorem spec_diag (ρ : ℂ) : ρ ∈ spec (diag T) ↔ ∃ i, ρ ∈ spec (T i) := by
  simp only [spec, Set.mem_ofPred_eq, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hx, hx0⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h; push Not at h; exact hx0 (DFinsupp.ext h)
    exact ⟨i, x i, (mem_maxGenEigenspace_diag_iff T ρ x).1 hx i, hi⟩
  · rintro ⟨i, y, hy, hy0⟩
    refine ⟨DirectSum.lof ℂ ι M i y, (mem_maxGenEigenspace_diag_iff T ρ _).2 fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simpa using hy
      · have h0 : (DirectSum.lof ℂ ι M i y) j = 0 := by
          rw [DirectSum.lof_eq_of]; exact DirectSum.of_eq_of_ne _ _ _ (by tauto)
        rw [h0]; exact Submodule.zero_mem _
    · intro h; apply hy0
      simpa using congrArg (fun z : ⨁ i, M i => z i) h

/-- The inclusion `⨁ (T_i)_{∼ρ} → ⨁ M_i`. -/
noncomputable def incl (ρ : ℂ) : (⨁ i, (T i).maxGenEigenspace ρ) →ₗ[ℂ] ⨁ i, M i :=
  DirectSum.lmap fun i => ((T i).maxGenEigenspace ρ).subtype

omit [DecidableEq ι] in
lemma incl_injective (ρ : ℂ) : Function.Injective (incl T ρ) := by
  intro x y h
  ext i
  have := congrArg (fun z : ⨁ i, M i => z i) h
  simpa [incl, DirectSum.lmap_apply] using this

lemma range_incl (ρ : ℂ) :
    LinearMap.range (incl T ρ) = (diag T).maxGenEigenspace ρ := by
  ext x
  rw [mem_maxGenEigenspace_diag_iff]
  constructor
  · rintro ⟨y, rfl⟩ i
    simp only [incl, DirectSum.lmap_apply]
    exact (y i).2
  · intro h
    classical
    refine ⟨∑ i ∈ x.support, DirectSum.lof ℂ ι (fun i => (T i).maxGenEigenspace ρ) i ⟨x i, h i⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← DirectSum.sum_support_of x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [incl, DirectSum.lof_eq_of]

/-- `(⨁ T_i)_{∼ρ} ≃ ⨁ (T_i)_{∼ρ}`. -/
noncomputable def maxGenEquiv (ρ : ℂ) :
    (⨁ i, (T i).maxGenEigenspace ρ) ≃ₗ[ℂ] (diag T).maxGenEigenspace ρ :=
  (LinearEquiv.ofInjective _ (incl_injective T ρ)).trans
    (LinearEquiv.ofEq _ _ (range_incl T ρ))

/-- The multiplicity of `⨁ T_i` at `ρ`, as a cardinal, is the sum of the multiplicities. -/
theorem rank_maxGenEigenspace_diag (ρ : ℂ) :
    Module.rank ℂ ((diag T).maxGenEigenspace ρ) =
      Cardinal.sum fun i => Module.rank ℂ ((T i).maxGenEigenspace ρ) := by
  rw [← (maxGenEquiv T ρ).rank_eq, rank_directSum]


/-- If `ρ` is a generalized eigenvalue of `T_i` only for `i = i₀`, then `(⨁ T_i)_{∼ρ} ≃ (T_{i₀})_{∼ρ}`
by taking the `i₀`-component. -/
noncomputable def maxGenEquivSingle (ρ : ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → (T i).maxGenEigenspace ρ = ⊥) :
    (diag T).maxGenEigenspace ρ ≃ₗ[ℂ] (T i₀).maxGenEigenspace ρ :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict ((T i₀).maxGenEigenspace ρ)
      ((DirectSum.component ℂ ι M i₀).comp ((diag T).maxGenEigenspace ρ).subtype)
      fun x => by
        rw [LinearMap.comp_apply, Submodule.subtype_apply, ← DirectSum.apply_eq_component]
        exact (mem_maxGenEigenspace_diag_iff T ρ x).1 x.2 i₀)
    (by
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have hxy' : x i₀ = y i₀ := by
          rw [DirectSum.apply_eq_component ℂ, DirectSum.apply_eq_component ℂ]
          simpa using congrArg Subtype.val hxy
        ext i
        by_cases hi : i = i₀
        · subst hi; exact hxy'
        · have hx' := (mem_maxGenEigenspace_diag_iff T ρ x).1 hx i
          have hy' := (mem_maxGenEigenspace_diag_iff T ρ y).1 hy i
          rw [h i hi, Submodule.mem_bot] at hx' hy'
          rw [hx', hy']
      · rintro ⟨y, hy⟩
        refine ⟨⟨DirectSum.lof ℂ ι M i₀ y, (mem_maxGenEigenspace_diag_iff T ρ _).2 fun i => ?_⟩, ?_⟩
        · by_cases hi : i = i₀
          · subst hi; simpa using hy
          · rw [h i hi, Submodule.mem_bot, DirectSum.lof_eq_of]
            exact DirectSum.of_eq_of_ne _ _ _ (by tauto)
        · ext; simp)

end DiagSum


section VQ

/-- **`def:R7-local`.** `V_𝒬 = ⨁_{p ∈ 𝒬} V_p`, the algebraic direct sum of the local spectral
cores `V_p = 𝟙_p` (`unitSpace p`). -/
abbrev VQ (𝒬 : Set ℕ) := ⨁ p : 𝒬, unitSpace ((p : ℕ) : ℝ)

/-- **`def:R7-local`.** `Θ_𝒬 = ⨁_p Θ_p`. -/
noncomputable def thetaQ (𝒬 : Set ℕ) :
    @Module.End ℂ (VQ 𝒬) _ AddCommGroup.toAddCommMonoid _ :=
  diag fun p : 𝒬 => unitTheta ((p : ℕ) : ℝ)

variable {𝒬 : Set ℕ} (h𝒬 : ∀ p ∈ 𝒬, p.Prime)
include h𝒬

lemma one_lt (p : 𝒬) : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast (h𝒬 p p.2).one_lt

/-- **`prop:R7` (i)**: `spec Θ_𝒬 = ⋃_{p ∈ 𝒬} (2πi / log p) ℤ`. -/
theorem mem_spec_thetaQ (ρ : ℂ) :
    ρ ∈ spec (V := VQ 𝒬) (thetaQ 𝒬) ↔ ∃ p ∈ 𝒬, ∃ n : ℤ, ρ = shift p n := by
  unfold thetaQ
  rw [spec_diag]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, p.2, (mem_spec_unit_iff (one_lt h𝒬 p) ρ).1 hp⟩
  · rintro ⟨p, hp, hρ⟩
    exact ⟨⟨p, hp⟩, (mem_spec_unit_iff (one_lt h𝒬 ⟨p, hp⟩) ρ).2 hρ⟩

/-- **`prop:R7` (i)**: `spec Θ_𝒬 ⊂ iℝ`. -/
theorem re_eq_zero_of_mem_spec {ρ : ℂ} (hρ : ρ ∈ spec (V := VQ 𝒬) (thetaQ 𝒬)) : ρ.re = 0 := by
  obtain ⟨p, hp, n, rfl⟩ := (mem_spec_thetaQ h𝒬 ρ).1 hρ
  exact (spec_local p (h𝒬 p hp)).2.1 _ ((spec_local p (h𝒬 p hp)).1 _ |>.2 ⟨n, rfl⟩)

lemma rank_local_zero (p : 𝒬) :
    Module.rank ℂ ((unitTheta ((p : ℕ) : ℝ)).maxGenEigenspace 0) = 1 := by
  have := (spectralCore_theta (1 : Module.End ℂ ℂ) (one_lt h𝒬 p)).finiteDimensional 0
  rw [← Module.finrank_eq_rank]
  have := mult_unit (one_lt h𝒬 p) 0
  simp only [shift, Int.cast_zero, mul_zero, zero_div] at this
  rw [mult] at this
  simp [this]

/-- **`prop:R7` (i)**: the eigenvalue `0` of `Θ_𝒬` has multiplicity `#𝒬` (a cardinal, so that the
statement also covers infinite `𝒬`). -/
theorem rank_maxGenEigenspace_zero :
    Module.rank ℂ (Module.End.maxGenEigenspace (M := VQ 𝒬) (thetaQ 𝒬) (0 : ℂ)) = Cardinal.mk 𝒬 := by
  unfold thetaQ
  rw [rank_maxGenEigenspace_diag]
  simp only [rank_local_zero h𝒬, Cardinal.sum_const', mul_one]

/-- **`prop:R7` (i)**: for finite `𝒬`, `m(0) = #𝒬`. -/
theorem mult_zero [Fintype 𝒬] : mult (V := VQ 𝒬) (thetaQ 𝒬) 0 = Fintype.card 𝒬 := by
  rw [mult, Module.finrank_eq_of_rank_eq (n := Fintype.card 𝒬)]
  rw [rank_maxGenEigenspace_zero h𝒬, Cardinal.mk_fintype]

/-- **`prop:R7` (i)**: every nonzero eigenvalue of `Θ_𝒬` is simple. -/
theorem mult_eq_one {p : ℕ} (hp : p ∈ 𝒬) {n : ℤ} (hn : n ≠ 0) :
    mult (V := VQ 𝒬) (thetaQ 𝒬) (shift p n) = 1 := by
  have hq := one_lt h𝒬 ⟨p, hp⟩
  unfold thetaQ
  rw [mult, (maxGenEquivSingle _ (shift p n) ⟨p, hp⟩ fun p' hne => ?_).finrank_eq]
  · exact mult_unit hq n
  · by_contra hb
    have hmem : shift p n ∈ spec (unitTheta ((p' : ℕ) : ℝ)) := hb
    obtain ⟨m, hm⟩ := (mem_spec_unit_iff (one_lt h𝒬 p') _).1 hmem
    have hne' : p ≠ (p' : ℕ) := fun h => hne (Subtype.ext h.symm)
    exact hn ((shift_eq_shift_iff (h𝒬 p hp) (h𝒬 p' p'.2) hne' n m).1 hm).1

/-- **`prop:R7` (ii)**: if `𝒬` is infinite, `(V_𝒬, Θ_𝒬)` is not a spectral core: the generalized
eigenspace at `0` is infinite-dimensional. -/
theorem not_spectralCore (hinf : 𝒬.Infinite) : ¬ SpectralCore (V := VQ 𝒬) (thetaQ 𝒬) := by
  intro hc
  have := hc.finiteDimensional 0
  have h := rank_maxGenEigenspace_zero h𝒬
  have : Cardinal.mk 𝒬 < Cardinal.aleph0 := h ▸ Module.rank_lt_aleph0 ℂ _
  exact hinf (Cardinal.lt_aleph0_iff_set_finite.1 this)

/-- **`prop:R7` (iii)** for `V_𝒬`: no eigenvalue of `Θ_𝒬` is a zero of `ξ`. -/
theorem completedXi_ne_zero_of_mem_specQ {ρ : ℂ} (hρ : ρ ∈ spec (V := VQ 𝒬) (thetaQ 𝒬)) :
    completedXi ρ ≠ 0 :=
  completedXi_ne_zero_of_re_eq_zero (re_eq_zero_of_mem_spec h𝒬 hρ)

end VQ

end WeilRH.R7
