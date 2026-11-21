/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.KunFq

/-!
# Products of periodic units (`prop:kun-orbits`)

The `p`-periodic unit `𝟙_p = ⨁_{n ∈ ℤ} ℂ v^n`, `Θ v^n = (2πin / log p) v^n` (`def:unit` (b)), is
the logarithmic suspension of `(ℂ, 1)` (`prop:unit`): `SuspSpace 1 p` has one copy of `ℂ` at each
`ρ` with `p^ρ = 1`, that is at each `ρ = 2πin / log p`, and `Θ = ρ` there because `N = log 1 = 0`.
We take this suspension as the definition of `𝟙_p` (`unitSpace`, `unitTheta`).

## Main results

* `KunOrbits.mem_spec_unit_iff`, `KunOrbits.mult_unit`: `spec 𝟙_q = {2πik / log q}`, each simple.
* `KunOrbits.kun_orbits_same` (`prop:kun-orbits` (i)): every eigenvalue `2πik / log p` of
  `𝟙_p ⊗ 𝟙_p` has infinite multiplicity.
* `KunOrbits.kun_orbits_dense` (`prop:kun-orbits` (ii)): for primes `p ≠ p'`, the spectrum of
  `𝟙_p ⊗ 𝟙_{p'}` is `{2πi(m / log p + n / log p')}`, the labelling by `(m, n)` is injective, each
  eigenvalue is simple, and the eigenvalues are dense in `iℝ`.
* `KunOrbits.card_cone`: `#{(m, n) : m + n = k, mn ≥ 0} = |k| + 1`.
* `KunOrbits.kurokawaCone` (`def:kurokawa-cone`) and `KunOrbits.kun_orbits_cone`
  (`prop:kun-orbits` (iii)): on the Kurokawa cone of `𝟙_p ⊗ 𝟙_p` the eigenvalue `2πik / log p` has
  multiplicity `|k| + 1`. `KunOrbits.finrank_maxGenEigenspace_restrict` identifies the part of a
  generalized eigenspace in a `Θ`-stable subspace with the generalized eigenspace of the restriction.
* `KunOrbits.kurokawaCone_inf_antidiag`, `KunOrbits.finiteDimensional_kurokawaCone_inf_antidiag`
  (`prop:kun-cone` (ii)): for a spectral core, the cone meets `⨁_ρ V_ρ ⊗ V_{1-ρ}` in the blocks with
  `ρ` real, which is finite-dimensional when the spectrum has finitely many real points.
-/

open Module Complex TensorProduct

namespace WeilRH.KunOrbits

open WeilRH.Spectral WeilRH.Suspension WeilRH.KunFq

/-- The `q`-periodic unit `𝟙_q` of `def:unit` (b), as the suspension of `(ℂ, 1)` (`prop:unit`). -/
abbrev unitSpace (q : ℝ) := SuspSpace (1 : Module.End ℂ ℂ) q

/-- The generator `Θ` of `𝟙_q`. -/
noncomputable abbrev unitTheta (q : ℝ) : Module.End ℂ (unitSpace q) := theta 1 q

lemma hasEigenvalue_one_iff (μ : ℂ) : (1 : Module.End ℂ ℂ).HasEigenvalue μ ↔ μ = 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have := hx.apply_eq_smul
    simp only [Module.End.one_apply] at this
    have hx0 : x ≠ 0 := hx.2
    have : (μ - 1) * x = 0 := by rw [sub_mul, ← smul_eq_mul, ← this]; simp
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hx0
  · rintro rfl
    rw [Module.End.hasEigenvalue_iff]
    intro h
    have : (1 : ℂ) ∈ (1 : Module.End ℂ ℂ).eigenspace 1 := by simp
    rw [h] at this
    simp at this

lemma qpow_eq_one_iff {q : ℝ} (hq : 1 < q) (ρ : ℂ) : qpow q ρ = 1 ↔ ∃ k : ℤ, ρ = shift q k := by
  have hL : (Real.log q : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hq).ne'
  rw [qpow, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [shift]
    field_simp
    linear_combination hn
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [shift]
    field_simp

/-- `spec 𝟙_q = {2πik / log q : k ∈ ℤ}`. -/
theorem mem_spec_unit_iff {q : ℝ} (hq : 1 < q) (ρ : ℂ) :
    ρ ∈ spec (unitTheta q) ↔ ∃ k : ℤ, ρ = shift q k := by
  rw [spec_theta]
  show (1 : Module.End ℂ ℂ).HasEigenvalue (qpow q ρ) ↔ _
  rw [hasEigenvalue_one_iff, qpow_eq_one_iff hq]

/-- Each eigenvalue of `𝟙_q` is simple. -/
theorem mult_unit {q : ℝ} (hq : 1 < q) (k : ℤ) : mult (unitTheta q) (shift q k) = 1 := by
  rw [mult_theta_eq]
  have hk : qpow q (shift q k) = 1 := (qpow_eq_one_iff hq _).2 ⟨k, rfl⟩
  rw [hk]
  have hne : (1 : Module.End ℂ ℂ).maxGenEigenspace 1 ≠ ⊥ := by
    intro h
    have : (1 : Module.End ℂ ℂ).HasEigenvalue 1 := (hasEigenvalue_one_iff 1).2 rfl
    exact this (eq_bot_iff.2 ((Module.End.eigenspace_le_maxGenEigenspace).trans h.le))
  have h1 : finrank ℂ ((1 : Module.End ℂ ℂ).maxGenEigenspace 1) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  have h2 : 0 < finrank ℂ ((1 : Module.End ℂ ℂ).maxGenEigenspace 1) :=
    Nat.pos_of_ne_zero (fun h => hne (Submodule.finrank_eq_zero.1 h))
  omega

lemma shift_eq (q : ℝ) (k : ℤ) :
    shift q k = ((2 * Real.pi * k / Real.log q : ℝ) : ℂ) * I := by
  simp only [shift]; push_cast; ring

lemma mem_spec_shift {q : ℝ} (hq : 1 < q) (k : ℤ) : shift q k ∈ spec (unitTheta q) :=
  (mem_spec_unit_iff hq _).2 ⟨k, rfl⟩

/-- **`prop:kun-orbits` (i).** For a prime `p`, every eigenvalue `2πik / log p` of `𝟙_p ⊗ 𝟙_p`
has infinite multiplicity: its generalized eigenspace is nonzero and not finite-dimensional. -/
theorem kun_orbits_same {p : ℕ} (hp : p.Prime) (k : ℤ) :
    Module.End.maxGenEigenspace (R := ℂ) (M := unitSpace p ⊗[ℂ] unitSpace p)
        (tensorSum (unitTheta p) (unitTheta p)) (shift p k) ≠ ⊥ ∧
      ¬ Module.Finite ℂ (Module.End.maxGenEigenspace (R := ℂ)
        (M := unitSpace p ⊗[ℂ] unitSpace p) (tensorSum (unitTheta p) (unitTheta p)) (shift p k)) := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hne : Module.End.maxGenEigenspace (R := ℂ) (M := unitSpace p ⊗[ℂ] unitSpace p)
      (tensorSum (unitTheta p) (unitTheta p)) (shift p k) ≠ ⊥ := by
    have hS := spectralCore_theta (1 : Module.End ℂ ℂ) hq
    have := hS.finiteDimensional (shift p k)
    have := hS.finiteDimensional 0
    have h0mem : (0 : ℂ) ∈ spec (unitTheta p) := (mem_spec_unit_iff hq 0).2 ⟨0, by simp [shift]⟩
    have hb := block_ne_bot (unitTheta p) (unitTheta p) (mem_spec_shift hq k) h0mem
    have hle := block_le (unitTheta p) (unitTheta p) (shift p k) 0
    rw [add_zero] at hle
    intro h
    exact hb (eq_bot_iff.2 (hle.trans h.le))
  have key := maxGenEigenspace_eq_bot_or_infinite (V := ℂ) (W := ℂ) hq (1 : Module.End ℂ ℂ)
    (1 : Module.End ℂ ℂ) (shift p k)
  exact ⟨hne, key.resolve_left hne⟩

/-- Unique factorization in the form used for `prop:kun-orbits` (ii) and `prop:kun-torus` (iii):
for distinct primes, `x log p' = y log p` with `x, y ∈ ℤ` forces `x = y = 0`. -/
lemma int_mul_log_eq {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') {x y : ℤ}
    (h : (x : ℝ) * Real.log p' = y * Real.log p) : x = 0 ∧ y = 0 := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hl' : 0 < Real.log p' := Real.log_pos (by exact_mod_cast hp'.one_lt)
  -- pass to absolute values
  have habs : (x.natAbs : ℝ) * Real.log p' = y.natAbs * Real.log p := by
    have := congrArg abs h
    rw [abs_mul, abs_mul, abs_of_pos hl, abs_of_pos hl'] at this
    simpa [Nat.cast_natAbs, Int.cast_abs] using this
  have hpow : (p' : ℝ) ^ x.natAbs = (p : ℝ) ^ y.natAbs := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp0' : (0 : ℝ) < p' := by exact_mod_cast hp'.pos
    apply Real.log_injOn_pos (pow_pos hp0' _) (pow_pos hp0 _)
    rw [Real.log_pow, Real.log_pow, habs]
  have hpowN : p' ^ x.natAbs = p ^ y.natAbs := by exact_mod_cast hpow
  have hy : y.natAbs = 0 := by
    by_contra hy
    have hd : p ∣ p' ^ x.natAbs := hpowN ▸ dvd_pow_self p hy
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hd))
  have hx : x.natAbs = 0 := by
    rw [hy, Nat.cast_zero, zero_mul] at habs
    rcases mul_eq_zero.1 habs with h | h
    · exact_mod_cast h
    · exact absurd h hl'.ne'
  exact ⟨Int.natAbs_eq_zero.1 hx, Int.natAbs_eq_zero.1 hy⟩

/-- Distinct `(m, n)` give distinct eigenvalues `2πi(m / log p + n / log p')`. -/
lemma shift_add_shift_injective {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') :
    Function.Injective fun mn : ℤ × ℤ => shift p mn.1 + shift p' mn.2 := by
  rintro ⟨m, n⟩ ⟨a, b⟩ h
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hl' : Real.log p' ≠ 0 := (Real.log_pos (by exact_mod_cast hp'.one_lt)).ne'
  simp only [shift_eq, ← add_mul, ← ofReal_add] at h
  have hr0 := ofReal_injective (mul_right_cancel₀ I_ne_zero h)
  field_simp at hr0
  have hr : ((m - a : ℤ) : ℝ) * Real.log p' = ((b - n : ℤ) : ℝ) * Real.log p := by
    push_cast
    linear_combination hr0
  obtain ⟨h1, h2⟩ := int_mul_log_eq hp hp' hne hr
  simp only [Prod.mk.injEq]
  omega

/-- The pairs of `𝟙_p ⊗ 𝟙_{p'}` over `2πi(m / log p + n / log p')` are only `(m, n)` itself. -/
lemma pairs_unit {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') (m n : ℤ) :
    pairs (unitTheta p) (unitTheta p') (shift p m + shift p' n) = {(shift p m, shift p' n)} := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq' : (1 : ℝ) < p' := by exact_mod_cast hp'.one_lt
  ext ⟨ρ, ρ'⟩
  simp only [pairs, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hs, h1, h2⟩
    obtain ⟨a, rfl⟩ := (mem_spec_unit_iff hq _).1 h1
    obtain ⟨b, rfl⟩ := (mem_spec_unit_iff hq' _).1 h2
    have := shift_add_shift_injective hp hp' hne (a₁ := (a, b)) (a₂ := (m, n)) hs
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, mem_spec_shift hq m, mem_spec_shift hq' n⟩

/-- **`prop:kun-orbits` (ii).** For distinct primes `p ≠ p'`, the spectrum of `𝟙_p ⊗ 𝟙_{p'}` is
`{2πi(m / log p + n / log p') : m, n ∈ ℤ}`, distinct `(m, n)` give distinct eigenvalues, each
eigenvalue is simple, and the eigenvalues lie on `iℝ` with imaginary parts dense in `ℝ`. -/
theorem kun_orbits_dense {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') :
    (∀ lam : ℂ, lam ∈ spec (tensorSum (unitTheta p) (unitTheta p')) ↔
        ∃ m n : ℤ, lam = shift p m + shift p' n) ∧
      Function.Injective (fun mn : ℤ × ℤ => shift p mn.1 + shift p' mn.2) ∧
      (∀ m n : ℤ, Module.Finite ℂ (Module.End.maxGenEigenspace (R := ℂ)
          (M := unitSpace p ⊗[ℂ] unitSpace p') (tensorSum (unitTheta p) (unitTheta p'))
          (shift p m + shift p' n)) ∧
        mult (tensorSum (unitTheta p) (unitTheta p')) (shift p m + shift p' n) = 1) ∧
      (∀ m n : ℤ, (shift p m + shift p' n).re = 0) ∧
      Dense (Set.range fun mn : ℤ × ℤ => (shift p mn.1 + shift p' mn.2).im) := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq' : (1 : ℝ) < p' := by exact_mod_cast hp'.one_lt
  have hS := spectralCore_theta (1 : Module.End ℂ ℂ) hq
  have hS' := spectralCore_theta (1 : Module.End ℂ ℂ) hq'
  have hmult : ∀ m n : ℤ, Module.Finite ℂ (Module.End.maxGenEigenspace (R := ℂ)
      (M := unitSpace p ⊗[ℂ] unitSpace p') (tensorSum (unitTheta p) (unitTheta p'))
      (shift p m + shift p' n)) ∧
      mult (tensorSum (unitTheta p) (unitTheta p')) (shift p m + shift p' n) = 1 := by
    intro m n
    have hfin : (pairs (unitTheta p) (unitTheta p') (shift p m + shift p' n)).Finite := by
      rw [pairs_unit hp hp' hne]; exact Set.finite_singleton _
    obtain ⟨hfd, hrk⟩ := finrank_maxGenEigenspace_tensorSum hS hS' _ hfin
    refine ⟨hfd, ?_⟩
    rw [mult, hrk]
    have ht : hfin.toFinset = {(shift p m, shift p' n)} := by
      ext x; simp [pairs_unit hp hp' hne]
    rw [ht, Finset.sum_singleton, mult_unit hq, mult_unit hq']
  refine ⟨fun lam => ⟨fun h => ?_, ?_⟩, shift_add_shift_injective hp hp' hne, hmult, ?_, ?_⟩
  · -- a nonzero generalized eigenspace has a pair
    by_contra hall
    push Not at hall
    apply h
    rw [maxGenEigenspace_tensorSum_eq_pairs _ _ hS.iSup_eq_top hS'.iSup_eq_top]
    refine iSup₂_eq_bot.2 fun x hx => ?_
    obtain ⟨hs, h1, h2⟩ := hx
    obtain ⟨a, ha⟩ := (mem_spec_unit_iff hq _).1 h1
    obtain ⟨b, hb⟩ := (mem_spec_unit_iff hq' _).1 h2
    exact absurd (by rw [← hs, ha, hb]) (hall a b)
  · rintro ⟨m, n, rfl⟩ hbot
    have h1 := (hmult m n).2
    rw [mult, hbot, finrank_bot] at h1
    exact zero_ne_one h1
  · intro m n
    rw [shift_eq, shift_eq, ← add_mul, ← ofReal_add]
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  · -- the imaginary parts form the group `ℤ a + ℤ b`, `a = 2π / log p`, `b = 2π / log p'`
    set a : ℝ := 2 * Real.pi / Real.log p
    set b : ℝ := 2 * Real.pi / Real.log p'
    have hl : 0 < Real.log p := Real.log_pos hq
    have hl' : 0 < Real.log p' := Real.log_pos hq'
    have him : ∀ mn : ℤ × ℤ, (shift p mn.1 + shift p' mn.2).im = mn.1 • a + mn.2 • b := by
      rintro ⟨m, n⟩
      simp only [shift_eq, ← add_mul, ← ofReal_add, mul_I_im, ofReal_re, a, b, zsmul_eq_mul]
      ring
    have hrange : (Set.range fun mn : ℤ × ℤ => (shift p mn.1 + shift p' mn.2).im) =
        (AddSubgroup.closure {a, b} : Set ℝ) := by
      ext x
      simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_closure_pair, him]
      constructor
      · rintro ⟨⟨m, n⟩, rfl⟩; exact ⟨m, n, rfl⟩
      · rintro ⟨m, n, rfl⟩; exact ⟨(m, n), rfl⟩
    rw [hrange, dense_addSubgroupClosure_pair_iff]
    -- `a / b = log p' / log p` is irrational
    have hab : a / b = Real.log p' / Real.log p := by
      simp only [a, b]; field_simp
    rw [hab, irrational_iff_ne_rational]
    intro x y hy hxy
    have hyr : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have : (y : ℝ) * Real.log p' = x * Real.log p := by
      rw [div_eq_div_iff hl.ne' hyr] at hxy; linarith
    exact hy (int_mul_log_eq hp hp' hne this).1

/-- The counting step of **`prop:kun-orbits` (iii)**. The Kurokawa cone of `𝟙_p ⊗ 𝟙_p` is spanned by the
`v^m ⊗ v^n` with `mn ≥ 0`, on which `Θ = 2πi(m + n) / log p`; the multiplicity of
`2πik / log p` there is `#{(m, n) ∈ ℤ² : m + n = k, mn ≥ 0} = |k| + 1`. -/
theorem card_cone (k : ℤ) :
    {mn : ℤ × ℤ | mn.1 + mn.2 = k ∧ 0 ≤ mn.1 * mn.2}.ncard = k.natAbs + 1 := by
  have hset : {mn : ℤ × ℤ | mn.1 + mn.2 = k ∧ 0 ≤ mn.1 * mn.2} =
      (fun m : ℤ => (m, k - m)) '' (Finset.Icc (min 0 k) (max 0 k) : Set ℤ) := by
    ext ⟨m, n⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_Icc, Set.mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨hs, hmn⟩
      refine ⟨m, ?_, rfl, by omega⟩
      subst hs
      simp only [min_le_iff, le_max_iff]
      rcases lt_trichotomy m 0 with hm | hm | hm
      · have : n ≤ 0 := nonpos_of_mul_nonneg_right hmn hm
        omega
      · omega
      · have : 0 ≤ n := nonneg_of_mul_nonneg_right hmn hm
        omega
    · rintro ⟨m', ⟨h1, h2⟩, rfl, rfl⟩
      refine ⟨by ring, ?_⟩
      simp only [min_le_iff, le_max_iff] at h1 h2
      rcases le_total 0 k with hk | hk
      · have : 0 ≤ m' := by omega
        have : 0 ≤ k - m' := by omega
        positivity
      · have : m' ≤ 0 := by omega
        have : k - m' ≤ 0 := by omega
        nlinarith
  rw [hset, Set.ncard_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h),
    Set.ncard_coe_finset, Int.card_Icc]
  rcases le_total 0 k with hk | hk
  · rw [min_eq_left hk, max_eq_right hk]; omega
  · rw [min_eq_right hk, max_eq_left hk]; omega


universe u

/-- In an internal direct sum, the meet of two partial sums is the partial sum over the
intersection of the index sets. -/
lemma biSup_inf_biSup_of_isInternal {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    {A : ι → Submodule ℂ M} (h : DirectSum.IsInternal A) (S T : Set ι) :
    (⨆ i ∈ S, A i) ⊓ (⨆ i ∈ T, A i) = ⨆ i ∈ S ∩ T, A i := by
  classical
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h
  have hzero : ∀ (U : Set ι) {x : M}, x ∈ ⨆ i ∈ U, A i → ∀ j ∉ U, e.symm x j = 0 := by
    intro U x hx j hj
    rw [iSup_subtype'] at hx
    induction hx using Submodule.iSup_induction' with
    | mem i y hy =>
      exact h.ofBijective_coeLinearMap_of_mem_ne (fun hij : (i : ι) = j => hj (by rw [← hij]; exact i.2)) hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, DirectSum.add_apply, hy, hz, add_zero]
  apply le_antisymm
  · rintro x ⟨hS, hT⟩
    have hx : x = DirectSum.coeLinearMap A (e.symm x) :=
      (e.apply_symm_apply x).symm
    rw [hx, ← DirectSum.sum_support_of (e.symm x), map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [DirectSum.coeLinearMap_of]
    have hi' : e.symm x i ≠ 0 := DFinsupp.mem_support_iff.1 hi
    have hiS : i ∈ S := by by_contra hn; exact hi' (hzero S hS i hn)
    have hiT : i ∈ T := by by_contra hn; exact hi' (hzero T hT i hn)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem ⟨hiS, hiT⟩ (e.symm x i).2)
  · exact le_inf (biSup_mono fun _ h => h.1) (biSup_mono fun _ h => h.2)

/-- **`def:kurokawa-cone`.** The Kurokawa cone of `V ⊗ V`: the sum of the blocks
`V_{Θ∼ρ} ⊗ V_{Θ∼ρ'}` over the pairs with `Im ρ · Im ρ' ≥ 0`. -/
noncomputable def kurokawaCone {V : Type*} [AddCommGroup V] [Module ℂ V] (Θ : Module.End ℂ V) :
    Submodule ℂ (V ⊗[ℂ] V) :=
  ⨆ p ∈ {p : ℂ × ℂ | 0 ≤ p.1.im * p.2.im}, block Θ Θ p.1 p.2

/-- The Kurokawa cone is `Θ`-stable. -/
lemma mapsTo_kurokawaCone {V : Type*} [AddCommGroup V] [Module ℂ V] (Θ : Module.End ℂ V) :
    ∀ x ∈ kurokawaCone Θ, tensorSum Θ Θ x ∈ kurokawaCone Θ := by
  intro x hx
  rw [kurokawaCone, iSup_subtype'] at hx ⊢
  induction hx using Submodule.iSup_induction' with
  | mem i y hy => exact Submodule.mem_iSup_of_mem i (mapsTo_block Θ Θ _ _ hy)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz

lemma shift_add (q : ℝ) (a b : ℤ) : shift q a + shift q b = shift q (a + b) := by
  simp only [shift]; push_cast; ring

lemma im_shift (q : ℝ) (k : ℤ) : (shift q k).im = 2 * Real.pi * k / Real.log q := by
  rw [shift_eq]; simp

/-- The dimension of a finite sum of blocks of two spectral cores. -/
lemma finrank_biSup_block {V W : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (hV : SpectralCore ΘV)
    (hW : SpectralCore ΘW) (S : Finset (ℂ × ℂ)) :
    FiniteDimensional ℂ (⨆ p ∈ (S : Set (ℂ × ℂ)), block ΘV ΘW p.1 p.2 :
        Submodule ℂ (V ⊗[ℂ] W)) ∧
      Module.finrank ℂ (⨆ p ∈ (S : Set (ℂ × ℂ)), block ΘV ΘW p.1 p.2 :
        Submodule ℂ (V ⊗[ℂ] W)) =
        ∑ p ∈ S, mult ΘV p.1 * mult ΘW p.2 := by
  classical
  have := hV.finiteDimensional; have := hW.finiteDimensional
  let A : ℂ × ℂ → Submodule ℂ (V ⊗[ℂ] W) := fun p => block ΘV ΘW p.1 p.2
  have hint := DirectSum.isInternal_biSup_submodule_of_iSupIndep (A := A) (S : Set (ℂ × ℂ))
    ((iSupIndep_block ΘV ΘW).comp Subtype.val_injective)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint
  have hfd : ∀ p : (S : Set (ℂ × ℂ)), FiniteDimensional ℂ
      ((A p).comap (⨆ i ∈ (S : Set (ℂ × ℂ)), A i).subtype) := fun p =>
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (le_biSup A p.2)).symm
  have hrk : ∀ p : (S : Set (ℂ × ℂ)), Module.finrank ℂ
      ((A p).comap (⨆ i ∈ (S : Set (ℂ × ℂ)), A i).subtype) = mult ΘV p.1.1 * mult ΘW p.1.2 := by
    intro p
    rw [(Submodule.comapSubtypeEquivOfLe (le_biSup A p.2)).finrank_eq,
      ← (blockEquiv ΘV ΘW p.1.1 p.1.2).finrank_eq, Module.finrank_tensorProduct]
    rfl
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_directSum]
  simp only [hrk]
  exact Finset.sum_coe_sort S (fun p => mult ΘV p.1 * mult ΘW p.2)

/-- The pairs of `𝟙_p ⊗ 𝟙_p` in the Kurokawa cone over `2πik / log p` are the
`(2πim / log p, 2πin / log p)` with `m + n = k`, `mn ≥ 0`. -/
lemma cone_pairs {p : ℕ} (hp : p.Prime) (k : ℤ) :
    {x : ℂ × ℂ | 0 ≤ x.1.im * x.2.im} ∩ pairs (unitTheta p) (unitTheta p) (shift p k) =
      (fun mn : ℤ × ℤ => (shift p mn.1, shift p mn.2)) ''
        {mn : ℤ × ℤ | mn.1 + mn.2 = k ∧ 0 ≤ mn.1 * mn.2} := by
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 < Real.log p := Real.log_pos hq
  have him : ∀ a b : ℤ, (shift p a).im * (shift p b).im =
      (2 * Real.pi / Real.log p) ^ 2 * ((a * b : ℤ) : ℝ) := by
    intro a b; rw [im_shift, im_shift]; push_cast; ring
  have hc : 0 < (2 * Real.pi / Real.log p) ^ 2 := by positivity
  ext ⟨ρ, ρ'⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, pairs, Set.mem_image, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hc0, hs, h1, h2⟩
    obtain ⟨a, rfl⟩ := (mem_spec_unit_iff hq _).1 h1
    obtain ⟨b, rfl⟩ := (mem_spec_unit_iff hq _).1 h2
    rw [shift_add] at hs
    refine ⟨a, b, ⟨shift_injective hq hs, ?_⟩, rfl, rfl⟩
    rw [him] at hc0
    exact_mod_cast (mul_nonneg_iff_of_pos_left hc).1 hc0
  · rintro ⟨a, b, ⟨hs, hab⟩, rfl, rfl⟩
    refine ⟨?_, by rw [shift_add, hs], mem_spec_shift hq a, mem_spec_shift hq b⟩
    rw [him]
    exact mul_nonneg hc.le (by exact_mod_cast hab)

/-- For a `Θ`-stable subspace `P`, the generalized `μ`-eigenspace of `Θ|_P` has the dimension of
`P ⊓ V_{Θ∼μ}`; so the multiplicity of `μ` on `P` is `finrank (P ⊓ V_{Θ∼μ})`. -/
lemma finrank_maxGenEigenspace_restrict {M : Type*} [AddCommGroup M] [Module ℂ M]
    (Θ : Module.End ℂ M) (P : Submodule ℂ M) (hP : ∀ x ∈ P, Θ x ∈ P) (μ : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (Θ.restrict hP) μ) =
      Module.finrank ℂ (P ⊓ Θ.maxGenEigenspace μ : Submodule ℂ M) := by
  rw [Submodule.inf_genEigenspace Θ P hP]
  exact (Submodule.equivMapOfInjective _ P.injective_subtype _).finrank_eq

/-- The part of `(V ⊗ V)_{Θ∼λ}` in the Kurokawa cone of a spectral core: when the cone pairs over
`λ` form a finite set `T`, it is finite-dimensional of dimension `Σ_{(ρ,ρ') ∈ T} m(ρ) m(ρ')`. -/
theorem finrank_cone_inf {V : Type u} [AddCommGroup V] [Module ℂ V] {Θ : Module.End ℂ V}
    (hS : SpectralCore Θ) (lam : ℂ) (T : Finset (ℂ × ℂ))
    (hT : {x : ℂ × ℂ | 0 ≤ x.1.im * x.2.im} ∩ pairs Θ Θ lam = T) :
    Module.Finite ℂ (kurokawaCone Θ ⊓ (tensorSum Θ Θ).maxGenEigenspace lam :
        Submodule ℂ (V ⊗[ℂ] V)) ∧
      Module.finrank ℂ (kurokawaCone Θ ⊓ (tensorSum Θ Θ).maxGenEigenspace lam :
        Submodule ℂ (V ⊗[ℂ] V)) = ∑ x ∈ T, mult Θ x.1 * mult Θ x.2 := by
  classical
  have hint := isInternal_block Θ Θ hS.iSup_eq_top hS.iSup_eq_top
  have hmeet : kurokawaCone Θ ⊓ (tensorSum Θ Θ).maxGenEigenspace lam =
      ⨆ x ∈ (T : Set (ℂ × ℂ)), block Θ Θ x.1 x.2 := by
    rw [kurokawaCone, maxGenEigenspace_tensorSum_eq_pairs Θ Θ hS.iSup_eq_top hS.iSup_eq_top,
      biSup_inf_biSup_of_isInternal hint, hT]
  obtain ⟨hfd, hrk⟩ := finrank_biSup_block hS hS T
  rw [hmeet]
  exact ⟨hfd, hrk⟩

/-- **`prop:kun-orbits` (iii).** On the Kurokawa cone of `𝟙_p ⊗ 𝟙_p` the eigenvalue
`2πik / log p` has multiplicity `|k| + 1`: the part of the generalized eigenspace lying in the
cone is finite-dimensional of dimension `|k| + 1` (by `finrank_maxGenEigenspace_restrict` this is
the generalized eigenspace of the generator restricted to the `Θ`-stable cone). -/
theorem kun_orbits_cone {p : ℕ} (hp : p.Prime) (k : ℤ) :
    Module.Finite ℂ (kurokawaCone (unitTheta p) ⊓ Module.End.maxGenEigenspace (R := ℂ)
        (M := unitSpace p ⊗[ℂ] unitSpace p) (tensorSum (unitTheta p) (unitTheta p)) (shift p k) :
        Submodule ℂ (unitSpace p ⊗[ℂ] unitSpace p)) ∧
      Module.finrank ℂ (kurokawaCone (unitTheta p) ⊓ Module.End.maxGenEigenspace (R := ℂ)
        (M := unitSpace p ⊗[ℂ] unitSpace p) (tensorSum (unitTheta p) (unitTheta p)) (shift p k) :
        Submodule ℂ (unitSpace p ⊗[ℂ] unitSpace p)) = k.natAbs + 1 := by
  classical
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hS := spectralCore_theta (1 : Module.End ℂ ℂ) hq
  set Z := {mn : ℤ × ℤ | mn.1 + mn.2 = k ∧ 0 ≤ mn.1 * mn.2}
  have hZfin : Z.Finite := Set.finite_of_ncard_pos (by rw [card_cone]; omega)
  set f : ℤ × ℤ → ℂ × ℂ := fun mn => (shift p mn.1, shift p mn.2)
  have hfinj : Function.Injective f := fun a b h => by
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext (shift_injective hq h.1) (shift_injective hq h.2)
  have himfin : (f '' Z).Finite := hZfin.image f
  obtain ⟨h1, h2⟩ := finrank_cone_inf hS (shift p k) himfin.toFinset
    (by rw [himfin.coe_toFinset]; exact cone_pairs hp k)
  refine ⟨h1, h2.trans ?_⟩
  have hone : ∀ x ∈ himfin.toFinset, mult (unitTheta p) x.1 * mult (unitTheta p) x.2 = 1 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨⟨a, b⟩, -, rfl⟩ := hx
    simp only [f, mult_unit hq, mul_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ himfin, Set.ncard_image_of_injective _ hfinj, card_cone]

/-- **`prop:kun-cone` (ii), equality.** The Kurokawa cone meets `⨁_ρ V_ρ ⊗ V_{1-ρ}` exactly in
the blocks with `ρ` real. -/
theorem kurokawaCone_inf_antidiag {V : Type u} [AddCommGroup V] [Module ℂ V]
    {Θ : Module.End ℂ V} (hS : SpectralCore Θ) :
    kurokawaCone Θ ⊓ (⨆ ρ, block Θ Θ ρ (1 - ρ)) =
      ⨆ ρ ∈ {ρ : ℂ | ρ.im = 0}, block Θ Θ ρ (1 - ρ) := by
  classical
  have hint := isInternal_block Θ Θ hS.iSup_eq_top hS.iSup_eq_top
  set f : ℂ → ℂ × ℂ := fun ρ => (ρ, 1 - ρ)
  have hU : ∀ U : Set ℂ, (⨆ ρ ∈ U, block Θ Θ ρ (1 - ρ)) =
      ⨆ x ∈ f '' U, block Θ Θ x.1 x.2 := fun U => by rw [iSup_image]
  have hall : (⨆ ρ, block Θ Θ ρ (1 - ρ)) = ⨆ ρ ∈ (Set.univ : Set ℂ), block Θ Θ ρ (1 - ρ) := by
    simp
  have hset : {x : ℂ × ℂ | 0 ≤ x.1.im * x.2.im} ∩ f '' Set.univ = f '' {ρ : ℂ | ρ.im = 0} := by
    ext ⟨ρ, ρ'⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.image_univ, Set.mem_range, f,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨h, ρ₀, rfl, rfl⟩
      refine ⟨ρ₀, ?_, rfl, rfl⟩
      have : (1 - ρ₀).im = -ρ₀.im := by simp
      rw [this] at h; nlinarith [sq_nonneg ρ₀.im]
    · rintro ⟨ρ₀, h0, rfl, rfl⟩
      exact ⟨by simp [h0], ρ₀, rfl, rfl⟩
  rw [hall, hU, hU, kurokawaCone, biSup_inf_biSup_of_isInternal hint, hset]

/-- **`prop:kun-cone` (ii), finiteness.** If the spectrum has only finitely many real points,
the meet of the Kurokawa cone with `⨁_ρ V_ρ ⊗ V_{1-ρ}` is finite-dimensional. -/
theorem finiteDimensional_kurokawaCone_inf_antidiag {V : Type u} [AddCommGroup V] [Module ℂ V]
    {Θ : Module.End ℂ V} (hS : SpectralCore Θ) (hfin : {ρ ∈ spec Θ | ρ.im = 0}.Finite) :
    FiniteDimensional ℂ (kurokawaCone Θ ⊓ (⨆ ρ, block Θ Θ ρ (1 - ρ)) :
      Submodule ℂ (V ⊗[ℂ] V)) := by
  classical
  rw [kurokawaCone_inf_antidiag hS]
  set R := hfin.toFinset
  have heq : (⨆ ρ ∈ {ρ : ℂ | ρ.im = 0}, block Θ Θ ρ (1 - ρ)) =
      ⨆ x ∈ ((R.image fun ρ => (ρ, 1 - ρ) : Finset (ℂ × ℂ)) : Set (ℂ × ℂ)),
        block Θ Θ x.1 x.2 := by
    rw [Finset.coe_image, iSup_image]
    apply le_antisymm
    · refine iSup₂_le fun ρ hρ => ?_
      by_cases hs : ρ ∈ spec Θ
      · exact le_biSup (fun ρ => block Θ Θ ρ (1 - ρ)) (by simp [R, hs, hρ.out])
      · rw [block_eq_bot_of_left Θ Θ _ (by simpa [spec] using hs)]; exact bot_le
    · exact biSup_mono fun ρ hρ => by simp [R] at hρ; exact hρ.2
  rw [heq]
  exact (finrank_biSup_block hS hS _).1

end WeilRH.KunOrbits
