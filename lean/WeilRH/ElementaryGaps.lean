/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Elementary gap examples: `prop:bsd-coefficient-gap`, `prop:bsd-primary-gap`, `prop:R11`,
`prop:R14`, `prop:R17`

Source: the manuscript `latex/notes.tex`, labels `prop:bsd-coefficient-gap`,
`prop:bsd-primary-gap`, `prop:R11` (i)–(iii) with `def:R11-quartet`, and `prop:R14` (i)–(iv) with `def:R14-sources`.

## Main results

* `WeilRH.ElementaryGaps.bsd_coefficient_gap`, `WeilRH.ElementaryGaps.lattice_gap`:
  **`prop:bsd-coefficient-gap`**.
* `WeilRH.ElementaryGaps.primaryComponent_finite`, `WeilRH.ElementaryGaps.G_infinite`:
  **`prop:bsd-primary-gap`** for `G = ⨁_{ℓ prime} ℤ/ℓℤ`.
* `WeilRH.R11.coeff_quartetC_im`, `eval_quartetC_neg`, `eval_quartetC_eq_zero_iff`,
  `root_im_ne_zero`: **`prop:R11` (i)**; `WeilRH.R11.im_neg_logDeriv_pos`: **`prop:R11` (ii)**;
  `WeilRH.R11.im_neg_logDeriv_value`, `norm_hb_lt`: **`prop:R11` (iii)**.
* `WeilRH.R14.compact_and_eigenvalue`: **`prop:R14` (i)**; `WeilRH.R14.shift`: **`prop:R14` (ii)**.
* `WeilRH.R14.corr` (`c_f` of `def:R14-sources`), `corr_eq_zero`, `corr_pos`: **`prop:R14` (iii)**;
  `corr_log_eq_zero`, `exists_corr_log_pos`: **`prop:R14` (iv)**.
* `WeilRH.R17.reflect` (the reflection of `def:hb`), `WeilRH.R17.integral_reflect_mul_deriv_eq_zero`:
  **`prop:R17` (i)**; `WeilRH.R17.bump` (`def:bump`), `WeilRH.R17.bump_spec`: **`prop:R17` (ii)**.
-/

open Complex
open scoped ComplexConjugate InnerProductSpace

namespace WeilRH.ElementaryGaps

/-! ### `prop:bsd-coefficient-gap` -/

/-- **`prop:bsd-coefficient-gap`, first sentence.** If `f` is meromorphic at `1` with nonzero
leading coefficient and `0 < c ≠ 1`, then `f` and `c f` have the same divisor (on any set `U`)
but different leading coefficients at `1`. The leading coefficient is Mathlib's
`meromorphicTrailingCoeffAt`, the first nonzero Laurent coefficient. -/
theorem bsd_coefficient_gap (U : Set ℂ) (f : ℂ → ℂ) (hf : MeromorphicAt f 1)
    (hlead : meromorphicTrailingCoeffAt f 1 ≠ 0) (c : ℝ) (hc : 0 < c) (hc1 : c ≠ 1) :
    MeromorphicOn.divisor ((c : ℂ) • f) U = MeromorphicOn.divisor f U ∧
      meromorphicTrailingCoeffAt ((c : ℂ) • f) 1 ≠ meromorphicTrailingCoeffAt f 1 := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨MeromorphicOn.divisor_const_smul hc0, ?_⟩
  have : (c : ℂ) • f = (fun _ : ℂ => (c : ℂ)) • f := rfl
  rw [this, (MeromorphicAt.const (c : ℂ) 1).meromorphicTrailingCoeffAt_smul hf,
    meromorphicTrailingCoeffAt_const, smul_eq_mul]
  intro h
  apply hc1
  have := mul_right_cancel₀ hlead (h.trans (one_mul _).symm)
  exact_mod_cast this

/-- **`prop:bsd-coefficient-gap`, second sentence.** The lattices `ℤ` and `2ℤ` in the Euclidean
line `ℝ` have the same real span, are different, and have Gram determinants `1` and `4`. -/
theorem lattice_gap :
    Submodule.span ℝ ((Submodule.span ℤ ({1} : Set ℝ) : Set ℝ)) =
        Submodule.span ℝ ((Submodule.span ℤ ({2} : Set ℝ) : Set ℝ)) ∧
      Submodule.span ℤ ({1} : Set ℝ) ≠ Submodule.span ℤ ({2} : Set ℝ) ∧
      (Matrix.gram ℝ ![(1 : ℝ)]).det = 1 ∧ (Matrix.gram ℝ ![(2 : ℝ)]).det = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 : Submodule.span ℝ ({1} : Set ℝ) = ⊤ := by
      rw [eq_top_iff]; intro x _; rw [Submodule.mem_span_singleton]; exact ⟨x, by simp⟩
    have h2 : Submodule.span ℝ ({2} : Set ℝ) = ⊤ := by
      rw [eq_top_iff]; intro x _; rw [Submodule.mem_span_singleton]
      exact ⟨x / 2, by simp⟩
    rw [h1, h2]
  · intro h
    have : (1 : ℝ) ∈ Submodule.span ℤ ({2} : Set ℝ) := h ▸ Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨n, hn⟩ := this
    have hn' : (n : ℝ) * 2 = 1 := by simpa using hn
    have : (n : ℝ) = 1 / 2 := by linarith
    have h0 : (0 : ℤ) < n := by exact_mod_cast (by rw [this]; norm_num : (0:ℝ) < n)
    have h1 : n < 1 := by exact_mod_cast (by rw [this]; norm_num : (n:ℝ) < 1)
    omega
  · simp [Matrix.gram]
  · simp [Matrix.gram]; norm_num

/-! ### `prop:bsd-primary-gap` -/

/-- `G = ⨁_{ℓ prime} ℤ/ℓℤ`. -/
abbrev G := DirectSum {ℓ : ℕ // ℓ.Prime} (fun ℓ => ZMod (ℓ : ℕ))

/-- **`prop:bsd-primary-gap`, first clause.** For every prime `ℓ` the `ℓ`-primary subgroup
`G[ℓ^∞]` (Mathlib's `AddCommMonoid.primaryComponent`) is finite. -/
theorem primaryComponent_finite (p : ℕ) [hp : Fact p.Prime] :
    Finite (AddCommMonoid.primaryComponent G p) := by
  set ℓ : {ℓ : ℕ // ℓ.Prime} := ⟨p, hp.out⟩
  have : NeZero (ℓ : ℕ) := ⟨hp.out.ne_zero⟩
  refine Finite.of_injective (fun g => (g : G) ℓ) ?_
  intro g g' h
  have hsupp : ∀ x : AddCommMonoid.primaryComponent G ℓ, ∀ ℓ' ≠ ℓ, (x : G) ℓ' = 0 := by
    intro x ℓ' hne
    obtain ⟨k, hk⟩ := (AddCommMonoid.mem_primaryComponent).1 x.2
    have hk' := congrArg (fun y : G => y ℓ') hk
    simp only [DirectSum.zero_apply] at hk'
    have hk'' : ((ℓ : ℕ) ^ k • (x : G) ℓ') = 0 := by
      rw [← DFinsupp.smul_apply]; exact hk'
    have : Fact (ℓ' : ℕ).Prime := ⟨ℓ'.2⟩
    have hcop : (((ℓ : ℕ) ^ k : ℕ) : ZMod (ℓ' : ℕ)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq ℓ'.2 ℓ.2).1 (ℓ'.2.dvd_of_dvd_pow hd)
      exact hne (Subtype.ext this)
    rw [nsmul_eq_mul] at hk''
    exact (mul_eq_zero.1 hk'').resolve_left hcop
  apply Subtype.ext
  ext ℓ'
  by_cases hl : ℓ' = ℓ
  · subst hl; exact h
  · rw [hsupp g ℓ' hl, hsupp g' ℓ' hl]

/-- **`prop:bsd-primary-gap`, second clause.** `G` is infinite. -/
theorem G_infinite : Infinite G := by
  have : Infinite {ℓ : ℕ // ℓ.Prime} := Nat.infinite_setOfPred_prime.to_subtype
  refine Infinite.of_injective (fun ℓ : {ℓ : ℕ // ℓ.Prime} => (DirectSum.of (fun ℓ : {ℓ : ℕ // ℓ.Prime} => ZMod (ℓ : ℕ)) ℓ 1 : G)) ?_
  intro ℓ ℓ' h
  by_contra hne
  have hl : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have h1 := congrArg (fun y : G => y ℓ) h
  simp only [DirectSum.of_eq_same] at h1
  rw [DirectSum.of_eq_of_ne _ _ _ hne] at h1
  exact one_ne_zero h1

end WeilRH.ElementaryGaps

namespace WeilRH.R11

open Polynomial

/-- `P_{T,a}(z) = ((z - T)² + a²)((z + T)² + a²)`, a real polynomial. -/
noncomputable def quartet (T a : ℝ) : ℝ[X] :=
  ((X - C T) ^ 2 + C (a ^ 2)) * ((X + C T) ^ 2 + C (a ^ 2))

/-- The quartet as a complex polynomial. -/
noncomputable def quartetC (T a : ℝ) : ℂ[X] := (quartet T a).map (algebraMap ℝ ℂ)

/-- The four zeros `±T ± i a`. -/
noncomputable def root (T a : ℝ) : Fin 4 → ℂ :=
  ![T + a * I, T - a * I, -T + a * I, -T - a * I]

/-- `P` evaluated at a complex point. -/
lemma eval_quartetC (T a : ℝ) (z : ℂ) :
    (quartetC T a).eval z = ((z - T) ^ 2 + (a : ℂ) ^ 2) * ((z + T) ^ 2 + (a : ℂ) ^ 2) := by
  simp [quartetC, quartet]

/-- `P = ∏_r (X - r)` over the four zeros. -/
lemma quartetC_eq (T a : ℝ) :
    quartetC T a = (X - C (root T a 0)) * (X - C (root T a 1)) * (X - C (root T a 2)) *
      (X - C (root T a 3)) := by
  apply Polynomial.funext
  intro z
  rw [eval_quartetC]
  simp only [root, eval_mul, eval_sub, eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination ((a : ℂ) ^ 2 * ((z - T) ^ 2 + (z + T) ^ 2) + (a : ℂ) ^ 4 * (1 - I ^ 2)) * I_sq


/-! ### `prop:R11` (i) -/

/-- **`prop:R11` (i), real coefficients.** -/
theorem coeff_quartetC_im (T a : ℝ) (n : ℕ) : ((quartetC T a).coeff n).im = 0 := by
  simp [quartetC, coeff_map]

/-- **`prop:R11` (i)**, `P(-z) = P(z)`. -/
theorem eval_quartetC_neg (T a : ℝ) (z : ℂ) :
    (quartetC T a).eval (-z) = (quartetC T a).eval z := by
  rw [eval_quartetC, eval_quartetC]; ring

/-- **`prop:R11` (i)**, the zeros of `P` are exactly `±T ± i a`. -/
theorem eval_quartetC_eq_zero_iff (T a : ℝ) (z : ℂ) :
    (quartetC T a).eval z = 0 ↔ ∃ i, z = root T a i := by
  rw [quartetC_eq]
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (((h | h) | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- Each zero has imaginary part `±a`. -/
theorem root_im (T a : ℝ) (i : Fin 4) : (root T a i).im = a ∨ (root T a i).im = -a := by
  fin_cases i <;> simp [root]

/-- **`prop:R11` (i)**, for `a > 0` no zero of `P` is real. -/
theorem root_im_ne_zero {T a : ℝ} (ha : 0 < a) (i : Fin 4) : (root T a i).im ≠ 0 := by
  rcases root_im T a i with h | h <;> rw [h] <;> linarith

/-- `Im (1 / (r - z)) > 0` when `Im r < Im z`. -/
lemma im_inv_sub_pos {r z : ℂ} (h : r.im < z.im) : 0 < (1 / (r - z)).im := by
  have hw : r - z ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  rw [one_div, Complex.inv_im]
  apply div_pos
  · simp; linarith
  · exact Complex.normSq_pos.2 hw

/-! ### `prop:R11` (ii) -/

/-- `-P'/P = ∑_r 1 / (r - z)` away from the zeros. -/
theorem neg_logDeriv_eq (T a : ℝ) (z : ℂ) (hz : ∀ i, z ≠ root T a i) :
    -(derivative (quartetC T a)).eval z / (quartetC T a).eval z =
      ∑ i, 1 / (root T a i - z) := by
  have h : ∀ i, z - root T a i ≠ 0 := fun i => sub_ne_zero.2 (hz i)
  have h' : ∀ i, root T a i - z ≠ 0 := fun i => sub_ne_zero.2 (hz i).symm
  rw [quartetC_eq]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    mul_one, eval_mul, eval_add, eval_sub, eval_X, eval_C, Fin.sum_univ_four]
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h0' := h' 0; have h1' := h' 1; have h2' := h' 2; have h3' := h' 3
  field_simp
  ring

/-- **`prop:R11` (ii).** `Im(-P'(z)/P(z)) > 0` whenever `Im z > a`. -/
theorem im_neg_logDeriv_pos {T a : ℝ} (ha : 0 < a) {z : ℂ} (hz : a < z.im) :
    0 < (-(derivative (quartetC T a)).eval z / (quartetC T a).eval z).im := by
  have hlt : ∀ i, (root T a i).im < z.im := by
    intro i; rcases root_im T a i with h | h <;> rw [h] <;> linarith
  have hne : ∀ i, z ≠ root T a i := by
    intro i h; have := hlt i; rw [← h] at this; exact lt_irrefl _ this
  rw [neg_logDeriv_eq T a z hne, Complex.im_sum]
  exact Finset.sum_pos (fun i _ => im_inv_sub_pos (hlt i)) Finset.univ_nonempty

/-! ### `prop:R11` (iii) -/

/-- `|x + i y|² - |x - i y|² = 4 |x|² Im(-y/x)`, in the form used for `prop:R11` (iii): if
`Im(-y/x) < 0` then `|x + i y| < |x - i y|`. -/
lemma norm_add_I_mul_lt {x y : ℂ} (hx : x ≠ 0) (h : (-y / x).im < 0) :
    ‖x + I * y‖ < ‖x - I * y‖ := by
  have hn : 0 < Complex.normSq x := Complex.normSq_pos.2 hx
  have key : x.im * y.re - x.re * y.im < 0 := by
    rw [Complex.div_im] at h
    have : (-y).im * x.re / normSq x - (-y).re * x.im / normSq x
        = (x.im * y.re - x.re * y.im) / normSq x := by
      simp only [Complex.neg_im, Complex.neg_re]; ring
    rw [this] at h
    exact (div_neg_iff.1 h).resolve_left (fun h' => absurd h'.2 (not_lt.2 hn.le)) |>.1
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- `2 + i/8` is not a zero of `P_{2,1/4}`. -/
lemma ne_root_value : ∀ i, (2 + I / 8 : ℂ) ≠ root 2 (1 / 4) i := by
  intro i h
  have := congrArg Complex.im h
  rcases root_im 2 (1 / 4) i with h' | h' <;> (rw [h'] at this; norm_num at this)

/-- **`prop:R11` (iii), the value.** For `T = 2`, `a = 1/4`,
`Im(-P'(2 + i/8) / P(2 + i/8)) = -16892192/3176475`. -/
theorem im_neg_logDeriv_value :
    (-(derivative (quartetC 2 (1 / 4))).eval (2 + I / 8) /
      (quartetC 2 (1 / 4)).eval (2 + I / 8)).im = -16892192 / 3176475 := by
  rw [neg_logDeriv_eq 2 (1 / 4) _ ne_root_value, Complex.im_sum, Fin.sum_univ_four]
  simp only [root, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_div, Complex.inv_im,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im]
  norm_num

/-- **`prop:R11` (iii), the HB inequality.** With `E_P = P + iP'` and `E_P^# = P - iP'` (the
source's `E_P^#`, using `P^# = P`), `|E_P(2 + i/8)| < |E_P^#(2 + i/8)|` for `T = 2`, `a = 1/4`. -/
theorem norm_hb_lt :
    ‖(quartetC 2 (1 / 4)).eval (2 + I / 8) + I * (derivative (quartetC 2 (1 / 4))).eval (2 + I / 8)‖ <
      ‖(quartetC 2 (1 / 4)).eval (2 + I / 8) -
        I * (derivative (quartetC 2 (1 / 4))).eval (2 + I / 8)‖ := by
  have hP : (quartetC 2 (1 / 4)).eval (2 + I / 8) ≠ 0 := by
    rw [Ne, eval_quartetC_eq_zero_iff]
    rintro ⟨i, hi⟩
    exact ne_root_value i hi
  refine norm_add_I_mul_lt hP ?_
  rw [neg_div, ← neg_div, im_neg_logDeriv_value]
  norm_num

end WeilRH.R11

namespace WeilRH.R14

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **`prop:R14` (i).** For a rank-one orthogonal projection `P = K.starProjection`
(`finrank K = 1`), `-2P` is a compact operator and `I - 2P` has the eigenvalue `-1`. Completeness
of `H` is not needed. -/
theorem compact_and_eigenvalue (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (hK : Module.finrank ℂ K = 1) :
    IsCompactOperator (⇑(-(2 : ℂ) • K.starProjection)) ∧
      Module.End.HasEigenvalue
        ((ContinuousLinearMap.id ℂ H - (2 : ℂ) • K.starProjection : H →L[ℂ] H) :
          Module.End ℂ H) (-1) := by
  refine ⟨?_, ?_⟩
  · have hc : IsCompactOperator (⇑K.starProjection) :=
      (isCompactOperator_of_locallyCompactSpace_dom K.orthogonalProjectionOnto).clm_comp
        K.subtypeL
    exact hc.smul _
  · have : Nontrivial K := Module.nontrivial_of_finrank_eq_succ hK
    obtain ⟨v, hv⟩ : ∃ v : K, v ≠ 0 := exists_ne 0
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := (v : H))
    refine ⟨?_, by simpa using hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.id_apply,
      Submodule.starProjection_mem_subspace_eq_self]
    module

/-- **`prop:R14` (ii).** For every `ε < 0` there is a bounded self-adjoint operator `Q` such
that `Q - εI` is positive semidefinite and `Q` is not; as in the manuscript, `Q = ε` on `ℂ`. -/
theorem shift (ε : ℝ) (hε : ε < 0) :
    ∃ Q : ℂ →L[ℂ] ℂ, IsSelfAdjoint Q ∧ (Q - (ε : ℂ) • ContinuousLinearMap.id ℂ ℂ).IsPositive ∧
      ¬ Q.IsPositive := by
  refine ⟨(ε : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_, by simp [ContinuousLinearMap.isPositive_zero],
    ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp
    ring
  · intro h
    have := h.re_inner_nonneg_left 1
    simp at this
    linarith

section Correlation

open MeasureTheory Set
open scoped ComplexOrder

/-- The correlation `c_f(x) = ∫ f(y) conj(f(y - x)) dy` (`def:R14-sources`). -/
noncomputable def corr (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, f y * conj (f (y - x))

/-- A continuous `f` with `supp f ⊆ [-ℓ, ℓ]` is nonzero only on `(-ℓ, ℓ)`. -/
lemma support_subset_Ioo {f : ℝ → ℂ} (hf : Continuous f) {ℓ : ℝ}
    (hsupp : tsupport f ⊆ Icc (-ℓ) ℓ) : Function.support f ⊆ Ioo (-ℓ) ℓ := by
  rw [← interior_Icc]
  exact interior_maximal (subset_tsupport f |>.trans hsupp) hf.isOpen_support

/-- **`prop:R14` (iii), first claim.** If `f` is continuous with `supp f ⊆ [-ℓ, ℓ]`, then
`c_f(x) = 0` for `|x| ≥ 2ℓ`. -/
theorem corr_eq_zero {f : ℝ → ℂ} (hf : Continuous f) {ℓ : ℝ}
    (hsupp : tsupport f ⊆ Icc (-ℓ) ℓ) {x : ℝ} (hx : 2 * ℓ ≤ |x|) : corr f x = 0 := by
  have hs := support_subset_Ioo hf hsupp
  have : (fun y => f y * conj (f (y - x))) = 0 := by
    funext y
    by_contra h
    have h1 : f y ≠ 0 := left_ne_zero_of_mul h
    have h2 : f (y - x) ≠ 0 := by
      intro h0; apply h; simp [h0]
    have a := hs h1
    have b := hs h2
    simp only [mem_Ioo] at a b
    rcases abs_cases x with ⟨hx', _⟩ | ⟨hx', _⟩ <;> rw [hx'] at hx <;> linarith [a.1, a.2, b.1, b.2]
  simp [corr, this]

/-- **`prop:R14` (iii), second claim.** If moreover `f` is real and `f > 0` on `(-ℓ, ℓ)`, then
`c_f(x) > 0` (in the order of `ℂ`: real and positive) for `|x| < 2ℓ`. -/
theorem corr_pos {f : ℝ → ℂ} (hf : Continuous f) {ℓ : ℝ}
    (hsupp : tsupport f ⊆ Icc (-ℓ) ℓ) (hreal : ∀ y, (f y).im = 0)
    (hpos : ∀ y ∈ Ioo (-ℓ) ℓ, 0 < (f y).re) {x : ℝ} (hx : |x| < 2 * ℓ) : 0 < corr f x := by
  set F : ℝ → ℝ := fun y => (f y).re
  have hfF : ∀ y, f y = (F y : ℂ) := fun y => Complex.ext (by simp [F]) (by simp [hreal])
  have hs := support_subset_Ioo hf hsupp
  have hF0 : ∀ y, 0 ≤ F y := by
    intro y
    by_cases hy : y ∈ Ioo (-ℓ) ℓ
    · exact (hpos y hy).le
    · have : f y = 0 := by_contra fun h => hy (hs h)
      simp [F, this]
  have hFc : Continuous F := continuous_re.comp hf
  have hcorr : corr f x = ((∫ y, F y * F (y - x) : ℝ) : ℂ) := by
    rw [corr, show (fun y => f y * conj (f (y - x))) = fun y => ((F y * F (y - x) : ℝ) : ℂ) by
      funext y; rw [hfF y, hfF (y - x)]; simp]
    exact integral_ofReal
  rw [hcorr]
  have hint : Integrable (fun y => F y * F (y - x)) := by
    have hcs : HasCompactSupport (fun y => F y * F (y - x)) := by
      have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hsupp
      have hFcs : HasCompactSupport F := hfc.comp_left Complex.zero_re
      exact hFcs.mul_right
    exact (hFc.mul (hFc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hcs
  have hpos' : 0 < ∫ y, F y * F (y - x) := by
    rw [integral_pos_iff_support_of_nonneg (fun y => mul_nonneg (hF0 y) (hF0 _)) hint]
    have hsub : Ioo (max (-ℓ) (x - ℓ)) (min ℓ (x + ℓ)) ⊆ Function.support (fun y => F y * F (y - x)) := by
      intro y hy
      simp only [mem_Ioo, max_lt_iff, lt_min_iff] at hy
      exact (mul_pos (hpos y ⟨hy.1.1, hy.2.1⟩) (hpos _ ⟨by linarith, by linarith⟩)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo, ENNReal.ofReal_pos, sub_pos]
    rcases abs_lt.mp hx with ⟨h1, h2⟩
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  exact_mod_cast hpos'

/-- **`prop:R14` (iv), first claim.** If `ℓ ≤ ½ log 2`, then `c_f(log n) = 0` for every `f` as
in (iii) and every integer `n ≥ 2`. -/
theorem corr_log_eq_zero {ℓ : ℝ} (_hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ Real.log 2 / 2) {f : ℝ → ℂ}
    (hf : Continuous f) (hsupp : tsupport f ⊆ Icc (-ℓ) ℓ) {n : ℕ} (hn : 2 ≤ n) :
    corr f (Real.log n) = 0 := by
  refine corr_eq_zero hf hsupp ?_
  have h2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [abs_of_nonneg ((Real.log_nonneg (by norm_num)).trans h2)]
  linarith

/-- **`prop:R14` (iv), second claim.** If `ℓ > ½ log 2`, the tent `f(t) = max(0, ℓ - |t|)` is as
in (iii) and has `c_f(log n) > 0` for every integer `2 ≤ n < e^{2ℓ}`. -/
theorem exists_corr_log_pos {ℓ : ℝ} (_hℓ : Real.log 2 / 2 < ℓ) :
    ∃ f : ℝ → ℂ, Continuous f ∧ tsupport f ⊆ Icc (-ℓ) ℓ ∧ (∀ y, (f y).im = 0) ∧
      (∀ y ∈ Ioo (-ℓ) ℓ, 0 < (f y).re) ∧
      ∀ n : ℕ, 2 ≤ n → (n : ℝ) < Real.exp (2 * ℓ) → 0 < corr f (Real.log n) := by
  set f : ℝ → ℂ := fun t => ((max 0 (ℓ - |t|) : ℝ) : ℂ)
  have hf : Continuous f := continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_abs))
  have hsupp : tsupport f ⊆ Icc (-ℓ) ℓ := by
    refine closure_minimal (fun t ht => ?_) isClosed_Icc
    have : max 0 (ℓ - |t|) ≠ 0 := fun h => ht (by simp [f, h])
    have : |t| ≤ ℓ := by
      by_contra h; exact this (max_eq_left (by linarith))
    exact abs_le.mp this
  have hpos : ∀ y ∈ Ioo (-ℓ) ℓ, 0 < (f y).re := by
    intro y hy
    have : |y| < ℓ := abs_lt.mpr hy
    simp only [f, ofReal_re]
    exact lt_max_of_lt_right (by linarith)
  refine ⟨f, hf, hsupp, fun y => by simp [f], hpos, fun n hn hlt => ?_⟩
  refine corr_pos hf hsupp (fun y => by simp [f]) hpos ?_
  have hn' : (0 : ℝ) < n := by positivity
  have h0 : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [abs_of_pos h0]
  exact (Real.log_lt_iff_lt_exp hn').mpr hlt

end Correlation

end WeilRH.R14

namespace WeilRH.R17

open MeasureTheory
open scoped ContDiff

/-- The reflection `F^#(z) = conj (F (conj z))` of `def:hb`. -/
def reflect (f : ℂ → ℂ) (z : ℂ) : ℂ := conj (f (conj z))

/-- **`prop:R17` (i).** -/
theorem integral_reflect_mul_deriv_eq_zero (Ω : Set ℂ) (_hΩ : ∀ z ∈ Ω, conj z ∈ Ω)
    (S : ℝ → ℂ → ℂ) (hS : ∀ t, S (-t) = S t)
    (_hloc : ∀ z ∈ Ω, LocallyIntegrable (fun t => S t z))
    (ψ : ℝ → ℂ) (_hψ : ContDiff ℝ ∞ ψ) (_hψc : HasCompactSupport ψ) (hψe : ∀ t, ψ (-t) = ψ t)
    (z : ℂ) (_hz : z ∈ Ω) :
    ∫ t, reflect (S t) z * (I * deriv ψ t) = 0 := by
  have hodd : ∀ t, deriv ψ (-t) = -deriv ψ t := by
    intro t
    have h : (fun x => ψ (-x)) = ψ := funext hψe
    have := deriv_comp_neg (f := ψ) (-t)
    rw [h, neg_neg] at this
    exact this
  set g : ℝ → ℂ := fun t => reflect (S t) z * (I * deriv ψ t)
  have hg : ∀ t, g (-t) = -g t := by
    intro t; simp only [g, hS, hodd]; ring
  have h1 : ∫ t, g t = ∫ t, g (-t) := (integral_neg_eq_self g volume).symm
  simp only [hg, integral_neg] at h1
  exact CharZero.eq_neg_self_iff.mp h1

/-- The standard bump `ψ₀` of `def:bump`. -/
noncomputable def bump (t : ℝ) : ℝ := if |t| < 1 then Real.exp (-1 / (1 - t ^ 2)) else 0

lemma bump_eq (t : ℝ) : bump t = expNegInvGlue (1 - t ^ 2) := by
  unfold bump expNegInvGlue
  by_cases h : |t| < 1
  · have : 0 < 1 - t ^ 2 := by
      have := sq_lt_one_iff_abs_lt_one t |>.mpr h; linarith
    simp only [h, ↓reduceIte, not_le.mpr this, neg_div, one_div]
  · have : 1 - t ^ 2 ≤ 0 := by
      have := (one_le_sq_iff_one_le_abs t).mpr (not_lt.mp h); linarith
    simp only [h, ↓reduceIte, this]

/-- **`prop:R17` (ii).** -/
theorem bump_spec : ContDiff ℝ ∞ bump ∧ HasCompactSupport bump ∧ (∀ t, bump (-t) = bump t) ∧
    bump 0 = Real.exp (-1) ∧ bump ≠ 0 := by
  have hfun : bump = fun t => expNegInvGlue (1 - t ^ 2) := funext bump_eq
  refine ⟨?_, ?_, fun t => by simp [bump], by simp [bump], fun h => ?_⟩
  · rw [hfun]; exact expNegInvGlue.contDiff.comp (by fun_prop)
  · refine HasCompactSupport.intro (K := Set.Icc (-1) 1) isCompact_Icc fun t ht => ?_
    have : ¬ |t| < 1 := fun h' => ht (abs_le.mp h'.le)
    simp [bump, this]
  · have := congrFun h 0
    simp [bump, Real.exp_ne_zero] at this

end WeilRH.R17
