/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.BlackBoxes
import WeilRH.ProjectiveLineScheme

/-!
# `prop:N-lines` from the Weil conjectures (round 68)

`latex/notes.tex`, `prop:N-lines`: for `X = E × ℙ¹` over `𝔽_q`, `ζ_X` has zeros on the two lines
`Re s = 1/2, 3/2` and poles on `Re s ∈ {0, 1, 2}`. Rounds 9 and the Axiom Math investigation proved
this from the elliptic count `#E(𝔽_{qⁿ}) = qⁿ + 1 - αⁿ - βⁿ` with `|α| = |β| = q^{1/2}`
(`NLinesGeometry.zetaOfCounts_finiteExtensions_eq_zetaX`). That count was the remaining geometric
input.

Here the black box `WeilConjectures` (B2', `WeilRH/BlackBoxes.lean`) supplies it, for any smooth,
proper, geometrically irreducible curve `X` over `𝔽_q`: `#X(𝔽_{qⁿ}) = qⁿ + 1 - Σ_{α ∈ A₁} αⁿ` with
every `α ∈ A₁` of absolute value `q^{1/2}`. B2' does not record `#A₁ = 2g`, so the analytic part is
proved for an arbitrary multiset `A₁` (`zetaXM`); the manuscript's two-term `zetaX` is the case
`A₁ = {α, β}` (`zetaXM_pair`). The zero and pole locations need only purity, not `#A₁`.

Everything using B2' is CONDITIONAL on `WeilConjectures`, which is **not kernel-checked** in this
project (see `BlackBoxes.lean`). The identification of the projective-line scheme's points with
abstract projective points remains the hypothesis `e` (README open obligation 11).
-/

open Complex AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

namespace WeilRH.NLines

/-! ### The multiset form of the rational expression -/

/-- `∏_{α ∈ A} (1 - α q^{-s})(1 - α q^{1-s})`: the numerator of `ζ_{C × ℙ¹}` for a curve `C` with
`H¹`-eigenvalue multiset `A`. -/
noncomputable def numM (q : ℝ) (A : Multiset ℂ) (s : ℂ) : ℂ :=
  (A.map fun α => (1 - α * qpow q (-s)) * (1 - α * qpow q (-(s - 1)))).prod

/-- The rational expression `numM / den` for `ζ_{C × ℙ¹}`. -/
noncomputable def zetaXM (q : ℝ) (A : Multiset ℂ) (s : ℂ) : ℂ := numM q A s / den q s

/-- For `A = {α, β}` the multiset form is the manuscript's `zetaX`. -/
theorem zetaXM_pair (q : ℝ) (α β s : ℂ) : zetaXM q {α, β} s = zetaX q α β s := by
  simp only [zetaXM, zetaX, numM, num, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  ring

theorem numM_eq_zero_iff (q : ℝ) (A : Multiset ℂ) (s : ℂ) :
    numM q A s = 0 ↔ ∃ α ∈ A, s ∈ progression q α ∨ s ∈ shift1 (progression q α) := by
  simp only [numM, Multiset.prod_eq_zero_iff, Multiset.mem_map, mul_eq_zero,
    one_sub_mul_qpow_neg_eq_zero_iff, shift1, Set.mem_ofPred_eq]

/-- **`prop:N-lines` (ii), location, multiset form.** If every `α ∈ A` has `|α| = q^{1/2}`, the
numerator vanishes only on `Re s = 1/2` and `Re s = 3/2`. -/
theorem re_of_numM_eq_zero {q : ℝ} (hq : 1 < q) {A : Multiset ℂ}
    (hA : ∀ α ∈ A, ‖α‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ} (hs : numM q A s = 0) :
    s.re = 1 / 2 ∨ s.re = 3 / 2 := by
  obtain ⟨α, hα, h | h⟩ := (numM_eq_zero_iff q A s).1 hs
  · exact Or.inl (re_of_mem_progression hq h (hA α hα))
  · right; have := re_of_mem_progression hq h (hA α hα); simp at this; linarith

/-- Numerator and denominator have no common zero (multiset form). -/
theorem den_ne_zero_of_numM_eq_zero {q : ℝ} (hq : 1 < q) {A : Multiset ℂ}
    (hA : ∀ α ∈ A, ‖α‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ} (hs : numM q A s = 0) : den q s ≠ 0 := by
  intro hd
  rcases re_of_numM_eq_zero hq hA hs with h | h <;>
    rcases re_of_den_eq_zero hq hd with h' | h' | h' <;> (rw [h] at h'; norm_num at h')

/-- **`prop:N-lines` (ii)–(iii), multiset form.** Zeros of `zetaXM` lie on `Re s ∈ {1/2, 3/2}`,
and wherever the denominator vanishes (the only possible poles) `Re s ∈ {0, 1, 2}`. -/
theorem zetaXM_zeros_poles {q : ℝ} (hq : 1 < q) {A : Multiset ℂ}
    (hA : ∀ α ∈ A, ‖α‖ = q ^ ((1 : ℝ) / 2)) (s : ℂ) :
    (zetaXM q A s = 0 → den q s ≠ 0 → s.re = 1 / 2 ∨ s.re = 3 / 2) ∧
      (den q s = 0 → s.re = 0 ∨ s.re = 1 ∨ s.re = 2) := by
  refine ⟨fun h hd => ?_, re_of_den_eq_zero hq⟩
  rw [zetaXM, div_eq_zero_iff] at h
  exact re_of_numM_eq_zero hq hA (h.resolve_right hd)

/-- The curve zeta function from a multiset of pure weight-one eigenvalues: for `Re s > 1`,
`#C(𝔽_{qⁿ}) = qⁿ + 1 - Σ_{α ∈ A} αⁿ` gives `ζ_C(s) = ∏_α (1 - αt)/((1 - t)(1 - qt))`,
`t = q^{-s}`, and the defining series converges. -/
theorem zetaOfCounts_curve {q : ℝ} (hq : 1 < q) {A : Multiset ℂ}
    (hA : ∀ α ∈ A, ‖α‖ = q ^ ((1 : ℝ) / 2)) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
        ((q : ℂ) ^ n + 1 - (A.map (· ^ n)).sum) * qpow q (-s) ^ n / n) ∧
      zetaOfCounts q (fun n => (q : ℂ) ^ n + 1 - (A.map (· ^ n)).sum) s =
        (A.map fun α => 1 - α * qpow q (-s)).prod /
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
  -- The multiset part, by induction.
  have hM : ∀ B : Multiset ℂ, (∀ α ∈ B, ‖α‖ = q ^ ((1 : ℝ) / 2)) →
      HasSum (fun n : ℕ => (B.map (· ^ n)).sum * t ^ n / n)
        (-(B.map fun α => log (1 - α * t)).sum) ∧
      exp ((B.map fun α => log (1 - α * t)).sum) = (B.map fun α => 1 - α * t).prod := by
    intro B
    induction B using Multiset.induction_on with
    | empty => intro _; simp [hasSum_zero]
    | cons a B ih =>
      intro hB
      obtain ⟨ihs, ihe⟩ := ih fun α hα => hB α (Multiset.mem_cons_of_mem hα)
      have ha := hγ a (hB a (Multiset.mem_cons_self a B))
      refine ⟨?_, ?_⟩
      · have := (hasSum_log ha).add ihs
        convert this using 1
        · funext n; simp only [Multiset.map_cons, Multiset.sum_cons, mul_pow]; ring
        · simp only [Multiset.map_cons, Multiset.sum_cons]; ring
      · simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, exp_add, ihe,
          exp_log (one_sub_ne_zero_of_norm_lt ha)]
  obtain ⟨hMs, hMe⟩ := hM A hA
  have key : HasSum (fun n : ℕ => ((q : ℂ) ^ n + 1 - (A.map (· ^ n)).sum) * t ^ n / n)
      ((A.map fun α => log (1 - α * t)).sum - log (1 - t) - log (1 - q * t)) := by
    have := ((hasSum_log hqt).add (hasSum_log h1)).sub hMs
    convert this using 1
    · funext n; simp only [mul_pow]; ring
    · ring
  refine ⟨key.summable, ?_⟩
  rw [zetaOfCounts, key.tsum_eq, exp_sub, exp_sub, hMe,
    exp_log (one_sub_ne_zero_of_norm_lt h1), exp_log (one_sub_ne_zero_of_norm_lt hqt),
    div_div]

/-- **`ζ_{C × ℙ¹}` is `zetaXM`** on `Re s > 2` (multiset form of `zetaOfCounts_eq_zetaX`). -/
theorem zetaOfCounts_eq_zetaXM {q : ℝ} (hq : 1 < q) {A : Multiset ℂ}
    (hA : ∀ α ∈ A, ‖α‖ = q ^ ((1 : ℝ) / 2)) (cX : ℕ → ℂ)
    (hX : ∀ n, 0 < n → cX n = ((q : ℂ) ^ n + 1 - (A.map (· ^ n)).sum) +
      (q : ℂ) ^ n * ((q : ℂ) ^ n + 1 - (A.map (· ^ n)).sum)) {s : ℂ} (hs : 2 < s.re) :
    zetaOfCounts q cX s = zetaXM q A s := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hs1 : 1 < (s - 1).re := by simp; linarith
  obtain ⟨hE1, hZ1⟩ := zetaOfCounts_curve hq hA (s := s) (by linarith)
  obtain ⟨hE2, hZ2⟩ := zetaOfCounts_curve hq hA hs1
  rw [zetaOfCounts_product_pos hq0 _ cX hX hE1 hE2, hZ1, hZ2, zetaXM, numM, den]
  have e1 := qpow_neg_sub_natCast hq0 s 1
  have e2 := qpow_neg_sub_natCast hq0 s 2
  simp only [Nat.cast_one, pow_one, Nat.cast_ofNat] at e1 e2
  rw [e2, e1, div_mul_div_comm, Multiset.prod_map_mul]
  ring

end WeilRH.NLines

namespace WeilRH.NLinesGeometry

/-! ### The Weil-conjecture count for a curve -/

variable (F : Type) [Field F] [Finite F]

/-- `KPoints` of the structure morphism are the `Over`-morphisms counted in `WeilConjectures`. -/
noncomputable def kPointsEquivOver (X : Over (Spec (CommRingCat.of F))) (E : Type) [Field E] [Algebra F E] :
    KPoints X.hom E ≃ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ X) where
  toFun p := Over.homMk p.1 p.2
  invFun φ := ⟨φ.left, Over.w φ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The Lefschetz count for a curve, from B2'.** For a smooth, proper, geometrically irreducible
curve `X` over `𝔽_q`, there is a multiset `A₁` of weight-one Weil numbers (`|α| = q^{1/2}`) with
`#X(E) = q^{[E:F]} + 1 - Σ_{α ∈ A₁} α^{[E:F]}` for every finite extension `E/F`.
CONDITIONAL on `WeilConjectures`. -/
theorem curve_count (hW : WeilConjectures) (X : Over (Spec (CommRingCat.of F)))
    [GeometricallyIrreducible X.hom] [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] :
    ∃ A₁ : Multiset ℂ, (∀ α ∈ A₁, ‖α‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2)) ∧
      ∀ (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E],
        (pointCount X.hom E : ℂ) =
          (Nat.card F : ℂ) ^ Module.finrank F E + 1 -
            (A₁.map (· ^ Module.finrank F E)).sum := by
  obtain ⟨A, hA0, hA, hcount⟩ := hW F X 1
  refine ⟨A 1, fun α hα => ?_, fun E _ _ _ => ?_⟩
  · rw [((hA 1 (by norm_num)).2.2 α hα).2, pow_one, Real.sqrt_eq_rpow]
  · have h2 : A 2 = {(Nat.card F : ℂ)} := by
      have := (hA 0 (by norm_num)).1
      simpa [hA0] using this
    rw [pointCount, Nat.card_congr (kPointsEquivOver F X E)]
    rw [hcount E, show (Finset.Iic (2 * 1) : Finset ℕ) = Finset.range 3 by decide]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hA0, h2]
    simp
    ring

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- **`prop:N-lines`, conditional on B2'.** For a smooth, proper, geometrically irreducible curve
`X` over `𝔽_q` (in particular an elliptic curve `E`) and the projective-line scheme
`ℙ¹_F = Proj F[X₀, X₁]`, there is a multiset `A₁` of weight-one Weil numbers such that on
`Re s > 2`, `ζ_{X × ℙ¹}(s) = zetaXM q A₁ s`; its zeros lie on `Re s = 1/2, 3/2` and its possible
poles on `Re s ∈ {0, 1, 2}`. Hypotheses: `WeilConjectures` (B2', not kernel-checked here) and the
point identification `e` for `ℙ¹_F` (open obligation 11). -/
theorem nLines_of_weil (hW : WeilConjectures) (X : Over (Spec (CommRingCat.of F)))
    [GeometricallyIrreducible X.hom] [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
    (e : ∀ n, 0 < n → KPoints (projectiveLineToSpec F) (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n)) :
    ∃ A₁ : Multiset ℂ, (∀ α ∈ A₁, ‖α‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2)) ∧
      (∀ s : ℂ, 2 < s.re →
        NLines.zetaOfCounts (Nat.card F)
            (countSequence (pullback.fst X.hom (projectiveLineToSpec F) ≫ X.hom)
              (finiteExtensionFamily F p)) s =
          NLines.zetaXM (Nat.card F) A₁ s) ∧
      ∀ s : ℂ,
        (NLines.zetaXM (Nat.card F) A₁ s = 0 → NLines.den (Nat.card F) s ≠ 0 →
          s.re = 1 / 2 ∨ s.re = 3 / 2) ∧
        (NLines.den (Nat.card F) s = 0 → s.re = 0 ∨ s.re = 1 ∨ s.re = 2) := by
  have hq : 1 < (Nat.card F : ℝ) := by exact_mod_cast (Finite.one_lt_card (α := F))
  obtain ⟨A₁, hA, hc⟩ := curve_count F hW X
  refine ⟨A₁, hA, fun s hs => ?_, NLines.zetaXM_zeros_poles hq hA⟩
  apply NLines.zetaOfCounts_eq_zetaXM hq hA _ ?_ hs
  intro n hn
  have hfr : Module.finrank F (finiteExtensionFamily F p n) = n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    exact FiniteField.finrank_extension F p (0 + m + 1)
  have hE := hc (finiteExtensionFamily F p n)
  rw [hfr] at hE
  have hprod :
      countSequence (pullback.fst X.hom (projectiveLineToSpec F) ≫ X.hom)
          (finiteExtensionFamily F p) n =
        countSequence X.hom (finiteExtensionFamily F p) n *
          ((Nat.card F : ℂ) ^ n + 1) := by
    simp only [countSequence]
    rw [pointCount_pullback,
      pointCount_projectiveLine_of_equiv (projectiveLineToSpec F) (finiteExtensionFamily F p n)
        (e n hn), card_finiteExtensionFamily F p n hn]
    norm_cast
  rw [hprod]
  simp only [countSequence]
  rw [hE]
  push_cast
  ring

/-- **The remark after `prop:formal-curve`, conditional on B2'.** No smooth, proper, geometrically
irreducible curve over a finite field has `N_n = #X(𝔽_{qⁿ}) = 0` for every `n ≥ 1`: by purity,
`|Σ_{α ∈ A₁} αⁿ| ≤ #A₁ · q^{n/2} < qⁿ + 1` once `q^{n/2} > #A₁`. So the formal curve of
`prop:formal-curve` (`q = 3`, `N_n = 0`) is not the cohomology of a curve. -/
theorem exists_count_ne_zero (hW : WeilConjectures) (X : Over (Spec (CommRingCat.of F)))
    [GeometricallyIrreducible X.hom] [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom] :
    ∃ n, 0 < n ∧ pointCount X.hom (finiteExtensionFamily F p n) ≠ 0 := by
  obtain ⟨A₁, hA, hc⟩ := curve_count F hW X
  set q : ℝ := (Nat.card F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (Finite.one_lt_card (α := F))
  set r : ℝ := q ^ ((1 : ℝ) / 2)
  have hr : 1 < r := Real.one_lt_rpow hq (by norm_num)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (A₁.card : ℝ) hr
  obtain ⟨n, hn, hmn⟩ : ∃ n, 0 < n ∧ (A₁.card : ℝ) < r ^ n :=
    ⟨m + 1, Nat.succ_pos m, hm.trans (pow_lt_pow_right₀ hr (Nat.lt_succ_self m))⟩
  refine ⟨n, hn, fun h0 => ?_⟩
  have hfr : Module.finrank F (finiteExtensionFamily F p n) = n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
    exact FiniteField.finrank_extension F p (0 + k + 1)
  have hE := hc (finiteExtensionFamily F p n)
  rw [hfr, h0, Nat.cast_zero, eq_comm, sub_eq_zero] at hE
  have hrn : r ^ n * r ^ n = q ^ n := by
    rw [← mul_pow, ← Real.rpow_add (by linarith)]; norm_num
  have hbound : ‖(A₁.map (· ^ n)).sum‖ ≤ A₁.card * r ^ n := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    have : ∀ x ∈ A₁.map ((‖·‖) ∘ (· ^ n)), x ≤ r ^ n := by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      simp [norm_pow, hA α hα, r]
    simpa using Multiset.sum_le_card_nsmul _ _ this
  have hlt : (A₁.card : ℝ) * r ^ n < q ^ n + 1 := by
    have hpos : 0 < r ^ n := pow_pos (by linarith) n
    nlinarith [hmn, hpos]
  have : ‖((q : ℂ) ^ n + 1)‖ = q ^ n + 1 := by
    rw [show ((q : ℂ) ^ n + 1) = ((q ^ n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hqdef] at this
  push_cast at this
  rw [hE] at this
  linarith

end WeilRH.NLinesGeometry
