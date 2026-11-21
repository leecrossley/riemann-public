/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.AW4Forms
import WeilRH.Deninger
import WeilRH.DedekindZetaConv

/-!
# The order formula: `thm:main-general`, `thm:A-schemes` (ii)–(iii), `thm:main-number-fields`

Source: `latex/notes.tex`, `def:graded-realization`, `thm:main-general`, `thm:A-schemes`,
`thm:main-number-fields` (first sentence).

A graded spectral realization of type `(d, w)` of a meromorphic `Z ≢ 0` is a family of spectral
cores `(V^j, Θ_j)`, `0 ≤ j ≤ 2d`, with
`div Z = ∑_j (-1)^{j+1} ∑_ρ dim V^j_{Θ∼ρ} [ρ]`. It is polarized if each `(V^j, Θ_j)` carries a
positive infinitesimal polarization of weight `w + j`. `thm:main-general`: then each `Θ_j` is
diagonalizable with eigenvalues on `Re s = (w + j)/2`, and
`ord_ρ Z = (-1)^{j+1} dim ker(Θ_j - ρ)` if `2 Re ρ - w = j ∈ {0, …, 2d}`, and `0` otherwise.

## Encoding

* `div Z` is Mathlib's `MeromorphicOn.divisor Z Set.univ`, whose value at `ρ` is
  `(meromorphicOrderAt Z ρ).untop₀` when `Z` is meromorphic on `ℂ`.
* `Z ≢ 0` is `∃ z, meromorphicOrderAt Z z ≠ ⊤` (`Z` is not locally zero); on the connected `ℂ`
  this makes every order finite, so the divisor statement is the order statement.
* The pieces are a family `V : ℕ → Type u`; only `j ≤ 2d` enters the divisor identity and the
  polarization, the other pieces are ignored.
* `dim V^j_{Θ∼ρ}` is `Spectral.mult (Θ j) ρ`.

## Main results

* `MainGeneral.GradedRealization`, `MainGeneral.Polarization` (`def:graded-realization`).
* `MainGeneral.iSup_eigenspace`, `MainGeneral.re_eq_of_hasEigenvalue` (purity, diagonalizability).
* `MainGeneral.divisor_eq_of_line`, `divisor_eq_zero_of_off`, `meromorphicOrderAt_eq_of_line`,
  `meromorphicOrderAt_eq_zero_of_off` (**`thm:main-general`, order formula**).
* `MainGeneral.exists_odd_of_divisor_pos`, `exists_even_of_divisor_neg`, `mult_eq_of_line`:
  zeros on odd lines, poles on even lines, each spectral divisor determined by `Z`.
* `MainGeneral.ofWeightedAlgebraDatum`, `MainGeneral.aschemes_ord`, `aschemes_ord_off`,
  `aschemes_zero`, `aschemes_pole`, `aschemes_mult` (**`thm:A-schemes` (ii)–(iii)**), and the
  polarized Deninger structure form `MainGeneral.ofDeninger`.
* `MainGeneral.re_eq_half_of_xi_eq_zero` (**`thm:main-number-fields`, first sentence**):
  conditional on `DedekindContinuation K` with simple poles, as everywhere in this tree;
  `MainGeneral.riemannHypothesis_of_realization` is the case `K = ℚ`, unconditional.
-/

open Module Complex Filter Topology

universe u

namespace WeilRH

namespace MainGeneral

/-- **`def:graded-realization` (a).** A graded spectral realization of type `(d, w)` of `Z`:
spectral cores `(V^j, Θ_j)` with `div Z = ∑_{j=0}^{2d} (-1)^{j+1} ∑_ρ dim V^j_{Θ∼ρ} [ρ]`. The
weight `w` imposes nothing until a polarization is required. -/
structure GradedRealization (d : ℕ) (w : ℝ) (Z : ℂ → ℂ) where
  /-- The piece `V^j`. -/
  V : ℕ → Type u
  [instAdd : ∀ j, AddCommGroup (V j)]
  [instMod : ∀ j, Module ℂ (V j)]
  /-- The generator `Θ_j`. -/
  Θ : ∀ j, Module.End ℂ (V j)
  /-- Each `(V^j, Θ_j)` is a spectral core. -/
  spectralCore : ∀ j, Spectral.SpectralCore (Θ j)
  /-- The divisor identity. -/
  divisor_eq : ∀ ρ : ℂ, MeromorphicOn.divisor Z Set.univ ρ =
    ∑ j ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ (j + 1) * (Spectral.mult (Θ j) ρ : ℤ)

attribute [instance] GradedRealization.instAdd GradedRealization.instMod

variable {d : ℕ} {w : ℝ} {Z : ℂ → ℂ}

/-- **`def:graded-realization` (b).** A polarization: positive infinitesimal polarizations of
weight `w + j` on `(V^j, Θ_j)`, `0 ≤ j ≤ 2d`. -/
structure Polarization (R : GradedRealization.{u} d w Z) where
  /-- The positive definite Hermitian form `h_j`. -/
  h : ∀ j, PosHermForm (R.V j)
  /-- `h_j(Θu, v) + h_j(u, Θv) = (w + j) h_j(u, v)`. -/
  isInfPol : ∀ j ≤ 2 * d, Suspension.IsInfPol (h j) (R.Θ j) (w + j)

variable {R : GradedRealization.{u} d w Z} (P : Polarization R)

include P

lemma aw4E {j : ℕ} (hj : j ≤ 2 * d) : AW4Forms.AW4E (R.Θ j) (w + j) :=
  AW4Forms.aw4E_of_aw4V (R.spectralCore j) ⟨P.h j, P.isInfPol j hj⟩

/-- **`thm:main-general`, diagonalizability.** -/
theorem iSup_eigenspace {j : ℕ} (hj : j ≤ 2 * d) : ⨆ ρ, (R.Θ j).eigenspace ρ = ⊤ :=
  AW4Forms.iSup_eigenspace_eq_top (aw4E P hj)

/-- **`thm:main-general`, purity.** Every eigenvalue of `Θ_j` has real part `(w + j)/2`. -/
theorem re_eq_of_hasEigenvalue {j : ℕ} (hj : j ≤ 2 * d) {ρ : ℂ}
    (hρ : (R.Θ j).HasEigenvalue ρ) : ρ.re = (w + j) / 2 :=
  AW4Forms.re_eq_half (aw4E P hj) hρ

lemma mult_eq_finrank_eigenspace {j : ℕ} (hj : j ≤ 2 * d) (ρ : ℂ) :
    Spectral.mult (R.Θ j) ρ = finrank ℂ ((R.Θ j).eigenspace ρ) := by
  unfold Spectral.mult
  rw [AW4Forms.maxGenEigenspace_eq_eigenspace (aw4E P hj) ρ]

lemma mult_eq_zero {j : ℕ} (hj : j ≤ 2 * d) {ρ : ℂ} (hρ : 2 * ρ.re - w ≠ j) :
    Spectral.mult (R.Θ j) ρ = 0 := by
  rw [mult_eq_finrank_eigenspace P hj]
  suffices h : (R.Θ j).eigenspace ρ = ⊥ by rw [h, finrank_bot]
  by_contra hne
  have := re_eq_of_hasEigenvalue P hj (Module.End.hasEigenvalue_iff.2 hne)
  exact hρ (by linarith)

/-- **`thm:main-general`, order formula on the lines.** If `2 Re ρ - w = j ∈ {0, …, 2d}`, then
`div Z (ρ) = (-1)^{j+1} dim ker(Θ_j - ρ)`. -/
theorem divisor_eq_of_line {ρ : ℂ} {j : ℕ} (hj : j ≤ 2 * d) (hρ : 2 * ρ.re - w = j) :
    MeromorphicOn.divisor Z Set.univ ρ =
      (-1 : ℤ) ^ (j + 1) * (finrank ℂ ((R.Θ j).eigenspace ρ) : ℤ) := by
  rw [R.divisor_eq, Finset.sum_eq_single j]
  · rw [mult_eq_finrank_eigenspace P hj]
  · intro k hk hkj
    rw [Finset.mem_range] at hk
    rw [mult_eq_zero P (by omega) (ρ := ρ) ?_]
    · simp
    · intro h
      apply hkj
      have : (k : ℝ) = j := by linarith
      exact_mod_cast this
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- **`thm:main-general`, order formula off the lines.** -/
theorem divisor_eq_zero_of_off {ρ : ℂ} (hρ : ∀ j ≤ 2 * d, 2 * ρ.re - w ≠ j) :
    MeromorphicOn.divisor Z Set.univ ρ = 0 := by
  rw [R.divisor_eq]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [mult_eq_zero P (by omega) (hρ k (by omega))]
  simp

omit P in
lemma meromorphicOrderAt_eq_divisor (hZ : MeromorphicOn Z Set.univ)
    (hZ0 : ∃ z, meromorphicOrderAt Z z ≠ ⊤) (ρ : ℂ) :
    meromorphicOrderAt Z ρ = (MeromorphicOn.divisor Z Set.univ ρ : WithTop ℤ) := by
  obtain ⟨z, hz⟩ := hZ0
  have hne : meromorphicOrderAt Z ρ ≠ ⊤ :=
    hZ.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ z)
      (Set.mem_univ ρ) hz
  rw [MeromorphicOn.divisor_apply hZ (Set.mem_univ ρ), WithTop.coe_untop₀_of_ne_top hne]

/-- **`thm:main-general`** as stated, with `ord_ρ Z`: on the line `2 Re ρ - w = j`. -/
theorem meromorphicOrderAt_eq_of_line (hZ : MeromorphicOn Z Set.univ)
    (hZ0 : ∃ z, meromorphicOrderAt Z z ≠ ⊤) {ρ : ℂ} {j : ℕ} (hj : j ≤ 2 * d)
    (hρ : 2 * ρ.re - w = j) :
    meromorphicOrderAt Z ρ = (((-1 : ℤ) ^ (j + 1) * (finrank ℂ ((R.Θ j).eigenspace ρ) : ℤ) : ℤ) :
      WithTop ℤ) := by
  rw [meromorphicOrderAt_eq_divisor hZ hZ0, divisor_eq_of_line P hj hρ]

/-- **`thm:main-general`** as stated, with `ord_ρ Z`: off the lines. -/
theorem meromorphicOrderAt_eq_zero_of_off (hZ : MeromorphicOn Z Set.univ)
    (hZ0 : ∃ z, meromorphicOrderAt Z z ≠ ⊤) {ρ : ℂ} (hρ : ∀ j ≤ 2 * d, 2 * ρ.re - w ≠ j) :
    meromorphicOrderAt Z ρ = 0 := by
  rw [meromorphicOrderAt_eq_divisor hZ hZ0, divisor_eq_zero_of_off P hρ]
  rfl

/-- Zeros occur only on the odd-degree lines. -/
theorem exists_odd_of_divisor_pos {ρ : ℂ} (h : 0 < MeromorphicOn.divisor Z Set.univ ρ) :
    ∃ j ≤ 2 * d, Odd j ∧ 2 * ρ.re - w = j := by
  by_cases hl : ∃ j ≤ 2 * d, 2 * ρ.re - w = j
  · obtain ⟨j, hj, hρ⟩ := hl
    refine ⟨j, hj, ?_, hρ⟩
    rw [divisor_eq_of_line P hj hρ] at h
    rcases Nat.even_or_odd j with he | ho
    · rw [(he.add_one).neg_one_pow] at h
      have : (0 : ℤ) ≤ (finrank ℂ ((R.Θ j).eigenspace ρ) : ℤ) := by positivity
      linarith
    · exact ho
  · push Not at hl
    rw [divisor_eq_zero_of_off P hl] at h
    exact absurd h (lt_irrefl 0)

/-- Poles occur only on the even-degree lines. -/
theorem exists_even_of_divisor_neg {ρ : ℂ} (h : MeromorphicOn.divisor Z Set.univ ρ < 0) :
    ∃ j ≤ 2 * d, Even j ∧ 2 * ρ.re - w = j := by
  by_cases hl : ∃ j ≤ 2 * d, 2 * ρ.re - w = j
  · obtain ⟨j, hj, hρ⟩ := hl
    refine ⟨j, hj, ?_, hρ⟩
    rw [divisor_eq_of_line P hj hρ] at h
    rcases Nat.even_or_odd j with he | ho
    · exact he
    · rw [(ho.add_one).neg_one_pow] at h
      have : (0 : ℤ) ≤ (finrank ℂ ((R.Θ j).eigenspace ρ) : ℤ) := by positivity
      linarith
  · push Not at hl
    rw [divisor_eq_zero_of_off P hl] at h
    exact absurd h (lt_irrefl 0)

/-- **No cancellation: `Z` determines each spectral divisor.** On the line `2 Re ρ - w = j`,
`dim V^j_{Θ∼ρ} = (-1)^{j+1} div Z (ρ)`; off it, `dim V^j_{Θ∼ρ} = 0`. -/
theorem mult_eq_of_line {ρ : ℂ} {j : ℕ} (hj : j ≤ 2 * d) (hρ : 2 * ρ.re - w = j) :
    (Spectral.mult (R.Θ j) ρ : ℤ) = (-1 : ℤ) ^ (j + 1) * MeromorphicOn.divisor Z Set.univ ρ := by
  rw [divisor_eq_of_line P hj hρ, mult_eq_finrank_eigenspace P hj, ← mul_assoc, ← pow_add]
  have : Even (j + 1 + (j + 1)) := ⟨j + 1, rfl⟩
  rw [this.neg_one_pow, one_mul]

end MainGeneral

/-! ### `thm:A-schemes`: a positive Weil datum of type `(d, 0)` with AW2 -/

namespace MainGeneral

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ} {w : ℝ} {Z : ℂ → ℂ}

/-- A graded positive datum (`WeightedAlgebraDatum`: derivation rule of AW1, trace equivariance of
AW3, AW4) satisfying AW2 for `Z` is a graded spectral realization of type `(d, w)` of `Z`. -/
def ofWeightedAlgebraDatum (D : WeightedAlgebraDatum V d w)
    (hdiv : ∀ ρ : ℂ, MeromorphicOn.divisor Z Set.univ ρ =
      ∑ j ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ (j + 1) * (Spectral.mult (D.Θr j) ρ : ℤ)) :
    GradedRealization.{u} d w Z where
  V j := D.G j
  Θ := D.Θr
  spectralCore := D.spectralCore
  divisor_eq := hdiv

/-- `prop:polarization-identity`: the forms `h_j` polarize it. -/
def ofWeightedAlgebraDatum.polarization (D : WeightedAlgebraDatum V d w)
    (hdiv : ∀ ρ : ℂ, MeromorphicOn.divisor Z Set.univ ρ =
      ∑ j ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ (j + 1) * (Spectral.mult (D.Θr j) ρ : ℤ)) :
    Polarization (ofWeightedAlgebraDatum D hdiv) where
  h := D.form
  isInfPol j _ := D.form_P j

variable (D : WeightedAlgebraDatum V d 0)
  (hdiv : ∀ ρ : ℂ, MeromorphicOn.divisor Z Set.univ ρ =
    ∑ j ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ (j + 1) * (Spectral.mult (D.Θr j) ρ : ℤ))

include D hdiv

/-- **`thm:A-schemes` (ii), on the lines.** For `j = 2 Re ρ ∈ {0, …, 2d}`,
`ord_ρ Z = (-1)^{j+1} m_j(ρ)`. -/
theorem aschemes_ord (hZ : MeromorphicOn Z Set.univ) (hZ0 : ∃ z, meromorphicOrderAt Z z ≠ ⊤)
    {ρ : ℂ} {j : ℕ} (hj : j ≤ 2 * d) (hρ : 2 * ρ.re = j) :
    meromorphicOrderAt Z ρ = (((-1 : ℤ) ^ (j + 1) * (Spectral.mult (D.Θr j) ρ : ℤ) : ℤ) :
      WithTop ℤ) := by
  have P := ofWeightedAlgebraDatum.polarization D hdiv
  have hρ' : 2 * ρ.re - 0 = j := by simpa using hρ
  rw [meromorphicOrderAt_eq_of_line P hZ hZ0 hj hρ', ← mult_eq_finrank_eigenspace P hj]
  rfl

/-- **`thm:A-schemes` (ii), off the lines.** `Z` has no zero or pole with
`2 Re ρ ∉ {0, …, 2d}`. -/
theorem aschemes_ord_off (hZ : MeromorphicOn Z Set.univ) (hZ0 : ∃ z, meromorphicOrderAt Z z ≠ ⊤)
    {ρ : ℂ} (hρ : ∀ j ≤ 2 * d, 2 * ρ.re ≠ j) : meromorphicOrderAt Z ρ = 0 :=
  meromorphicOrderAt_eq_zero_of_off (ofWeightedAlgebraDatum.polarization D hdiv) hZ hZ0
    fun j hj h => hρ j hj (by simpa using h)

/-- **`thm:A-schemes` (iii), zeros.** Every zero of `Z` has real part `j/2` with `j` odd,
`j ≤ 2d`, i.e. in `{1/2, 3/2, …, (2d-1)/2}`. -/
theorem aschemes_zero {ρ : ℂ} (h : 0 < MeromorphicOn.divisor Z Set.univ ρ) :
    ∃ j ≤ 2 * d, Odd j ∧ 2 * ρ.re = j := by
  simpa using exists_odd_of_divisor_pos (ofWeightedAlgebraDatum.polarization D hdiv) h

/-- **`thm:A-schemes` (iii), poles.** Every pole of `Z` has real part in `{0, 1, …, d}`. -/
theorem aschemes_pole {ρ : ℂ} (h : MeromorphicOn.divisor Z Set.univ ρ < 0) :
    ∃ j ≤ 2 * d, Even j ∧ 2 * ρ.re = j := by
  simpa using exists_even_of_divisor_neg (ofWeightedAlgebraDatum.polarization D hdiv) h

/-- **`thm:A-schemes` (iii), `Z` determines every spectral divisor `Sp_j`.** -/
theorem aschemes_mult {ρ : ℂ} {j : ℕ} (hj : j ≤ 2 * d) (hρ : 2 * ρ.re = j) :
    (Spectral.mult (D.Θr j) ρ : ℤ) = (-1 : ℤ) ^ (j + 1) * MeromorphicOn.divisor Z Set.univ ρ :=
  mult_eq_of_line (ofWeightedAlgebraDatum.polarization D hdiv) hj (by simpa using hρ)

omit D hdiv in
/-- **`thm:A-schemes` for a polarized Deninger structure** (AW1 for `𝟙`, AW3 perfectness, AW4):
it is a polarized graded spectral realization of type `(d, 0)` of any `Z` it realizes (AW2). -/
def ofDeninger {U : Type*} [CommRing U] [Algebra ℂ U] {ΘU : Module.End ℂ U}
    {E : DeningerStructure V d U ΘU} (P : E.Polarization)
    (hdiv : ∀ ρ : ℂ, MeromorphicOn.divisor Z Set.univ ρ =
      ∑ j ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ (j + 1) *
        (Spectral.mult (P.toWeightedAlgebraDatum.Θr j) ρ : ℤ)) :
    Polarization (ofWeightedAlgebraDatum P.toWeightedAlgebraDatum hdiv) :=
  ofWeightedAlgebraDatum.polarization _ hdiv

end MainGeneral

/-! ### `thm:main-number-fields`, first sentence -/

namespace MainGeneral

open DedekindZetaConv

variable {K : Type*} [Field K] [NumberField K] {C : DedekindContinuation K}

/-- `Λ_K` is meromorphic on `ℂ` (given its continuation with simple poles). -/
theorem meromorphicOn_Λ (P : C.SimplePoles) : MeromorphicOn C.Λ Set.univ := by
  intro x _
  by_cases hx : x = 0 ∨ x = 1
  · have hm : MeromorphicAt (fun s => P.ξ s / (s * (s - 1))) x :=
      (P.differentiable.analyticAt x).meromorphicAt.div
        ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).meromorphicAt)
    refine hm.congr ?_
    have hev : ∀ᶠ s in 𝓝[≠] x, s ≠ 0 ∧ s ≠ 1 := by
      rcases hx with rfl | rfl
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds ((isOpen_ne_fun continuous_id continuous_const).mem_nhds
            (by norm_num : (0 : ℂ) ≠ 1))] with s hs h1
        exact ⟨hs, h1⟩
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds ((isOpen_ne_fun continuous_id continuous_const).mem_nhds
            (by norm_num : (1 : ℂ) ≠ 0))] with s hs h0
        exact ⟨h0, hs⟩
    filter_upwards [hev] with s ⟨h0, h1⟩
    rw [P.eq_xiK s h0 h1, xiK]
    have : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
    field_simp
  · push Not at hx
    have hmem : x ∈ ({0, 1}ᶜ : Set ℂ) := by simp [hx.1, hx.2]
    exact ((C.differentiableOn.analyticOnNhd DedekindContinuation.isOpen_compl) x hmem).meromorphicAt

lemma analyticAt_Λ {x : ℂ} (h0 : x ≠ 0) (h1 : x ≠ 1) : AnalyticAt ℂ C.Λ x :=
  (C.differentiableOn.analyticOnNhd DedekindContinuation.isOpen_compl) x (by simp [h0, h1])

/-- `Λ_K ≢ 0`: its order at `2` is finite. -/
theorem exists_meromorphicOrderAt_Λ_ne_top (P : C.SimplePoles) :
    ∃ z, meromorphicOrderAt C.Λ z ≠ ⊤ := by
  refine ⟨2, ?_⟩
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h21 : (2 : ℂ) ≠ 1 := by norm_num
  rw [(analyticAt_Λ h2 h21).meromorphicOrderAt_eq]
  have hΛ : C.Λ 2 ≠ 0 := by
    have := xi_ne_zero_of_real P (x := 2) (by norm_num)
    push_cast at this
    rw [P.eq_xiK 2 h2 h21, xiK] at this
    exact right_ne_zero_of_mul this
  rw [(analyticAt_Λ h2 h21).analyticOrderAt_eq_zero.2 hΛ]
  simp

/-- At a zero `ρ` of `ξ_K` (a nontrivial zero of `ζ_K`), `div Λ_K (ρ) > 0`. -/
theorem divisor_Λ_pos (P : C.SimplePoles) {ρ : ℂ} (hρ : P.ξ ρ = 0) :
    0 < MeromorphicOn.divisor C.Λ Set.univ ρ := by
  obtain ⟨hΛ, h0, h1⟩ := (P.xi_eq_zero_iff ρ).1 hρ
  have hA := analyticAt_Λ (C := C) h0 h1
  have hne : meromorphicOrderAt C.Λ ρ ≠ ⊤ := by
    obtain ⟨z, hz⟩ := exists_meromorphicOrderAt_Λ_ne_top P
    exact (meromorphicOn_Λ P).meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z) (Set.mem_univ ρ) hz
  rw [MeromorphicOn.divisor_apply (meromorphicOn_Λ P) (Set.mem_univ ρ)]
  rw [hA.meromorphicOrderAt_eq] at hne ⊢
  have hpos : analyticOrderAt C.Λ ρ ≠ 0 := hA.analyticOrderAt_ne_zero.2 hΛ
  have htop : analyticOrderAt C.Λ ρ ≠ ⊤ := by
    intro h; rw [h] at hne; exact hne rfl
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← hn] at hpos ⊢
  have : n ≠ 0 := by rintro rfl; exact hpos rfl
  simp only [ENat.map_natCast, WithTop.untop₀_coe]
  exact_mod_cast Nat.pos_of_ne_zero this

/-- **`thm:main-number-fields`, first sentence.** If `Λ_K` has a polarized graded spectral
realization of type `(1, 0)` with endpoint data `(V^0, Θ_0) = (ℂ, 0)`, `(V^2, Θ_2) = (ℂ, 1)`,
every nontrivial zero of `ζ_K` (a zero of `ξ_K`) has real part `1/2`. Conditional on the
continuation `C` of `Λ_K` with simple poles `P`, as everywhere in this tree; the endpoint data are
not used. -/
theorem re_eq_half_of_xi_eq_zero (P : C.SimplePoles) {R : GradedRealization.{u} 1 0 C.Λ}
    (Q : Polarization R) (_e0 : R.V 0 ≃ₗ[ℂ] ℂ) (_e2 : R.V 2 ≃ₗ[ℂ] ℂ) {ρ : ℂ} (hρ : P.ξ ρ = 0) :
    ρ.re = 1 / 2 := by
  obtain ⟨j, hj, ho, hl⟩ := exists_odd_of_divisor_pos Q (divisor_Λ_pos P hρ)
  have : j = 1 := by
    rcases ho with ⟨k, rfl⟩
    omega
  subst this
  push_cast at hl
  linarith

/-- **`thm:main-number-fields` for `K = ℚ`: RH from a realization.** If `Λ` has a polarized graded
spectral realization of type `(1, 0)`, every zero of `ξ` has real part `1/2`. Unconditional: the
continuation of `Λ_ℚ` and its simple poles are constructed (`DedekindContinuation.SimplePoles.ofRat`). -/
theorem riemannHypothesis_of_realization
    {R : GradedRealization.{u} 1 0 DedekindContinuation.rat.Λ} (Q : Polarization R) {ρ : ℂ}
    (hρ : (DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat).ξ ρ = 0) :
    ρ.re = 1 / 2 := by
  obtain ⟨j, hj, ho, hl⟩ := exists_odd_of_divisor_pos Q
    (divisor_Λ_pos (DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat) hρ)
  have : j = 1 := by
    rcases ho with ⟨k, rfl⟩
    omega
  subst this
  push_cast at hl
  linarith

end MainGeneral

end WeilRH
