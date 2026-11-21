/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ZetaZerosRvM
import WeilRH.Completed

/-!
# `prop:P1Z`, zero clauses (round 74)

Source: `latex/notes.tex`, Proposition `prop:P1Z`. For `X = ℙ¹_ℤ`, `ζ_X(s) = ζ(s) ζ(s-1)`; the
zeros of `ζ_X` in `0 < Re s < 2` are exactly `Z ∪ (Z + 1)`, `Z` the nontrivial zeros of `ζ`;
`Z` is nonempty, `Z ⊆ {0 < Re s < 1}` and `Z + 1 ⊆ {1 < Re s < 2}`; no vertical line contains all
zeros of `ζ_X` in `0 < Re s < 2`.

## Encoding

* The product formula `ζ_X = ζ(s) ζ(s-1)` needs a scheme-level zeta of `ℙ¹_ℤ` and is open
  (README obligation 32). Here `ζ_X` is the function `zetaP1 s = ζ(s) ζ(s-1)`.
* The poles `s = 1, 2` of `ζ_X` are excluded (Mathlib's `riemannZeta 1` is a junk value).
* Nonemptiness of `Z` and the vertical-line clause use B6 (`RiemannVonMangoldt`) as an explicit
  hypothesis; the zero description and the strip clauses are unconditional.
-/

namespace WeilRH.P1ZZeros

open Complex

/-- `ζ_{ℙ¹_ℤ}(s) = ζ(s) ζ(s - 1)` (the product formula itself is not proved here). -/
noncomputable def zetaP1 (s : ℂ) : ℂ := riemannZeta s * riemannZeta (s - 1)

/-- Nontrivial zeros of `ζ` lie in the open strip `0 < Re s < 1`. -/
theorem re_mem_Ioo {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hlt : ∀ {z : ℂ}, IsNontrivialZetaZero z → z.re < 1 := fun {z} hz => by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h) hz.1
  refine ⟨?_, hlt hρ⟩
  have h1 : completedXi (1 - ρ) = 0 := by
    rw [completedXi_one_sub, completedXi_eq_zero_iff]; exact hρ
  have := hlt ((completedXi_eq_zero_iff _).1 h1)
  simp at this
  linarith

lemma not_trivial_of_re_pos {s : ℂ} (hs : -2 < s.re) : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩
  simp at hs
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **`prop:P1Z`, zeros.** For `0 < Re s < 2`, `s ≠ 1, 2`: `ζ_X(s) = 0` iff `s ∈ Z ∪ (Z + 1)`. -/
theorem zetaP1_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (_h2 : s.re < 2) (hs1 : s ≠ 1) (hs2 : s ≠ 2) :
    zetaP1 s = 0 ↔ IsNontrivialZetaZero s ∨ IsNontrivialZetaZero (s - 1) := by
  unfold zetaP1
  rw [mul_eq_zero]
  refine or_congr ⟨fun h => ⟨h, not_trivial_of_re_pos (by linarith), hs1⟩, fun h => h.1⟩
    ⟨fun h => ⟨h, not_trivial_of_re_pos (by simp; linarith), fun h' => hs2 (by
      linear_combination h')⟩, fun h => h.1⟩

/-- `Z + 1` lies in `1 < Re s < 2`. -/
theorem re_mem_Ioo_add_one {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    1 < (ρ + 1).re ∧ (ρ + 1).re < 2 := by
  have := re_mem_Ioo hρ
  simp; constructor <;> linarith

/-- **`Z` is nonempty** (under B6). -/
theorem nonempty (hB : RiemannVonMangoldt) : ∃ ρ : ℂ, IsNontrivialZetaZero ρ := by
  obtain ⟨ρ, h0, h1, h2⟩ := RvM.exists_nontrivial_zero hB
  exact ⟨ρ, h0, not_trivial_of_re_pos (by linarith), fun h => by rw [h] at h2; simp at h2⟩

/-- **No vertical line contains all zeros of `ζ_X` in `0 < Re s < 2`** (under B6). -/
theorem no_vertical_line (hB : RiemannVonMangoldt) (σ : ℝ) :
    ∃ s : ℂ, 0 < s.re ∧ s.re < 2 ∧ s ≠ 1 ∧ s ≠ 2 ∧ zetaP1 s = 0 ∧ s.re ≠ σ := by
  obtain ⟨ρ, hρ⟩ := nonempty hB
  have hI := re_mem_Ioo hρ
  have hρ1 : ρ ≠ 1 := hρ.2.2
  have hρ2 : ρ ≠ 2 := fun h => by rw [h] at hI; norm_num at hI
  have hz : zetaP1 ρ = 0 :=
    (zetaP1_eq_zero_iff hI.1 (by linarith) hρ1 hρ2).2 (Or.inl hρ)
  have hJ := re_mem_Ioo_add_one hρ
  have hz' : zetaP1 (ρ + 1) = 0 := by
    refine (zetaP1_eq_zero_iff (by linarith) hJ.2 ?_ ?_).2 (Or.inr (by simpa using hρ))
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; apply hρ1; linear_combination h
  by_cases hσ : ρ.re = σ
  · refine ⟨ρ + 1, by linarith, hJ.2, ?_, ?_, hz', ?_⟩
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; apply hρ1; linear_combination h
    · simp; linarith
  · exact ⟨ρ, hI.1, by linarith, hρ1, hρ2, hz, hσ⟩

end WeilRH.P1ZZeros
