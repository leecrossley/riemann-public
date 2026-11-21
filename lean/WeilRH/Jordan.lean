/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.WeilConverse

/-!
# A Jordan block with pure eigenvalues and no positive polarization

Source: the manuscript `latex/notes.tex`, `prop:N-jordan` (with `def:frob-pol`).

For real `q > 1` and `j`, the matrix `F = [[q^(j/2), 1], [0, q^(j/2)]]` on `ℂ²` has every
eigenvalue of absolute value `q^(j/2)`, yet no positive definite Hermitian form `h` satisfies
`h(Fu, Fv) = q^j h(u, v)`.

## Main results

* `WeilRH.Jordan.norm_eq_of_hasEigenvalue`: purity of the eigenvalues.
* `WeilRH.Jordan.not_exists_polarization`: no positive Frobenius polarization of weight `j`.
* `WeilRH.Jordan.hasEigenvalue_jordanF`: `q^(j/2)` is an eigenvalue (non-vacuity).
* `WeilRH.Jordan.not_exists_frobPol`: the second clause in the encoding of `WeilConverse.lean`
  (`PosHermForm`, `IsFrobPol`), by the manuscript's route: `F` is not diagonalizable
  (`iSup_eigenspace_ne_top`), so `exists_frobPol_iff` (`prop:weil-converse` (i), whose forward
  direction is `prop:weil-linear`) excludes a polarization.

Hermitian forms are linear in the first argument, as in the manuscript:
`hermForm H u v = v* H u`.
-/

open Matrix
open scoped ComplexOrder

namespace WeilRH.Jordan

/-- The matrix `F = [[q^(j/2), 1], [0, q^(j/2)]]` of `prop:N-jordan`. -/
noncomputable def jordanF (q j : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((q ^ (j / 2) : ℝ) : ℂ), 1; 0, ((q ^ (j / 2) : ℝ) : ℂ)]

/-- The Hermitian form of `H`, linear in the first argument: `h(u, v) = v* H u`. -/
def hermForm (H : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ) : ℂ := star v ⬝ᵥ (H *ᵥ u)

/-- The only eigenvalue of `F` is `q^(j/2)`. -/
theorem eq_of_hasEigenvalue {q j : ℝ} {α : ℂ}
    (hα : Module.End.HasEigenvalue (Matrix.toLin' (jordanF q j)) α) :
    α = ((q ^ (j / 2) : ℝ) : ℂ) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hFv := hv.apply_eq_smul
  have hne := hv.2
  rw [Matrix.toLin'_apply] at hFv
  have h0 := congrFun hFv 0
  have h1 := congrFun hFv 1
  simp [jordanF, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro hv0; apply hne; ext i; fin_cases i <;> simp [hv0, hv1]
    rw [hv1, add_zero] at h0
    exact (mul_right_cancel₀ hv0 h0).symm
  · exact (h1.resolve_right hv1).symm

/-- **`prop:N-jordan`**, first clause: every eigenvalue `α` of `F` has `|α| = q^(j/2)`. -/
theorem norm_eq_of_hasEigenvalue {q j : ℝ} (hq : 1 < q) {α : ℂ}
    (hα : Module.End.HasEigenvalue (Matrix.toLin' (jordanF q j)) α) :
    ‖α‖ = q ^ (j / 2) := by
  have hα := eq_of_hasEigenvalue hα
  rw [hα, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]

/-- **`prop:N-jordan`**, second clause: `(ℂ², F)` admits no positive Frobenius polarization of
weight `j` (`def:frob-pol`). A positive definite Hermitian form on `ℂ²` is `hermForm H` for a
positive definite matrix `H`. The proof evaluates the polarization identity at `(e₁, e₀)`, which
forces `h(e₀, e₀) = 0`; the manuscript instead cites `prop:weil-linear` (formalized as
`WeilRH.isSemisimple_of_weil`). -/
theorem not_exists_polarization {q j : ℝ} (hq : 1 < q) :
    ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧ ∀ u v,
      hermForm H (jordanF q j *ᵥ u) (jordanF q j *ᵥ v) = ((q ^ j : ℝ) : ℂ) * hermForm H u v := by
  rintro ⟨H, hH, hF⟩
  have key := hF (Pi.single 1 1) (Pi.single 0 1)
  have ha : (q ^ (j / 2) : ℝ) * q ^ (j / 2) = q ^ j := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hpos : 0 < (q ^ (j / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  simp [hermForm, jordanF, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] at key
  have hsq : ((q ^ j : ℝ) : ℂ) = ((q ^ (j / 2) : ℝ) : ℂ) * ((q ^ (j / 2) : ℝ) : ℂ) := by
    rw [← ha]; push_cast; ring
  rw [hsq] at key
  have h00 : ((q ^ (j / 2) : ℝ) : ℂ) * H 0 0 = 0 := by linear_combination key
  have hne : ((q ^ (j / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  have hH00 := hH.diag_pos (i := 0)
  rw [(mul_eq_zero.1 h00).resolve_left hne] at hH00
  exact lt_irrefl _ hH00

/-- `q^(j/2)` is an eigenvalue of `F`, so the first clause of `prop:N-jordan` is not vacuous. -/
theorem hasEigenvalue_jordanF (q j : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' (jordanF q j)) ((q ^ (j / 2) : ℝ) : ℂ) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single 0 1) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i; fin_cases i <;> simp [jordanF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp
/-- `F` is not diagonalizable: its eigenspaces do not span `ℂ²`. -/
theorem iSup_eigenspace_ne_top (q j : ℝ) :
    ⨆ α, Module.End.eigenspace (Matrix.toLin' (jordanF q j)) α ≠ ⊤ := by
  set F : Module.End ℂ (Fin 2 → ℂ) := Matrix.toLin' (jordanF q j)
  set a : ℂ := ((q ^ (j / 2) : ℝ) : ℂ)
  have hle : ⨆ α, F.eigenspace α ≤ F.eigenspace a := by
    refine iSup_le fun α => ?_
    by_cases hα : α = a
    · rw [hα]
    · have : F.eigenspace α = ⊥ := by
        by_contra h
        exact hα (eq_of_hasEigenvalue (Module.End.hasEigenvalue_iff.2 h))
      rw [this]; exact bot_le
  intro htop
  have hmem : (Pi.single 1 1 : Fin 2 → ℂ) ∈ F.eigenspace a := hle (htop ▸ Submodule.mem_top)
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hmem
  have := congrFun hmem 0
  simp [jordanF, Matrix.mulVec, dotProduct, Pi.single_apply] at this

/-- **`prop:N-jordan`**, second clause, by the manuscript's route: `F` has the single eigenvalue
`q^(j/2)` and is not diagonalizable, and `prop:weil-converse` (i) (`exists_frobPol_iff`, whose
forward direction is `prop:weil-linear`) then excludes a positive Frobenius polarization. -/
theorem not_exists_frobPol {q j : ℝ} (hq : 1 < q) :
    ¬ ∃ h : PosHermForm (Fin 2 → ℂ), IsFrobPol h (Matrix.toLin' (jordanF q j)) q j := by
  rw [exists_frobPol_iff _ hq j]
  exact fun ⟨hdiag, _⟩ => iSup_eigenspace_ne_top q j hdiag

end WeilRH.Jordan
