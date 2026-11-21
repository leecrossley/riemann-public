/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ConverseCore

/-!
# Zero orders of `ξ` and `ζ` agree at the nontrivial zeros

Source: `latex/notes.tex`, `prop:converse` ("`spec Θ` with multiplicities is the multiset of
nontrivial zeros of `ζ`"). Round 65 encodes the multiplicity of `ρ` as `ord_ρ ξ`. Here we prove
that at a nontrivial zero `ord_ρ ξ = ord_ρ ζ`, and that `ord_ρ ξ = 0` elsewhere, so the encoding is
the multiset of nontrivial zeros of `ζ` counted with their `ζ`-multiplicity.

Near a nontrivial zero `ρ` (`ρ ≠ 0, 1`), `ζ(s) = h(s) ξ(s)` with
`h(s) = 2 Γ_ℝ(s)⁻¹ / (s (s - 1))`, analytic at `ρ` (`1/Γ_ℝ` is entire) and nonzero there
(`Γ_ℝ(ρ) ≠ 0` because `ρ` is not a trivial zero).

## Main results

* `WeilRH.analyticOrderAt_riemannZeta_eq_completedXi`, `analyticOrderNatAt_riemannZeta_eq_completedXi`.
* `WeilRH.analyticOrderNatAt_completedXi_eq` : `ord_ρ ξ = if ρ is a nontrivial zero then ord_ρ ζ else 0`.
* `WeilRH.PositiveZetaCore.mult_eq_zeta`: `prop:converse` (ii) with `ζ`-multiplicities.
-/

open Complex Filter Topology

namespace WeilRH

lemma ne_zero_of_isNontrivialZetaZero {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) : ρ ≠ 0 := by
  rintro rfl
  have := hρ.1
  rw [riemannZeta_zero] at this
  norm_num at this

lemma Gammaℝ_ne_zero_of_isNontrivialZetaZero {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    Gammaℝ ρ ≠ 0 := by
  intro h
  obtain ⟨n, rfl⟩ := Gammaℝ_eq_zero_iff.1 h
  rcases n with _ | n
  · exact ne_zero_of_isNontrivialZetaZero hρ (by simp)
  · exact hρ.2.1 ⟨n, by push_cast; ring⟩

/-- `ζ = h ξ` off `{0, 1}`, with `h(s) = 2 Γ_ℝ(s)⁻¹ / (s (s - 1))`. -/
lemma riemannZeta_eq_mul_completedXi {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannZeta s = (2 * (Gammaℝ s)⁻¹ / (s * (s - 1))) * completedXi s := by
  rw [completedXi_eq h0 h1, riemannZeta_def_of_ne_zero h0]
  have : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  field_simp

/-- **At a nontrivial zero, `ord_ρ ζ = ord_ρ ξ`.** -/
theorem analyticOrderAt_riemannZeta_eq_completedXi {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt completedXi ρ := by
  have h0 := ne_zero_of_isNontrivialZetaZero hρ
  have h1 := hρ.2.2
  set h : ℂ → ℂ := fun s => 2 * (Gammaℝ s)⁻¹ / (s * (s - 1)) with hh
  have hden : ρ * (ρ - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  have hA : AnalyticAt ℂ h ρ := by
    have hinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
    exact (analyticAt_const.mul hinv).div
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) hden
  have hne : h ρ ≠ 0 := by
    simp only [hh]
    exact div_ne_zero (mul_ne_zero two_ne_zero
      (inv_ne_zero (Gammaℝ_ne_zero_of_isNontrivialZetaZero hρ))) hden
  have hev : riemannZeta =ᶠ[𝓝 ρ] h * completedXi := by
    have hU : IsOpen ({0, 1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
    filter_upwards [hU.mem_nhds (by simp [h0, h1])] with s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    simp only [Pi.mul_apply, hh]
    exact riemannZeta_eq_mul_completedXi hs.1 hs.2
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hA (analyticAt_completedXi ρ),
    hA.analyticOrderAt_eq_zero.2 hne, zero_add]

/-- **At a nontrivial zero, `ord_ρ ζ = ord_ρ ξ`** (natural-number orders). -/
theorem analyticOrderNatAt_riemannZeta_eq_completedXi {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt completedXi ρ := by
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_riemannZeta_eq_completedXi hρ]

/-- `ord_ρ ξ` is the `ζ`-multiplicity of `ρ` as a nontrivial zero, and `0` at every other point. -/
theorem analyticOrderNatAt_completedXi_eq (ρ : ℂ) [Decidable (IsNontrivialZetaZero ρ)] :
    analyticOrderNatAt completedXi ρ =
      if IsNontrivialZetaZero ρ then analyticOrderNatAt riemannZeta ρ else 0 := by
  split_ifs with hρ
  · exact (analyticOrderNatAt_riemannZeta_eq_completedXi hρ).symm
  · by_contra hne
    exact hρ ((analyticOrderNatAt_completedXi_pos_iff ρ).1 (Nat.pos_of_ne_zero hne))

/-- **`prop:converse` (ii) with `ζ`-multiplicities.** In a `PositiveZetaCore`, `spec Θ` with
multiplicities is the multiset of nontrivial zeros of `ζ`, each counted with its order as a zero
of `ζ`. -/
theorem PositiveZetaCore.mult_eq_zeta (C : PositiveZetaCore) (ρ : ℂ)
    [Decidable (IsNontrivialZetaZero ρ)] :
    Spectral.mult C.Θ ρ = if IsNontrivialZetaZero ρ then analyticOrderNatAt riemannZeta ρ else 0 := by
  rw [C.mult_eq, analyticOrderNatAt_completedXi_eq]

end WeilRH
