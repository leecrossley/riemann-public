/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import WeilRH.HbEquiv
import WeilRH.XiKZerosInfinite

/-!
# `prop:hb` and `prop:hb-high` without B6 (round 77)

The round-75 proofs of `prop:hb-high` (second clause) and `prop:hb` (i) ⇒ (ii) used B6
(Riemann–von Mangoldt) only to know that `F(z) = ξ(1/2 - iz)` has a zero. That also follows from
`Hecke.zeroIdx_infinite` at `K = ℚ` (B1 and B3, the latter from B3'), so both results hold under
B1 for `ℚ` and B3' alone (`fidelity-74-75.md`, fix 2).
-/

open Complex

namespace WeilRH

/-- Under B1 for `ℚ` and B3', `F` has a zero. -/
lemma riemannXiUpper_exists_zero_of_hecke (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU) :
    ∃ w, riemannXiUpper w = 0 := by
  haveI := Hecke.zeroIdx_infinite hB (hadamardOrderOne_of_LU hH)
  obtain i : Hecke.ZeroIdx hB := Classical.arbitrary _
  set ρ : ℂ := i.1.1
  have hρ : completedXi ρ = 0 := by
    have h := i.2.1
    rw [HeckePackage.xi_rat hB] at h
    simpa using h
  refine ⟨I * (ρ - 1 / 2), ?_⟩
  have hw : (1 / 2 : ℂ) - I * (I * (ρ - 1 / 2)) = ρ := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [riemannXiUpper, hw]; exact hρ

/-- **`prop:hb-high`, second clause**, CONDITIONAL on B1 for `ℚ` and B3' only. -/
theorem riemannXiUpper_im_neg_logDeriv_pos' (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU)
    {z : ℂ} (hz : 1 / 2 ≤ z.im) : 0 < (-logDeriv riemannXiUpper z).im :=
  riemannXiUpper_im_neg_logDeriv_pos_of_zero hB hH (riemannXiUpper_exists_zero_of_hecke hB hH) hz

/-- **`prop:hb`**, CONDITIONAL (only `(i) → (ii)`) on B1 for `ℚ` and B3'. -/
theorem Hb.hb_tfae' (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU) :
    List.TFAE
      [∀ w, riemannXiUpper w = 0 → w.im = 0,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 ∧ 0 < (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 → 0 ≤ (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → ‖Hb.Esharp z‖ < ‖Hb.E z‖] :=
  Hb.hb_tfae_of_zero hB hH (riemannXiUpper_exists_zero_of_hecke hB hH)

end WeilRH
