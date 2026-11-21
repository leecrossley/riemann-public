/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.HbSum
import WeilRH.R11Pole
import WeilRH.XiKConj

/-!
# The Hermite–Biehler and Herglotz forms of RH (`prop:hb`, round 75)

Source: `latex/notes.tex`, `prop:hb` with `def:hb`. For `F(z) = ξ(1/2 - iz)`, `𝔪 = -F'/F`,
`E = F + iF'` and `E^#(z) = conj (E (conj z))`, the following are equivalent:

1. every zero of `F` is real (RH);
2. `F ≠ 0` on `ℂ⁺` and `Im 𝔪 > 0` on `ℂ⁺`;
3. `Im 𝔪(z) ≥ 0` for every `z ∈ ℂ⁺` with `F(z) ≠ 0`;
4. `|E^#(z)| < |E(z)|` for every `z ∈ ℂ⁺` (the HB inequality).

`hb_tfae` proves this. Only `1 → 2` uses black boxes (B1 for `ℚ`, B3', B6, through
`HbSum.im_neg_logDeriv_pos`); `2 → 3`, `3 → 1`, `2 → 4`, `4 → 1` are unconditional.

Representation: "`𝔪` is holomorphic on `ℂ⁺`" in (ii) is encoded as `F ≠ 0` on `ℂ⁺`; they are
equivalent because at a zero of order `k` the function `𝔪` has a pole with residue `-k`
(`prop:hb`, proof of (ii) ⇒ (iv)). The step `3 → 1` is `R11.im_neg_logDeriv_lt_zero`.
The identity `|E|² - |E^#|² = 4 |F|² Im 𝔪` is `eq:hb-modulus` (`normSq_E_sub`).
-/

open Complex
open scoped ComplexConjugate

namespace WeilRH.Hb

/-- `ξ(s̄) = conj ξ(s)` (unconditional: `XiKConj.xi_conj` for the `ℚ` continuation of
`DedekindContinuation.rat`, whose `ξ` is `2 ξ`). -/
theorem completedXi_conj (s : ℂ) : completedXi (conj s) = conj (completedXi s) := by
  have h := XiKConj.xi_conj (DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat) s
  simp only [DedekindContinuation.SimplePoles.ofRat, map_mul, map_ofNat] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- `F(z̄) = conj F(z)` for `F(z) = ξ(1/2 - iz)`. -/
theorem riemannXiUpper_conj (z : ℂ) : riemannXiUpper (conj z) = conj (riemannXiUpper z) := by
  rw [riemannXiUpper, riemannXiUpper, ← completedXi_conj, ← completedXi_one_sub]
  congr 1
  simp only [map_sub, map_mul, conj_I, map_div₀, map_one, map_ofNat]
  ring

/-- `F'(z̄) = conj F'(z)`. -/
theorem deriv_riemannXiUpper_conj (z : ℂ) :
    deriv riemannXiUpper (conj z) = conj (deriv riemannXiUpper z) := by
  have hF : riemannXiUpper = conj ∘ riemannXiUpper ∘ conj := by
    funext w; simp [riemannXiUpper_conj]
  have h := congrFun (deriv_conj_conj (f := riemannXiUpper)) z
  rw [← hF] at h
  rw [h]; simp

/-- The HB companion `E = F + i F'`. -/
noncomputable def E (z : ℂ) : ℂ := riemannXiUpper z + I * deriv riemannXiUpper z

/-- Its reflection `E^#(z) = conj (E (conj z))`. -/
noncomputable def Esharp (z : ℂ) : ℂ := conj (E (conj z))

lemma Esharp_eq (z : ℂ) : Esharp z = riemannXiUpper z - I * deriv riemannXiUpper z := by
  rw [Esharp, E, riemannXiUpper_conj, deriv_riemannXiUpper_conj]
  simp only [map_add, map_mul, conj_conj, conj_I]
  ring

/-- `|a + i d|² - |a - i d|² = 4 |a|² Im (-d/a)` for `a ≠ 0` (`eq:hb-modulus`). -/
lemma normSq_add_sub {a d : ℂ} (ha : a ≠ 0) :
    normSq (a + I * d) - normSq (a - I * d) = 4 * normSq a * (-(d / a)).im := by
  have hn : normSq a ≠ 0 := (normSq_pos.2 ha).ne'
  have hn1 : a.re * a.re + a.im * a.im ≠ 0 := by rwa [normSq_apply] at hn
  have hn2 : a.re ^ 2 + a.im ^ 2 ≠ 0 := by rw [sq, sq]; exact hn1
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, I_re, I_im, neg_im,
    div_im]
  field_simp
  ring

/-- **`eq:hb-modulus`**: `|E|² - |E^#|² = 4 |F|² Im 𝔪` where `F ≠ 0`. -/
theorem normSq_E_sub {z : ℂ} (hz : riemannXiUpper z ≠ 0) :
    normSq (E z) - normSq (Esharp z) =
      4 * normSq (riemannXiUpper z) * (-logDeriv riemannXiUpper z).im := by
  rw [E, Esharp_eq, normSq_add_sub hz, logDeriv_apply]

/-- **`prop:hb`.** The four conditions are equivalent. Only `(i) → (ii)` uses black boxes:
B1 for `ℚ`, B3' and B6. -/
theorem hb_tfae_of_zero (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU)
    (hz0 : ∃ w, riemannXiUpper w = 0) :
    List.TFAE
      [∀ w, riemannXiUpper w = 0 → w.im = 0,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 ∧ 0 < (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 → 0 ≤ (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → ‖Esharp z‖ < ‖E z‖] := by
  have hFd := differentiable_riemannXiUpper
  have hF0 := riemannXiUpper_zero_ne
  -- a zero off the real axis gives one in `ℂ⁺`
  have hup : ∀ w, riemannXiUpper w = 0 → w.im ≠ 0 →
      ∃ w', riemannXiUpper w' = 0 ∧ 0 < w'.im := by
    intro w hw hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨-w, by rw [riemannXiUpper_neg]; exact hw, by simp; linarith⟩
    · exact ⟨w, hw, h⟩
  tfae_have 1 → 2 := by
    intro hRH z hz
    have hFz : riemannXiUpper z ≠ 0 := fun h0 => by have := hRH z h0; linarith
    refine ⟨hFz, ?_⟩
    obtain ⟨-, a, b, g, -, hfac, hlog⟩ := hH riemannXiUpper hFd ⟨0, hF0⟩
      (riemannXiUpper_growth hB) HbSum.ZIdx.pt
      (fun i hi => hF0 (by have := i.2.1; simp only [HbSum.ZIdx.pt] at hi; rwa [hi] at this))
      (fun w _ => HbSum.ZIdx.exists_iff hFd hF0 w) (fun w _ => HbSum.ZIdx.card_fiber hFd hF0 w)
    have h00 : analyticOrderNatAt riemannXiUpper 0 = 0 := by
      by_contra h
      exact hF0 ((SymEntire.mult_pos_iff hFd hF0 0).1 (Nat.pos_of_ne_zero h))
    have hfac' : ∀ s, riemannXiUpper s = exp (a + b * s) * g s := by
      intro s; rw [hfac s, h00, pow_zero, mul_one]
    obtain ⟨w, hw⟩ := hz0
    have : Nonempty (HbSum.ZIdx riemannXiUpper) :=
      ⟨⟨(w, 0), hw, (SymEntire.mult_pos_iff hFd hF0 w).2 hw⟩⟩
    refine HbSum.im_neg_logDeriv_pos HbSum.ZIdx.pt hFd riemannXiUpper_neg hfac' hlog hFz
      (fun i => ?_)
    rw [hRH i.pt i.2.1, abs_zero]; exact hz
  tfae_have 2 → 3 := fun h z hz _ => (h z hz).2.le
  tfae_have 3 → 1 := by
    intro h w hw
    by_contra hne
    obtain ⟨w', hw', hpos⟩ := hup w hw hne
    have hk := (SymEntire.mult_pos_iff hFd hF0 w').2 hw'
    have hord : analyticOrderAt riemannXiUpper w' = (analyticOrderNatAt riemannXiUpper w' : ℕ) :=
      (Nat.cast_analyticOrderNatAt (SymEntire.order_ne_top hFd hF0 w')).symm
    obtain ⟨ε₀, hε₀, hε₀', hε⟩ := R11.im_neg_logDeriv_lt_zero hFd hpos hk hord
    obtain ⟨hne0, -, hlt⟩ := hε (ε₀ / 2) (by linarith) (by linarith)
    have him : 0 < (w' - (ε₀ / 2 : ℝ) * I).im := by simp; linarith
    have := h _ him hne0
    rw [logDeriv_apply, ← neg_div] at this
    linarith
  tfae_have 2 → 4 := by
    intro h z hz
    obtain ⟨hFz, hm⟩ := h z hz
    have hd := normSq_E_sub hFz
    have hpos : 0 < normSq (E z) - normSq (Esharp z) := by
      rw [hd]; have := normSq_pos.2 hFz; positivity
    have h1 : ‖Esharp z‖ ^ 2 < ‖E z‖ ^ 2 := by
      rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  tfae_have 4 → 1 := by
    intro h w hw
    by_contra hne
    obtain ⟨w', hw', hpos⟩ := hup w hw hne
    have := h w' hpos
    rw [Esharp_eq, E, hw', zero_add, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  tfae_finish

/-- **`prop:hb`** (round 75 form, with B6 supplying a zero of `F`). -/
theorem hb_tfae (hB : HeckePackage ℚ) (hH : HadamardOrderOneLU) (hR : RiemannVonMangoldt) :
    List.TFAE
      [∀ w, riemannXiUpper w = 0 → w.im = 0,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 ∧ 0 < (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → riemannXiUpper z ≠ 0 → 0 ≤ (-logDeriv riemannXiUpper z).im,
       ∀ z : ℂ, 0 < z.im → ‖Esharp z‖ < ‖E z‖] :=
  hb_tfae_of_zero hB hH (riemannXiUpper_exists_zero hR)

end WeilRH.Hb
