/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.XiHalf

/-!
# No zeros of `F` high in the upper half-plane (`prop:hb-high`, first clause)

Source: `latex/notes.tex`, Proposition `prop:hb-high`: with `F` as in `def:zeta`, `F` has no zero in
the closed half-plane `{Im z ≥ 1/2}`, and `Im 𝔪(z) > 0` there, `𝔪 = -F'/F`.

`riemannXiUpper_ne_zero` is the first clause, for `F = riemannXiUpper` (`F(z) = ξ(1/2 - iz)`,
`def:zeta` (d), as in `XiHalf`). The manuscript's proof uses that all zeros lie in the strip
`|Im z| < 1/2`; here the needed half of that, `ζ(s) ≠ 0` for `Re s ≥ 1`, is Mathlib's
`riemannZeta_ne_zero_of_one_le_re`, and `Re(1/2 - iz) = 1/2 + Im z ≥ 1`.

The second clause (`Im 𝔪 > 0`) uses the Hadamard product `eq:hb-product` of `F` and is not
formalized.
-/

open Complex

namespace WeilRH

/-- **`prop:hb-high`, first clause.** `F(z) = ξ(1/2 - iz)` has no zero with `Im z ≥ 1/2`. -/
theorem riemannXiUpper_ne_zero {z : ℂ} (hz : 1 / 2 ≤ z.im) : riemannXiUpper z ≠ 0 := by
  intro h0
  rw [riemannXiUpper, completedXi_eq_zero_iff] at h0
  have hre : 1 ≤ (1 / 2 - I * z).re := by
    simp only [sub_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, sub_neg_eq_add]
    norm_num
    linarith
  exact riemannZeta_ne_zero_of_one_le_re hre h0.1

end WeilRH
