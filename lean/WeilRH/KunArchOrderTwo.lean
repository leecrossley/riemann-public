/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.KunArch

/-!
# `prop:kun-arch` for a group of order two (round 71)

`prop:kun-arch` concerns the nontrivial character `χ` of `Gal(ℚ(i)/ℚ)`, a group of order two whose
nontrivial element is complex conjugation `c` (the decomposition group at the real place is the
whole group). Round 67 proved the statement for any `G`, `χ`, `c` with `χ c ≠ 1` and `c² = 1`.
Here those hypotheses are discharged for **every group of order two** with its nontrivial
character and nontrivial element (`orderTwo`), and the result is instantiated at the concrete group
`Multiplicative (ZMod 2)` with the sign character (`zmod2`).

Not formalized: the identification of `Gal(ℚ(i)/ℚ)` itself (as `ℚ(i) ≃ₐ[ℚ] ℚ(i)`) with a group of
order two whose nontrivial element is complex conjugation.
-/

open Complex

namespace WeilRH.KunArch

/-- In a group of order two, the nontrivial element `c` satisfies `c² = 1`, and a nontrivial
character `χ` has `χ c ≠ 1`. -/
theorem orderTwo_hyp {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 2) {c : G} (hc : c ≠ 1)
    {χ : G →* ℂˣ} (hχ : χ ≠ 1) : χ c ≠ 1 ∧ c ^ 2 = 1 := by
  have hall : ∀ g : G, g = 1 ∨ g = c := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G)).1 hG
    intro g
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hy g hg).trans (hy c hc).symm)
  refine ⟨fun h => hχ ?_, ?_⟩
  · ext g
    rcases hall g with rfl | rfl <;> simp [h]
  · rw [← hG]; exact pow_card_eq_one'

/-- **`prop:kun-arch`, first sentence, for every group of order two**: with `c` its nontrivial
element and `χ` a nontrivial character, `L_∞(χ, s) = Γ_ℝ(s + 1)` and `L_∞(χ ⊗ χ, s) = Γ_ℝ(s)`. -/
theorem orderTwo {G : Type*} [CommGroup G] [Finite G] (hG : Nat.card G = 2) {c : G} (hc : c ≠ 1)
    {χ : G →* ℂˣ} (hχ : χ ≠ 1) (s : ℂ) :
    LInftyChar χ c s = Gammaℝ (s + 1) ∧ LInftyChar (χ ^ 2) c s = Gammaℝ s :=
  ⟨LInftyChar_of_ne_one χ (orderTwo_hyp hG hc hχ).1 s,
    LInftyChar_sq χ (orderTwo_hyp hG hc hχ).2 s⟩

/-- The sign character of `ℤ/2`: `ofAdd 1 ↦ -1`. -/
noncomputable def signChar : Multiplicative (ZMod 2) →* ℂˣ where
  toFun g := if Multiplicative.toAdd g = 0 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases h01 (Multiplicative.toAdd x) with hx | hx <;>
      rcases h01 (Multiplicative.toAdd y) with hy | hy <;>
      simp [toAdd_mul, hx, hy, h11, h10]

/-- **`prop:kun-arch`, first sentence, at the concrete group `Multiplicative (ZMod 2)`** with the
sign character and `c = ofAdd 1`. -/
theorem zmod2 (s : ℂ) :
    LInftyChar signChar (Multiplicative.ofAdd (1 : ZMod 2)) s = Gammaℝ (s + 1) ∧
      LInftyChar (signChar ^ 2) (Multiplicative.ofAdd (1 : ZMod 2)) s = Gammaℝ s := by
  have hχ : signChar (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
    intro h
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simp [signChar] at this
    norm_num at this
  have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  exact ⟨LInftyChar_of_ne_one _ hχ s, LInftyChar_sq _ hc s⟩

end WeilRH.KunArch
