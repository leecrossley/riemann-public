/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Deninger

/-!
# `prop:no-positivity-cancel`, first clause: the top class `η`

Source: `latex/notes.tex`, `prop:no-positivity-cancel` and `def:adjoin-pair`. For a Weil datum of
type `(d, 0)` satisfying AW1 for `U = 𝟙` and AW3, there is `η ∈ V^{2d}` with `Θ_{2d} η = d η` and
`Tr η = 1`. The notes state this for `d = 2`; it holds for every `d`, by the same proof:
AW1 gives `V^{2d} ≅ 𝟙(-d)`, so `Θ_{2d} = d`, and AW3 makes `V^0 × V^{2d} → ℂ` perfect, so `Tr` is
nonzero on `V^{2d}`.

A Weil datum satisfying AW1 for `𝟙` and AW3 is a `DeningerStructure V d ℂ Unit.arith`.

## Main results

* `WeilRH.DeningerStructure.Θ_one`: `Θ 1 = 0`.
* `WeilRH.DeningerStructure.Θ_top`: `Θ = d` on `V^{2d}`.
* `WeilRH.DeningerStructure.exists_eta` (**`prop:no-positivity-cancel`, existence of `η`**).

## Not formalized

The adjunction of the pair `{ρ, 2 - ρ}` (`def:adjoin-pair`) and its AW1/AW2/AW3 are not built.
`DeningerStructure` does not require `V = ⊕_j V^j`, so the product of a new vector with an
arbitrary old vector (`1 ∪ x = x`, all others zero) is not definable without a projection onto
`ℂ · 1`; and generalized eigenspaces of `Θ ⊕ Θ_new` on `V^j ⊕ L_j` are not yet in the tree.
-/

open Module

namespace WeilRH

namespace DeningerStructure

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  (D : DeningerStructure V d ℂ Unit.arith)

/-- AW1 for `𝟙`: `Θ 1 = 0`. -/
theorem Θ_one : D.Θ D.one = 0 := by
  have h := D.e0_Θ ⟨D.one, D.one_mem⟩
  simp only [Unit.arith, LinearMap.zero_apply] at h
  have : (⟨D.Θ D.one, D.Θ_mem D.one_mem⟩ : D.G 0) = 0 := D.e0.injective (by rw [h, map_zero])
  simpa using congrArg Subtype.val this

/-- AW1 for `𝟙`: `V^{2d} ≅ 𝟙(-d)`, so `Θ x = d x` on `V^{2d}`. -/
theorem Θ_top {x : V} (hx : x ∈ D.G (2 * d)) : D.Θ x = (d : ℂ) • x := by
  have h := D.etop_Θ ⟨x, hx⟩
  simp only [Unit.twist, Unit.arith, zero_add, LinearMap.smul_apply, Module.End.one_apply,
    Int.cast_natCast] at h
  have : (⟨D.Θ x, D.Θ_mem hx⟩ : D.G (2 * d)) = (d : ℂ) • ⟨x, hx⟩ :=
    D.etop.injective (by rw [h, map_smul])
  simpa using congrArg Subtype.val this

lemma one_ne_zero : D.one ≠ 0 := by
  intro h
  have h1 := D.e0_one
  have : (⟨D.one, D.one_mem⟩ : D.G 0) = 0 := Subtype.ext h
  rw [this, map_zero] at h1
  exact zero_ne_one h1

/-- **`prop:no-positivity-cancel`, first clause.** There is `η ∈ V^{2d}` with `Θ_{2d} η = d η` and
`Tr η = 1`. -/
theorem exists_eta : ∃ η ∈ D.G (2 * d), D.Θ η = (d : ℂ) • η ∧ D.Tr η = 1 := by
  have h1 : D.one ∈ D.Θ.maxGenEigenspace 0 :=
    D.Θ.eigenspace_le_maxGenEigenspace (by
      rw [Module.End.mem_eigenspace_iff, Θ_one, zero_smul])
  obtain ⟨v, hv, -, hTr⟩ := D.nondeg D.one_mem h1 (one_ne_zero D)
  rw [Nat.sub_zero, D.one_mul] at *
  refine ⟨(D.Tr v)⁻¹ • v, Submodule.smul_mem _ _ hv, ?_, ?_⟩
  · rw [map_smul, Θ_top D hv, smul_comm]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hTr]

end DeningerStructure

end WeilRH
