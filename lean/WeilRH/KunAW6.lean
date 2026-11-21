/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.KunDiag
import WeilRH.XiKConj
import WeilRH.XiKZerosInfinite

/-!
# `prop:kun-AW6`: `0` has infinite multiplicity for `T₁ ⊞ T₁`

`latex/notes.tex`, `prop:kun-AW6`. For a Weil datum of type `(1,0)` on `X̄_K` satisfying AW1–AW4,
`T₁` is the diagonal operator of `prop:hilbert` (degree `j = 1`): its eigenvalues are the `τ` with
`ρ = 1/2 + iτ` running over the zeros of `ξ_K` (`thm:rh`). Then `0` is an eigenvalue of infinite
multiplicity of `T₁ ⊞ T₁`, so `T₁ ⊞ T₁` has no compact resolvent.

**Representation.** The datum enters through the output of `thm:rh` and `prop:hilbert` that the
proof uses: a family `τ : ι → ℝ` (the diagonal entries of `T₁`) with `ξ_K(1/2 + iτ_i) = 0` for every
`i`, every zero of `ξ_K` of the form `1/2 + iτ_i` (`hsurj`). The Weil datum itself, the Hilbert
completion and the operator are not re-built here; `T₁ ⊞ T₁` is represented by its diagonal entries
as in `KunDiag`. The manuscript's proof is followed: zeros are infinite (here from B1 and B3,
`Hecke.zeroIdx_infinite`, instead of `thm:kun-square`), `ξ_K(s̄) = conj ξ_K(s)` gives `−τ_i` as an
eigenvalue, and `prop:kun-diag` (iv) applies. CONDITIONAL on B1 (`HeckePackage K`) and B3
(`HadamardOrderOne`).
-/

open Complex ComplexConjugate

namespace WeilRH
namespace KunAW6

variable {K : Type} [Field K] [NumberField K] (hB : HeckePackage K)

/-- The zeros of `ξ_K` form an infinite set (B1 + B3): `ZeroIdx` is infinite and each zero has
finitely many indices. -/
theorem zeroSet_infinite (hH : HadamardOrderOne) : {z : ℂ | Hecke.xi hB z = 0}.Infinite := by
  intro hfin
  have hinf := Hecke.zeroIdx_infinite hB hH
  set S := hfin.toFinset
  set N := S.sup (fun z => analyticOrderNatAt hB.simplePoles.ξ z)
  have hsub : ∀ i : Hecke.ZeroIdx hB, i.1 ∈ (S ×ˢ Finset.range (N + 1) : Finset (ℂ × ℕ)) := by
    intro i
    have hz : i.1.1 ∈ S := by
      rw [Set.Finite.mem_toFinset]; exact i.2.1
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨hz, ?_⟩
    have := Finset.le_sup (f := fun z => analyticOrderNatAt hB.simplePoles.ξ z) hz
    have := i.2.2
    omega
  have : Finite (Hecke.ZeroIdx hB) :=
    Finite.of_injective (fun i => (⟨i.1, hsub i⟩ : (S ×ˢ Finset.range (N + 1) : Finset (ℂ × ℕ))))
      (fun i j h => Subtype.ext (by simpa using congrArg Subtype.val h))
  exact not_finite (Hecke.ZeroIdx hB)

/-- **`prop:kun-AW6`**, CONDITIONAL on B1 and B3. If the diagonal entries `τ_i` of `T₁` are the
`τ` with `ξ_K(1/2 + iτ) = 0` and every zero arises, then infinitely many pairs have
`τ_i + τ_k = 0`; hence `0` is an eigenvalue of infinite multiplicity of `T₁ ⊞ T₁` (its counting
function is `⊤` at `0`) and `T₁ ⊞ T₁` has no compact resolvent. -/
theorem kun_AW6 (hH : HadamardOrderOne) {ι : Type*} (τ : ι → ℝ)
    (hτ : ∀ i, Hecke.xi hB (1 / 2 + (τ i : ℂ) * I) = 0)
    (hsurj : ∀ ρ, Hecke.xi hB ρ = 0 → ∃ i, ρ = 1 / 2 + (τ i : ℂ) * I) :
    {p : ι × ι | τ p.1 + τ p.2 = 0}.Infinite ∧ KunDiag.Nsum τ τ 0 = ⊤ ∧
      ¬ {p : ι × ι | |τ p.1 + τ p.2| ≤ 0}.Finite := by
  -- every `−τ_i` is an entry
  have hneg : ∀ i, ∃ k, τ k = -τ i := by
    intro i
    have hz : Hecke.xi hB (conj (1 / 2 + (τ i : ℂ) * I)) = 0 := by
      rw [Hecke.xi_conj, hτ i, map_zero]
    obtain ⟨k, hk⟩ := hsurj _ hz
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simp at him
    linarith
  choose κ hκ using hneg
  -- `ι` is infinite, since every zero is some `1/2 + iτ_i`
  have hIinf : Infinite ι := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have hrange : {z : ℂ | Hecke.xi hB z = 0} ⊆
        Set.range (fun i => (1 / 2 + (τ i : ℂ) * I)) := by
      intro z hz; obtain ⟨i, hi⟩ := hsurj z hz; exact ⟨i, hi.symm⟩
    exact zeroSet_infinite hB hH ((Set.finite_range _).subset hrange)
  have hpairs : {p : ι × ι | τ p.1 + τ p.2 = 0}.Infinite := by
    have hinj : Function.Injective (fun i : ι => (i, κ i)) := fun i j h => (Prod.mk.inj h).1
    refine Set.infinite_of_injective_forall_mem hinj (fun i => ?_)
    show τ i + τ (κ i) = 0
    rw [hκ i]; ring
  exact ⟨hpairs, KunDiag.zero_infinite hpairs⟩

end KunAW6
end WeilRH
