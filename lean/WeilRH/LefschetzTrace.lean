/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import WeilRH.Lefschetz

/-!
# Traces of powers (`thm:ff-lefschetz`, the linear-algebra step)

Source: `latex/notes.tex`, Theorem `thm:ff-lefschetz` and Definition `def:lefschetz-numbers`.

The finite-dimensional core in `WeilRH.Lefschetz` works with the degreewise multisets `M j` of
Frobenius eigenvalues and defines `N_k = ∑_j (-1)^j ∑_{α ∈ M j} α^k`. The notes use this as
`N_k = ∑_j (-1)^j Tr(F^k | V^j)`. This file proves the missing identity:

* `trace_pow_eq_sum_roots`: for an endomorphism `F` of a finite-dimensional complex vector space,
  `Tr(F^k) = ∑_{α ∈ roots(χ_F)} α^k`, eigenvalues counted with algebraic multiplicity.
* `lefschetzNumber_eq_sum_trace`: hence, for a graded family of endomorphisms `F j` of `V j`,
  `lefschetzNumber n (fun j => (F j).charpoly.roots) k = ∑_{j < n} (-1)^j Tr((F j)^k)`.

The proof decomposes `V` into the generalized eigenspaces `V_(α)`; on `V_(α)` the map
`F^k - α^k` is nilpotent, so its trace vanishes, and `dim V_(α)` is the root multiplicity.

Items (i)–(ii) of `thm:ff-lefschetz` (the Grothendieck–Lefschetz trace formula and the
Poisson-summation identity) are not formalized here.
-/

open Module Polynomial

namespace WeilRH

namespace LefschetzTrace

/-- If `x` and `y` commute and `x - y` is nilpotent, so is `x^k - y^k`. -/
lemma isNilpotent_pow_sub_pow {A : Type*} [Ring A] {x y : A} (h : Commute x y)
    (hn : IsNilpotent (x - y)) (k : ℕ) : IsNilpotent (x ^ k - y ^ k) := by
  rw [← h.geom_sum₂_mul k]
  refine Commute.isNilpotent_mul_left ?_ hn
  refine Commute.sum_left _ _ _ fun i _ => ?_
  exact ((Commute.pow_left (Commute.sub_right (Commute.refl x) h) i).mul_left
    (Commute.pow_left (Commute.sub_right h.symm (Commute.refl y)) _))

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- On the generalized eigenspace `V_(α)`, the trace of `F^k` is `dim V_(α) · α^k`. -/
lemma trace_restrict_pow (F : Module.End ℂ V) (α : ℂ) (k : ℕ)
    (h : Set.MapsTo (F ^ k) (F.maxGenEigenspace α) (F.maxGenEigenspace α)) :
    LinearMap.trace ℂ _ ((F ^ k).restrict h) = finrank ℂ (F.maxGenEigenspace α) * α ^ k := by
  have h1 : Set.MapsTo F (F.maxGenEigenspace α) (F.maxGenEigenspace α) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl F) α
  set g := F.restrict h1 with hg
  have hpow : (F ^ k).restrict h = g ^ k := by
    rw [hg, Module.End.pow_restrict k h1 h]
  have hnil : IsNilpotent (g - algebraMap ℂ _ α) := by
    have := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap F α
    convert this using 1
    ext x
    simp [g, Algebra.algebraMap_eq_smul_one]
    rfl
  have hcomm : Commute g (algebraMap ℂ (Module.End ℂ (F.maxGenEigenspace α)) α) :=
    Algebra.commutes' α g |>.symm
  have hk := isNilpotent_pow_sub_pow hcomm hnil k
  have htr : LinearMap.trace ℂ _ (g ^ k - (algebraMap ℂ _ α) ^ k) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hk).eq_zero
  rw [hpow]
  rw [map_sub, sub_eq_zero] at htr
  rw [htr, ← map_pow, Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one,
    smul_eq_mul, mul_comm]

/-- **`Tr(F^k) = ∑ α^k`** over the roots of the characteristic polynomial, with multiplicity. -/
theorem trace_pow_eq_sum_roots (F : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (F ^ k) = (F.charpoly.roots.map (· ^ k)).sum := by
  classical
  have hind : iSupIndep F.maxGenEigenspace := Module.End.independent_maxGenEigenspace F
  have htop : ⨆ α, F.maxGenEigenspace α = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top F
  have hint : DirectSum.IsInternal F.maxGenEigenspace :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hind, htop⟩
  have hmaps : ∀ α, Set.MapsTo (F ^ k) (F.maxGenEigenspace α) (F.maxGenEigenspace α) :=
    fun α => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.pow_right (Commute.refl F) k) α
  have hfin : {α | F.maxGenEigenspace α ≠ ⊥}.Finite := by
    refine (F.charpoly.roots.toFinset.finite_toSet).subset fun α hα => ?_
    simp only [Set.mem_ofPred_eq] at hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hr
    apply hα
    rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
      ← Polynomial.count_roots]
    exact Multiset.count_eq_zero.mpr hr
  rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps]
  simp_rw [trace_restrict_pow F _ k (hmaps _)]
  rw [Finset.sum_multiset_map_count]
  have hsub : hfin.toFinset ⊆ F.charpoly.roots.toFinset := by
    intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hα
    simp only [Multiset.mem_toFinset]
    by_contra hr
    apply hα
    rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
      ← Polynomial.count_roots]
    exact Multiset.count_eq_zero.mpr hr
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [Polynomial.count_roots, LinearMap.finrank_maxGenEigenspace_eq, nsmul_eq_mul]
  · intro α _ hα
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hα
    rw [Polynomial.count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, hα, finrank_bot,
      zero_smul]

/-- **Lefschetz numbers are alternating traces.** For endomorphisms `F j` of finite-dimensional
complex spaces `V j`, the Lefschetz number of the eigenvalue multisets `roots(χ_{F j})` is
`∑_{j < n} (-1)^j Tr((F j)^k)` (`def:lefschetz-numbers`, as used in `thm:ff-lefschetz`). -/
theorem lefschetzNumber_eq_sum_trace (n : ℕ) (V : ℕ → Type*) [∀ j, AddCommGroup (V j)]
    [∀ j, Module ℂ (V j)] [∀ j, FiniteDimensional ℂ (V j)] (F : ∀ j, Module.End ℂ (V j)) (k : ℕ) :
    Lefschetz.lefschetzNumber n (fun j => (F j).charpoly.roots) k =
      ∑ j ∈ Finset.range n, (-1) ^ j * LinearMap.trace ℂ (V j) ((F j) ^ k) := by
  unfold Lefschetz.lefschetzNumber
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_pow_eq_sum_roots]

end LefschetzTrace

end WeilRH
