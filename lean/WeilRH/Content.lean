/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.TrivialModel
import WeilRH.AW4Forms

/-!
# The content of the axioms (`prop:content`)

Source: the manuscript `latex/notes.tex`, `prop:content` and its proofs.

The trivial model is the degree-one slice `TrivialModel.model` of `def:trivial-model`
(`TrivialModel.lean`): `V^1 = ⨁_{ι × Bool} ℂ`, `Θ_1 = diag(lam ρ)`, spectrum `Σ`.

## Main results

* **`prop:content` (ii)**: `Content.exists_stdForm`. The trivial model carries a positive definite
  Hermitian form on `V^1` (the basis vectors are orthonormal); it is not the star form `h_1` of
  the model unless `Σ` lies on the line, and `Content.re_eq_half_of_isInfPol` shows that no
  positive definite form satisfies `(eq:inf-pol)` with weight one unless `Σ` lies on the line.
* **`prop:content` (iii), the real-pair block**: `Content.pairDatum ρ` (`ρ : ℝ`) is the Weil datum
  of type `(1, 0)` on `ℂe ⊕ ℂf` with `Θ = diag(ρ, 1 - ρ)`, `B(e, f) = 1 = -B(f, e)` and
  `*(ae + bf) = -āe + b̄f`. Its star form is `pair_h` (`h_1(ae+bf, a'e+b'f) = a b̄' + b ā'`),
  Hermitian (`pair_conj_symm`), nondegenerate (`pair_nondegenerate`), satisfies `(eq:inf-pol)`
  with weight one (`pair_infPol`), and has signature `(1, 1)` (`pair_h_pos`, `pair_h_neg`).
  The quartet block is `R2` (`Negative.lean`).
* **`prop:content` (iii), last clause**: `Content.not_isPositive_of_re_ne` — a degree-one datum
  of type `(1, 0)` with an eigenvalue off the line has a non-positive star form.

Not formalized: (i) and (iv), which need `Σ_K = div ξ_K` for a number field `K`
(`prop:xiK`). The assembly in (iii) of the blocks for an arbitrary divisor `Σ` into one datum is
`ContentAssembly.content_indef` (`ContentAssembly.lean`).
-/

open Module Complex ComplexConjugate DirectSum

namespace WeilRH.Content

open TrivialModel

section Positive

variable {ι : Type} [DecidableEq ι] (ρ : ι → ℂ)

/-- The basis `e_{ρ,k}` of `V^1 = ⨁_{ι × Bool} ℂ`. -/
noncomputable def stdBasis : Basis (ι × Bool) ℂ (V1 ι) :=
  Finsupp.basisSingleOne.map (finsuppLequivDFinsupp (M := ℂ) ℂ)

lemma stdBasis_apply (i : ι × Bool) :
    stdBasis i = DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) i 1 := by
  change Finsupp.toDFinsupp (Finsupp.single i (1 : ℂ)) = _
  rw [Finsupp.toDFinsupp_single, DirectSum.lof_eq_of]; rfl

/-- `Θ_1 e_p = ρ_p e_p`: every `ρ_p` is an eigenvalue of `Θ_1`. -/
lemma hasEigenvalue_theta (p : ι) : (theta ρ).HasEigenvalue (ρ p) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := stdBasis (p, true)) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext k
    rw [theta_apply, DFinsupp.smul_apply, smul_eq_mul, stdBasis_apply, lof_eval]
    split_ifs with h
    · subst h; simp [lam]
    · simp
  · exact (stdBasis (ι := ι)).ne_zero _

/-- **`prop:content` (ii)**, second half: a positive definite Hermitian form on `V^1` satisfying
`(eq:inf-pol)` with weight one forces `Σ` onto the line (Proposition `prop:purity`). -/
theorem re_eq_half_of_isInfPol (h : PosHermForm (V1 ι))
    (hP : Suspension.IsInfPol h (theta ρ) 1) (p : ι) : (ρ p).re = 1 / 2 := by
  have := h.re_eq_half (theta ρ) 1 (fun u v => by simpa using hP u v) (hasEigenvalue_theta ρ p)
  simpa using this

/-- Off the line the star form `h_1` of the trivial model is zero. -/
lemma model_h_of_not (hoff : ¬ ∀ p, (ρ p).re = 1 / 2) (u v : V1 ι) : (model ρ).h u v = 0 := by
  simp [WeightedStarDatum.h, WeightedStarDatum.B, model, star1_of_not ρ hoff]

/-- **`prop:content` (ii).** The trivial model carries a positive definite Hermitian form on `V^1`
for which the basis vectors `e_{ρ,k}` are orthonormal. It is not the star form `h_1` unless `Σ`
lies on the line, and it satisfies `(eq:inf-pol)` with weight one only if `Σ` lies on the line. -/
theorem exists_stdForm :
    ∃ h : PosHermForm (V1 ι),
      (∀ i k, h.toFun (stdBasis i) (stdBasis k) = if i = k then 1 else 0) ∧
      ((¬ ∀ p, (ρ p).re = 1 / 2) → ∃ u v, h.toFun u v ≠ (model ρ).h u v) ∧
      (Suspension.IsInfPol h (theta ρ) 1 → ∀ p, (ρ p).re = 1 / 2) := by
  refine ⟨PosHermForm.ofBasis stdBasis, PosHermForm.ofBasis_apply_basis stdBasis, ?_,
    re_eq_half_of_isInfPol ρ _⟩
  intro hoff
  obtain ⟨p, -⟩ := not_forall.1 hoff
  refine ⟨stdBasis (p, true), stdBasis (p, true), ?_⟩
  rw [model_h_of_not ρ hoff, PosHermForm.ofBasis_apply_basis]
  simp

end Positive

section Pair

/-! ### The real-pair block of `prop:content` (iii) -/

variable (ρ : ℝ)

/-- `Θ = diag(ρ, 1 - ρ)` on `ℂe ⊕ ℂf`. -/
noncomputable def pairTheta : Module.End ℂ (Fin 2 → ℂ) where
  toFun v := ![(ρ : ℂ) * v 0, (1 - (ρ : ℂ)) * v 1]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

/-- `B(e, f) = 1 = -B(f, e)`, `B(e, e) = B(f, f) = 0`. -/
noncomputable def pairB : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun u v => u 0 * v 1 - u 1 * v 0)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/-- `*(ae + bf) = -āe + b̄f`. -/
noncomputable def pairStar : (Fin 2 → ℂ) →ₗ⋆[ℂ] (Fin 2 → ℂ) where
  toFun v := ![-conj (v 0), conj (v 1)]
  map_add' u v := by ext i; fin_cases i <;> simp; ring
  map_smul' c v := by ext i; fin_cases i <;> simp

/-- **`prop:content` (iii)**, the real-pair block as a Weil datum of type `(1, 0)` in degree one:
AW1 for `U = 𝟙` (`cup_derivation`), the AW3 trace and the star law of AW4 (`star_comm`). -/
noncomputable def pairDatum : WeightedStarDatum 1 0 1 (Fin 2 → ℂ) (Fin 2 → ℂ) ℂ where
  ΘV := pairTheta ρ
  ΘW := pairTheta ρ
  ΘT := LinearMap.id
  cup := pairB
  cup_derivation u v := by simp [pairB, pairTheta]; ring
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := pairStar
  star_comm v := by
    ext i; fin_cases i <;> simp [pairTheta, pairStar, Complex.conj_ofReal]

/-- The star form of the real-pair block: `h_1(ae + bf, a'e + b'f) = a b̄' + b ā'`. -/
theorem pair_h (u v : Fin 2 → ℂ) :
    (pairDatum ρ).h u v = u 0 * conj (v 1) + u 1 * conj (v 0) := by
  simp [WeightedStarDatum.h, WeightedStarDatum.B, pairDatum, pairB, pairStar]

/-- `h_1` is Hermitian. -/
theorem pair_conj_symm (u v : Fin 2 → ℂ) : conj ((pairDatum ρ).h u v) = (pairDatum ρ).h v u := by
  rw [pair_h, pair_h]; simp; ring

/-- `h_1` is nondegenerate. -/
theorem pair_nondegenerate {u : Fin 2 → ℂ} (hu : u ≠ 0) : ∃ v, (pairDatum ρ).h u v ≠ 0 := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1; apply hu; ext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by rw [pair_h]; simpa using h1⟩
  · exact ⟨![0, 1], by rw [pair_h]; simpa using h0⟩

/-- `h_1` satisfies `(eq:inf-pol)` with weight one (`prop:polarization-identity`). -/
theorem pair_infPol (u v : Fin 2 → ℂ) :
    (pairDatum ρ).h ((pairDatum ρ).ΘV u) v + (pairDatum ρ).h u ((pairDatum ρ).ΘV v) =
      (1 : ℂ) * (pairDatum ρ).h u v := by
  simpa using (pairDatum ρ).polarization_identity u v

/-- Signature `(1, 1)`: `h_1(e + f, e + f) = 2`. -/
theorem pair_h_pos : (pairDatum ρ).h ![1, 1] ![1, 1] = 2 := by
  rw [pair_h]; norm_num

/-- Signature `(1, 1)`: `h_1(e - f, e - f) = -2`. -/
theorem pair_h_neg : (pairDatum ρ).h ![1, -1] ![1, -1] = -2 := by
  rw [pair_h]; norm_num

/-- The eigenvalues of the real-pair block are `ρ` and `1 - ρ`. -/
theorem pair_hasEigenvalue :
    (pairTheta ρ).HasEigenvalue ρ ∧ (pairTheta ρ).HasEigenvalue (1 - ρ) := by
  constructor
  · refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0]) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; ext i; fin_cases i <;> simp [pairTheta]
    · intro h; simpa using congrFun h 0
  · refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![0, 1]) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; ext i; fin_cases i <;> simp [pairTheta]
    · intro h; simpa using congrFun h 1

end Pair

/-- **`prop:content` (iii)**, last clause: a Weil datum of type `(1, 0)` in degree one whose `Θ_1`
has an eigenvalue off the line does not have a positive definite star form `h_1`. -/
theorem not_isPositive_of_re_ne {V W T : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup T] [Module ℂ T]
    (D : WeightedStarDatum 1 0 1 V W T) {σ : ℂ} (hσ : D.ΘV.HasEigenvalue σ)
    (hre : σ.re ≠ 1 / 2) : ¬ D.IsPositive :=
  fun hD => hre (WeightedStarDatum.re_eq_half_of_curve D hD hσ)

end WeilRH.Content
