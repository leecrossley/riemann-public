/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.AlgebraFormOrdered

/-!
# The algebra form over `ℚ` and `ℝ`: moduli and representations (`prop:algebra-form` (i)–(ii))

Source: `latex/notes.tex`, Proposition `prop:algebra-form` (Kleiman 1968, Lemma 4.6), for
`k ∈ {ℚ, ℝ}`. The `k = ℂ` case is `WeilRH.AlgebraForm`; separability over `k` is
`PositiveTraceOrd.minpoly_separable` (`WeilRH.AlgebraFormOrdered`).

## Setting

`K` is an ordered field with algebra maps `K → ℝ → ℂ` (a scalar tower) such that `K → ℝ` sends
positive elements to positive reals. This covers `K = ℚ` and `K = ℝ` (`nonvacuous_rat`,
`nonvacuous_real`). The source's "complex roots of the minimal polynomial over `k`" are the roots
of `(minpoly K g).map (algebraMap K ℂ)`.

## Main results

* `PositiveTraceOrd.norm_eq_rpow_of_isRoot` (**(i), moduli**): if `g g† = c` with
  `c ↦ q^j ∈ ℝ`, every complex root of the minimal polynomial of `g` over `K` has modulus `q^{j/2}`.
* `PositiveTraceOrd.rep_isSemisimple`, `rep_norm_eq_rpow`, `rep_iSup_eigenspace` (**(ii)**): for a
  ring map `ι : A → End_ℂ V` that is `K`-linear on scalars, `ι(g)` is diagonalizable with
  eigenvalues of modulus `q^{j/2}`.

## Route (differs from the source's proof)

The source extends `S` to a Hermitian form on `A ⊗_k ℂ` and shows it stays positive definite. We
avoid the tensor product: an `S`-orthogonal basis of `A` over `K` (`exists_orthogonal_basis`)
diagonalizes `S` with positive entries `d_i ∈ K`, so `Mᵀ D M = c D` for the matrix `M` of left
multiplication by `g`. Mapping `M` to `ℂ`, an eigenvector `v` gives
`|λ|² ∑ d_i |v_i|² = c ∑ d_i |v_i|²`. For (ii) the source assumes `ι : A ⊗_k ℂ → End V` injective
and unital; we only use its restriction to `A` and the scalar compatibility, and no injectivity.
-/

open Polynomial Module Matrix

namespace WeilRH

namespace PositiveTraceOrd

variable {K A : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Ring A] [Algebra K A]
  (P : PositiveTraceOrd K A)

lemma symForm_isSymm : LinearMap.IsSymm P.symForm :=
  LinearMap.isSymm_def.2 fun a b => by
    rw [RingHom.id_apply, symForm_apply, symForm_apply, add_comm]

variable [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma algebraMap_complex (x : K) : algebraMap K ℂ x = ((algebraMap K ℝ x : ℝ) : ℂ) :=
  IsScalarTower.algebraMap_apply K ℝ ℂ x

omit [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ] in
/-- The matrix identity `Mᵀ D M = c D` in an `S`-orthogonal basis. -/
lemma matrix_similitude [FiniteDimensional K A] {g : A} {c : K} (hc : c ≠ 0)
    (hg : g * P.dag g = c • (1 : A)) {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K A)
    (hb : (P.symForm : LinearMap.BilinForm K A).IsOrthoᵢ b) (i l : ι) :
    ∑ k, LinearMap.toMatrix b b (Algebra.lmul K A g) k i *
        LinearMap.toMatrix b b (Algebra.lmul K A g) k l * P.symForm (b k) (b k) =
      if i = l then c * P.symForm (b i) (b i) else 0 := by
  obtain ⟨M, hM⟩ : ∃ M, M = LinearMap.toMatrix b b (Algebra.lmul K A g) := ⟨_, rfl⟩
  rw [← hM]
  have hexp : ∀ m, g * b m = ∑ k, M k m • b k := by
    intro m
    conv_lhs => rw [← b.sum_repr (g * b m)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hM, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul]
    rfl
  have hdiag : ∀ k m, k ≠ m → P.symForm (b k) (b m) = 0 := fun k m h => hb h
  have hS2 : P.symForm (g * b i) (g * b l) = ∑ k, M k i * M k l * P.symForm (b k) (b k) := by
    rw [hexp i, hexp l]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro m _ hm; rw [hdiag m k hm]; ring
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [← hS2, P.symForm_mulLeft hc hg]
  by_cases h : i = l
  · subst h; rw [if_pos rfl]
  · rw [if_neg h, hdiag i l h, mul_zero]

/-- **`prop:algebra-form` (i), moduli, over `k ∈ {ℚ, ℝ}`.** If `g g† = c` with `c ↦ q^j` in `ℝ`,
every complex root of the minimal polynomial of `g` over `K` has modulus `q^{j/2}`. -/
theorem norm_eq_rpow_of_isRoot [FiniteDimensional K A]
    (hpos : ∀ x : K, 0 < x → 0 < algebraMap K ℝ x) {g : A} {c : K} {q j : ℝ} (hq : 0 < q)
    (hcq : algebraMap K ℝ c = q ^ j) (hg : g * P.dag g = c • (1 : A)) {μ : ℂ}
    (hμ : ((minpoly K g).map (algebraMap K ℂ)).IsRoot μ) : ‖μ‖ = q ^ (j / 2) := by
  classical
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcq
    exact (Real.rpow_pos_of_pos hq j).ne' hcq.symm
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (P.symForm_isSymm)
  set f := Algebra.lmul K A g
  obtain ⟨M, hM⟩ : ∃ M, M = LinearMap.toMatrix b b f := ⟨_, rfl⟩
  set d : Fin (finrank K A) → K := fun k => P.symForm (b k) (b k)
  have hd : ∀ k, 0 < d k := fun k => P.symForm_self_pos (b.ne_zero k)
  -- `μ` is an eigenvalue of the complexified matrix
  have hmin : minpoly K f = minpoly K g := by
    refine minpoly.algHom_eq _ (fun x y hxy => ?_) g
    simpa [Algebra.coe_lmul_eq_mul] using congrArg (fun h : Module.End K A => h 1) hxy
  have hdvd : minpoly K g ∣ M.charpoly := by
    rw [← hmin, hM, LinearMap.charpoly_toMatrix]
    exact LinearMap.minpoly_dvd_charpoly f
  obtain ⟨M', hM'⟩ : ∃ M', M' = M.map (algebraMap K ℂ) := ⟨_, rfl⟩
  have hroot : M'.charpoly.IsRoot μ := by
    rw [hM', Matrix.charpoly_map]
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd _ hdvd) hμ
  have hdet : (Matrix.scalar _ μ - M').det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hMv : M' *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext k
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  -- the weighted norm
  set D : Fin (finrank K A) → ℂ := fun k => algebraMap K ℂ (d k)
  set W : ℂ := ∑ k, D k * (v k * star (v k))
  have hDreal : ∀ k, star (D k) = D k := fun k => by
    simp only [D, algebraMap_complex, Complex.star_def, Complex.conj_ofReal]
  have hW : 0 < W.re ∧ W.im = 0 := by
    have hterm : ∀ k, D k * (v k * star (v k)) =
        ((algebraMap K ℝ (d k) * ‖v k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      simp only [D, algebraMap_complex]
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    simp only [W, hterm, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.ofReal_im, and_true]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun k =>
      algebraMap K ℝ (d k) * ‖v k‖ ^ 2) (fun k _ => by
        have := hpos _ (hd k); positivity) (Finset.mem_univ k))
    have := hpos _ (hd k)
    have : 0 < ‖v k‖ := norm_pos_iff.2 hk
    positivity
  have hW0 : W ≠ 0 := fun h => by rw [h] at hW; simp at hW
  -- the similitude identity over `ℂ`
  have hsim : ∀ i l, ∑ k, M' k i * M' k l * D k =
      if i = l then algebraMap K ℂ c * D i else 0 := by
    intro i l
    have := congrArg (algebraMap K ℂ) (P.matrix_similitude hc hg b hb i l)
    rw [← hM] at this
    simp only [map_sum, map_mul, apply_ite (algebraMap K ℂ), map_zero] at this
    rw [hM']
    simpa [Matrix.map_apply, D, d] using this
  have hMreal : ∀ k i, star (M' k i) = M' k i := fun k i => by
    rw [hM', Matrix.map_apply, algebraMap_complex, Complex.star_def, Complex.conj_ofReal]
  have hmv : ∀ k, (M' *ᵥ v) k = ∑ i, M' k i * v i := fun k => rfl
  have hkey : ∑ k, D k * ((M' *ᵥ v) k * star ((M' *ᵥ v) k)) = algebraMap K ℂ c * W := by
    calc ∑ k, D k * ((M' *ᵥ v) k * star ((M' *ᵥ v) k))
        = ∑ k, ∑ i, ∑ l, D k * (M' k i * v i) * (M' k l * star (v l)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hmv k, star_sum, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [star_mul', hMreal]; ring
      _ = ∑ i, ∑ l, (∑ k, M' k i * M' k l * D k) * (v i * star (v l)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ i, algebraMap K ℂ c * (D i * (v i * star (v i))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp_rw [hsim, ite_mul, zero_mul]
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          ring
      _ = algebraMap K ℂ c * W := by rw [← Finset.mul_sum]
  have hleft : ∑ k, D k * ((M' *ᵥ v) k * star ((M' *ᵥ v) k)) = (μ * star μ) * W := by
    simp only [hMv, Pi.smul_apply, smul_eq_mul, star_mul', W, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hμc : μ * star μ = algebraMap K ℂ c := mul_right_cancel₀ hW0 (hleft.symm.trans hkey)
  rw [Complex.star_def, Complex.mul_conj, algebraMap_complex, hcq] at hμc
  have hsq : ‖μ‖ ^ 2 = q ^ j := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast hμc
  have h2 : (q ^ (j / 2)) ^ 2 = q ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  exact (sq_eq_sq₀ (norm_nonneg μ) (Real.rpow_nonneg hq.le _)).1 (hsq.trans h2.symm)

/-! ### Representations (`prop:algebra-form` (ii)) -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [LinearOrder K] [IsStrictOrderedRing K] [Algebra K ℝ] [IsScalarTower K ℝ ℂ]
  [FiniteDimensional ℂ V] in
/-- For a ring map `ι : A → End V` compatible with scalars, `p(ι g) = ι(p(g))` for `p ∈ K[X]`. -/
lemma aeval_map_ring (ι : A →+* Module.End ℂ V)
    (hι : ∀ x : K, ι (algebraMap K A x) = algebraMap ℂ _ (algebraMap K ℂ x)) (g : A) (p : K[X]) :
    aeval (ι g) (p.map (algebraMap K ℂ)) = ι (aeval g p) := by
  induction p using Polynomial.induction_on with
  | C a => simp [hι]
  | add p p' hp hp' => simp [hp, hp']
  | monomial n a h => simp [Polynomial.map_mul, map_mul, hι, pow_succ]

include P in
/-- **`prop:algebra-form` (ii), semisimplicity, over `k ∈ {ℚ, ℝ}`.** -/
theorem rep_isSemisimple [FiniteDimensional K A] (ι : A →+* Module.End ℂ V)
    (hι : ∀ x : K, ι (algebraMap K A x) = algebraMap ℂ _ (algebraMap K ℂ x)) {g : A} {c : K}
    (hc : c ≠ 0) (hg : g * P.dag g = c • (1 : A)) : (ι g).IsSemisimple := by
  have hsep := (P.minpoly_separable hc hg).map (f := algebraMap K ℂ)
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  rw [aeval_map_ring ι hι, minpoly.aeval, map_zero]

include P in
/-- **`prop:algebra-form` (ii), moduli, over `k ∈ {ℚ, ℝ}`.** -/
theorem rep_norm_eq_rpow [FiniteDimensional K A] (hpos : ∀ x : K, 0 < x → 0 < algebraMap K ℝ x)
    (ι : A →+* Module.End ℂ V)
    (hι : ∀ x : K, ι (algebraMap K A x) = algebraMap ℂ _ (algebraMap K ℂ x)) {g : A} {c : K}
    {q j : ℝ} (hq : 0 < q) (hcq : algebraMap K ℝ c = q ^ j) (hg : g * P.dag g = c • (1 : A))
    {μ : ℂ} (hμ : (ι g).HasEigenvalue μ) : ‖μ‖ = q ^ (j / 2) := by
  refine P.norm_eq_rpow_of_isRoot hpos hq hcq hg ?_
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have h0 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly K g).map (algebraMap K ℂ)) hx
  rw [aeval_map_ring ι hι, minpoly.aeval, map_zero, LinearMap.zero_apply] at h0
  exact (smul_eq_zero.1 h0.symm).resolve_right hx.2

include P in
/-- **`prop:algebra-form` (ii), diagonalizability, over `k ∈ {ℚ, ℝ}`.** -/
theorem rep_iSup_eigenspace [FiniteDimensional K A] (ι : A →+* Module.End ℂ V)
    (hι : ∀ x : K, ι (algebraMap K A x) = algebraMap ℂ _ (algebraMap K ℂ x)) {g : A} {c : K}
    (hc : c ≠ 0) (hg : g * P.dag g = c • (1 : A)) : ⨆ α, (ι g).eigenspace α = ⊤ := by
  have hs := (P.rep_isSemisimple ι hι hc hg).isFinitelySemisimple
  rw [← (ι g).iSup_maxGenEigenspace_eq_top]
  exact iSup_congr fun μ => (hs.maxGenEigenspace_eq_eigenspace μ).symm

end PositiveTraceOrd

/-- The hypotheses on `K` hold for `ℚ`. -/
theorem nonvacuous_rat : ∀ x : ℚ, 0 < x → 0 < algebraMap ℚ ℝ x := fun x hx => by
  simpa using hx

/-- The hypotheses on `K` hold for `ℝ`. -/
theorem nonvacuous_real : ∀ x : ℝ, 0 < x → 0 < algebraMap ℝ ℝ x := fun x hx => by
  simpa using hx

example : IsScalarTower ℚ ℝ ℂ := inferInstance

end WeilRH
