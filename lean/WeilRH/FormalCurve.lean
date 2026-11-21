/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The formal curve

Source: the manuscript `latex/notes.tex`, `def:formal-curve` and `prop:formal-curve` (i)–(iv).

The formal curve is the graded `ℂ`-algebra `H⁰ ⊕ H¹ ⊕ H² = ℂ·1 ⊕ (ℂe₁ ⊕ ℂe₂) ⊕ ℂη` with
`e₁ ∪ e₂ = -e₂ ∪ e₁ = η`, all other products of positive-degree elements zero, trace
`Tr(cη) = c`, and `F = 1 ⊕ diag(3, 1) ⊕ 3`, `q = 3`. Its `H¹` satisfies every linear Weil
condition except purity, and admits no positive Frobenius-compatible Hermitian form.

An element is a triple `(a, x, b)` standing for `a·1 + x₀e₁ + x₁e₂ + bη`; `mul` is the cup
product written out on components.

## Main results

* (i) `WeilRH.FormalCurve.F_mul`, `F_one`, `F_bijective` (graded algebra automorphism);
  `B_self`, `B_antisymm`, `B_perfect`, `B_F` (alternating perfect pairing of weight `q`);
  `lefschetz_eq_zero` (`N_n = 0`); `P₁_eq`, `Z_eq` (`Z = P₁/((1-t)(1-qt))`), `P₁_funct`.
* (ii) `hasEigenvalue_F₁_iff`, `norm_ne_sqrt_of_hasEigenvalue` (impurity).
* (iii) `frobCompatible_iff`, `det_ne_zero_of_frobCompatible`, `exists_pos_of_frobCompatible`,
  `exists_neg_of_frobCompatible`, `not_posDef_of_frobCompatible`.
* (iv) `algPair_eq_tr_mul`, `algPair_nondegenerate`, `algPair_F`, `hasEigenvalue_Falg_iff`,
  `iSup_eigenspace_Falg`.

Hermitian forms on `H¹` are given by their Gram matrix `G` and are linear in the first
argument, as in the manuscript: `hermForm G u v = v* G u` (as in `WeilRH.Jordan.hermForm`).
-/

open Matrix Polynomial
open scoped ComplexOrder

namespace WeilRH.FormalCurve

/-- An element `a·1 + x₀e₁ + x₁e₂ + bη` of the formal curve `H⁰ ⊕ H¹ ⊕ H²`. -/
abbrev H := ℂ × (Fin 2 → ℂ) × ℂ

/-- The cup product of `def:formal-curve`: `e₁ ∪ e₂ = -e₂ ∪ e₁ = η`, `1` a unit, all other
products of positive-degree elements zero. -/
def mul (u v : H) : H :=
  (u.1 * v.1, u.1 • v.2.1 + v.1 • u.2.1,
    u.1 * v.2.2 + u.2.2 * v.1 + (u.2.1 0 * v.2.1 1 - u.2.1 1 * v.2.1 0))

/-- The unit `1 ∈ H⁰`. -/
def one : H := (1, 0, 0)

/-- The trace `Tr(a·1 + x + bη) = b` (`Tr(cη) = c`, extended by zero on `H⁰ ⊕ H¹`). -/
def tr (u : H) : ℂ := u.2.2

/-- The matrix `diag(3, 1)` of `F` on `H¹` in the basis `e₁, e₂`. -/
def F₁ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![3, 1]

/-- The graded map `F = 1 ⊕ diag(3, 1) ⊕ 3`. -/
def F (u : H) : H := (u.1, F₁ *ᵥ u.2.1, 3 * u.2.2)

/-- `q = 3`. -/
def q : ℂ := 3

lemma F₁_mulVec (x : Fin 2 → ℂ) : F₁ *ᵥ x = ![3 * x 0, x 1] := by
  ext i; fin_cases i <;> simp [F₁, Matrix.mulVec_diagonal]

/-- **`prop:formal-curve` (i)**: `F` is multiplicative. -/
theorem F_mul (u v : H) : F (mul u v) = mul (F u) (F v) := by
  obtain ⟨a, x, b⟩ := u
  obtain ⟨a', y, b'⟩ := v
  simp only [F, mul, F₁_mulVec, Prod.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i <;> simp [mul_add, mul_left_comm]
  · simp; ring

/-- **`prop:formal-curve` (i)**: `F` fixes the unit. -/
theorem F_one : F one = one := by
  simp [F, one]

/-- **`prop:formal-curve` (i)**: `F` is bijective, hence a graded algebra automorphism. -/
theorem F_bijective : Function.Bijective F := by
  refine ⟨fun u v h => ?_, fun w => ⟨(w.1, ![w.2.1 0 / 3, w.2.1 1], w.2.2 / 3), ?_⟩⟩
  · obtain ⟨a, x, b⟩ := u
    obtain ⟨a', y, b'⟩ := v
    simp only [F, F₁_mulVec, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h20 := congrFun h2 0
    have h21 := congrFun h2 1
    simp at h20 h21
    refine Prod.ext h1 (Prod.ext ?_ ?_)
    · ext i; fin_cases i <;> simpa
    · simpa using h3
  · obtain ⟨a, x, b⟩ := w
    simp only [F, F₁_mulVec, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · ext i; fin_cases i <;> simp; field_simp
    · field_simp

/-- The pairing `B(u, v) = Tr(u ∪ v)` on `H¹`. -/
def B (x y : Fin 2 → ℂ) : ℂ := tr (mul (0, x, 0) (0, y, 0))

lemma B_apply (x y : Fin 2 → ℂ) : B x y = x 0 * y 1 - x 1 * y 0 := by
  simp [B, tr, mul]

/-- **`prop:formal-curve` (i)**: `B` is alternating. -/
theorem B_self (x : Fin 2 → ℂ) : B x x = 0 := by
  rw [B_apply]; ring

/-- `B` is antisymmetric. -/
theorem B_antisymm (x y : Fin 2 → ℂ) : B y x = -B x y := by
  rw [B_apply, B_apply]; ring

/-- **`prop:formal-curve` (i)**: `B` is perfect: every linear functional on `H¹` is `B(x, ·)`
for a unique `x`. -/
theorem B_perfect (φ : (Fin 2 → ℂ) →ₗ[ℂ] ℂ) : ∃! x : Fin 2 → ℂ, ∀ y, B x y = φ y := by
  have key : ∀ y : Fin 2 → ℂ,
      φ y = y 0 * φ (Pi.single 0 1) + y 1 * φ (Pi.single 1 1) := by
    intro y
    have : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [this]
    simp [map_add, map_smul]
  refine ⟨![φ (Pi.single 1 1), -φ (Pi.single 0 1)], fun y => ?_, fun x hx => ?_⟩
  · rw [B_apply, key y]; simp; ring
  · have h0 := hx (Pi.single 1 1)
    have h1 := hx (Pi.single 0 1)
    simp [B_apply] at h0 h1
    ext i; fin_cases i <;> simp [h0, ← h1]

/-- **`prop:formal-curve` (i)**: `B(Fu, Fv) = q B(u, v)`. -/
theorem B_F (x y : Fin 2 → ℂ) : B (F₁ *ᵥ x) (F₁ *ᵥ y) = q * B x y := by
  simp only [B_apply, F₁_mulVec, q]; simp; ring

/-- The Lefschetz number `N_n = Σᵢ (-1)ⁱ Tr(Fⁿ | Hⁱ)`, with `F = 1` on `H⁰` and `3` on `H²`. -/
def lefschetz (n : ℕ) : ℂ := 1 - Matrix.trace (F₁ ^ n) + 3 ^ n

/-- **`prop:formal-curve` (i)**: `N_n = 0` for all `n`. -/
theorem lefschetz_eq_zero (n : ℕ) : lefschetz n = 0 := by
  simp [lefschetz, F₁, Matrix.diagonal_pow, Matrix.trace, Fin.sum_univ_two]

/-- `P₁(t) = det(1 - F t | H¹) ∈ ℤ[t]`. -/
noncomputable def P₁ : ℤ[X] :=
  Matrix.det (1 - (X : ℤ[X]) • Matrix.diagonal ![(3 : ℤ[X]), 1])

/-- **`prop:formal-curve` (i)**: `P₁(t) = (1 - t)(1 - 3t)`. -/
theorem P₁_eq : P₁ = (1 - X) * (1 - 3 * X) := by
  rw [P₁, Matrix.det_fin_two]
  simp [Matrix.diagonal]
  ring

/-- `F₁` is the image of the integer matrix of `P₁`. -/
lemma P₁_eval (t : ℂ) :
    (P₁.map (Int.castRingHom ℂ)).eval t = Matrix.det (1 - t • F₁) := by
  rw [P₁_eq, Matrix.det_fin_two]
  simp [F₁, Matrix.diagonal]
  ring

/-- The zeta function `Z(t) = Πᵢ det(1 - F t | Hⁱ)^((-1)^(i+1))`, as a function of `t`. -/
noncomputable def Z (t : ℂ) : ℂ :=
  Matrix.det (1 - t • F₁) / ((1 - t * 1) * (1 - t * 3))

/-- **`prop:formal-curve` (i)**: `Z(t) = P₁(t) / ((1 - t)(1 - q t))`. -/
theorem Z_eq (t : ℂ) :
    Z t = (P₁.map (Int.castRingHom ℂ)).eval t / ((1 - t) * (1 - q * t)) := by
  rw [Z, P₁_eval, q]; ring_nf

/-- **`prop:formal-curve` (i)**: the functional equation `q t² P₁(1/(qt)) = P₁(t)`. -/
theorem P₁_funct {t : ℂ} (ht : t ≠ 0) :
    q * t ^ 2 * (P₁.map (Int.castRingHom ℂ)).eval (1 / (q * t)) =
      (P₁.map (Int.castRingHom ℂ)).eval t := by
  simp only [P₁_eq, q, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_ofNat, eval_mul, eval_sub, eval_one, eval_X, eval_ofNat]
  field_simp
  ring

/-- **`prop:formal-curve` (ii)**: the eigenvalues of `F` on `H¹` are `3` and `1`. -/
theorem hasEigenvalue_F₁_iff (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' F₁) μ ↔ μ = 3 ∨ μ = 1 := by
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hFv := hv.apply_eq_smul
    rw [Matrix.toLin'_apply, F₁_mulVec] at hFv
    have h0 : 3 * v 0 = μ * v 0 := by
      have := congrFun hFv 0
      simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] using this
    have h1 : v 1 = μ * v 1 := by
      have := congrFun hFv 1
      simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        using this
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1; apply hv.2; ext i; fin_cases i <;> simp [hv0, hv1]
      right
      have : (μ - 1) * v 1 = 0 := by linear_combination -h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv1)
    · left
      have : (μ - 3) * v 0 = 0 := by linear_combination -h0
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv0))
  · rintro (rfl | rfl)
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single 0 1) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, F₁_mulVec]
        ext i; fin_cases i <;> simp
      · simp
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single 1 1) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, F₁_mulVec]
        ext i; fin_cases i <;> simp
      · simp

/-- **`prop:formal-curve` (ii)**: no eigenvalue of `F` on `H¹` has modulus `q^(1/2) = √3`. -/
theorem norm_ne_sqrt_of_hasEigenvalue {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' F₁) μ) : ‖μ‖ ≠ Real.sqrt 3 := by
  rcases (hasEigenvalue_F₁_iff μ).1 hμ with rfl | rfl
  · intro h
    have : (3 : ℝ) = Real.sqrt 3 := by simpa using h
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    rw [← this] at hs
    norm_num at hs
  · intro h
    have : (1 : ℝ) = Real.sqrt 3 := by simpa using h
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    rw [← this] at hs
    norm_num at hs

/-- The Hermitian form with Gram matrix `G`, linear in the first argument: `h(u, v) = v* G u`. -/
def hermForm (G : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ) : ℂ := star v ⬝ᵥ (G *ᵥ u)

/-- `h` is Frobenius compatible of weight one: `h(Fu, Fv) = q h(u, v)`. -/
def FrobCompatible (G : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ u v : Fin 2 → ℂ, hermForm G (F₁ *ᵥ u) (F₁ *ᵥ v) = q * hermForm G u v

lemma hermForm_apply (G : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ) :
    hermForm G u v = star (v 0) * (G 0 0 * u 0 + G 0 1 * u 1) +
      star (v 1) * (G 1 0 * u 0 + G 1 1 * u 1) := by
  simp [hermForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`prop:formal-curve` (iii)**: a Hermitian form is Frobenius compatible iff
`h(e₁, e₁) = h(e₂, e₂) = 0`. -/
theorem frobCompatible_iff (G : Matrix (Fin 2) (Fin 2) ℂ) :
    FrobCompatible G ↔ hermForm G (Pi.single 0 1) (Pi.single 0 1) = 0 ∧
      hermForm G (Pi.single 1 1) (Pi.single 1 1) = 0 := by
  simp only [hermForm_apply]
  simp
  constructor
  · intro h
    have h0 := h (Pi.single 0 1) (Pi.single 0 1)
    have h1 := h (Pi.single 1 1) (Pi.single 1 1)
    simp only [F₁_mulVec, hermForm_apply, q] at h0 h1
    simp at h0 h1
    refine ⟨?_, ?_⟩
    · linear_combination h0 / 2
    · linear_combination -h1 / 2
  · rintro ⟨h0, h1⟩ u v
    simp only [F₁_mulVec, hermForm_apply, q]
    simp [h0, h1]
    ring

/-- The shape of a Frobenius-compatible Hermitian Gram matrix: `[[0, c], [c̄, 0]]`, with `c ≠ 0`
when the form is nonzero. -/
lemma shape_of_frobCompatible {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.IsHermitian)
    (hF : FrobCompatible G) (hne : G ≠ 0) :
    G 0 0 = 0 ∧ G 1 1 = 0 ∧ G 1 0 = star (G 0 1) ∧ G 0 1 ≠ 0 := by
  obtain ⟨h0, h1⟩ := (frobCompatible_iff G).1 hF
  simp [hermForm_apply] at h0 h1
  have h10 : G 1 0 = star (G 0 1) := by
    simpa using (congrFun (congrFun hG.eq 1) 0).symm
  refine ⟨h0, h1, h10, fun hc => hne ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [h0, h1, hc, h10]

/-- **`prop:formal-curve` (iii)**: a nonzero Frobenius-compatible Hermitian form is
nondegenerate. -/
theorem det_ne_zero_of_frobCompatible {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.IsHermitian)
    (hF : FrobCompatible G) (hne : G ≠ 0) : G.det ≠ 0 := by
  obtain ⟨h0, h1, h10, hc⟩ := shape_of_frobCompatible hG hF hne
  rw [Matrix.det_fin_two, h0, h1, h10]
  intro hd
  have : G 0 1 * star (G 0 1) = 0 := by linear_combination -hd
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at this
  exact hc this

lemma hermForm_self_shape {G : Matrix (Fin 2) (Fin 2) ℂ} (h0 : G 0 0 = 0) (h1 : G 1 1 = 0)
    (h10 : G 1 0 = star (G 0 1)) (s : ℝ) :
    (hermForm G ![1, s * star (G 0 1)] ![1, s * star (G 0 1)]).re =
      2 * s * Complex.normSq (G 0 1) := by
  rw [hermForm_apply, h0, h1, h10]
  simp [Complex.normSq_apply]
  ring

/-- **`prop:formal-curve` (iii)**: a nonzero Frobenius-compatible Hermitian form has a positive
direction. -/
theorem exists_pos_of_frobCompatible {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.IsHermitian)
    (hF : FrobCompatible G) (hne : G ≠ 0) : ∃ u, 0 < (hermForm G u u).re := by
  obtain ⟨h0, h1, h10, hc⟩ := shape_of_frobCompatible hG hF hne
  refine ⟨![1, ((1 : ℝ) : ℂ) * star (G 0 1)], ?_⟩
  rw [hermForm_self_shape h0 h1 h10 1]
  have := Complex.normSq_pos.2 hc
  linarith

/-- **`prop:formal-curve` (iii)**: a nonzero Frobenius-compatible Hermitian form has a negative
direction; with `exists_pos_of_frobCompatible`, its signature is `(1, 1)`. -/
theorem exists_neg_of_frobCompatible {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.IsHermitian)
    (hF : FrobCompatible G) (hne : G ≠ 0) : ∃ u, (hermForm G u u).re < 0 := by
  obtain ⟨h0, h1, h10, hc⟩ := shape_of_frobCompatible hG hF hne
  refine ⟨![1, ((-1 : ℝ) : ℂ) * star (G 0 1)], ?_⟩
  rw [hermForm_self_shape h0 h1 h10 (-1)]
  have := Complex.normSq_pos.2 hc
  linarith

/-- **`prop:formal-curve` (iii)**: no Frobenius-compatible Hermitian form is positive
definite. -/
theorem not_posDef_of_frobCompatible {G : Matrix (Fin 2) (Fin 2) ℂ}
    (hF : FrobCompatible G) : ¬ G.PosDef := by
  intro hP
  obtain ⟨h0, -⟩ := (frobCompatible_iff G).1 hF
  have := hP.dotProduct_mulVec_pos (x := Pi.single 0 1) (by simp)
  simp [hermForm_apply] at h0
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, h0] at this

/-- The element `a·1 + bη` of the subalgebra `H⁰ ⊕ H²` of algebraic classes, from `(a, b)`. -/
def alg (u : Fin 2 → ℂ) : H := (u 0, 0, u 1)

/-- The pairing `(a·1 + bη, a'·1 + b'η) ↦ ab' + ba'` on `H⁰ ⊕ H²`. -/
def algPair (u v : Fin 2 → ℂ) : ℂ := u 0 * v 1 + u 1 * v 0

/-- **`prop:formal-curve` (iv)** (proof): the pairing is `Tr(u ∪ v)` restricted to `H⁰ ⊕ H²`,
and `H⁰ ⊕ H²` is closed under the cup product. -/
theorem algPair_eq_tr_mul (u v : Fin 2 → ℂ) : algPair u v = tr (mul (alg u) (alg v)) ∧
    mul (alg u) (alg v) = alg ![u 0 * v 0, u 0 * v 1 + u 1 * v 0] := by
  refine ⟨by simp [algPair, tr, mul, alg], ?_⟩
  simp [mul, alg]

/-- **`prop:formal-curve` (iv)**: the pairing on `H⁰ ⊕ H²` is nondegenerate. -/
theorem algPair_nondegenerate (u : Fin 2 → ℂ) (h : ∀ v, algPair u v = 0) : u = 0 := by
  have h0 := h (Pi.single 1 1)
  have h1 := h (Pi.single 0 1)
  simp [algPair] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

/-- The matrix `diag(1, 3)` of `F` on `H⁰ ⊕ H²` in the basis `1, η`. -/
def Falg : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 3]

lemma Falg_mulVec (u : Fin 2 → ℂ) : Falg *ᵥ u = ![u 0, 3 * u 1] := by
  ext i; fin_cases i <;> simp [Falg, Matrix.mulVec_diagonal]

/-- `Falg` is `F` restricted to `H⁰ ⊕ H²`. -/
theorem F_alg (u : Fin 2 → ℂ) : F (alg u) = alg (Falg *ᵥ u) := by
  rw [Falg_mulVec]
  simp [F, alg]

/-- **`prop:formal-curve` (iv)**: the pairing is `F`-compatible of weight one. -/
theorem algPair_F (u v : Fin 2 → ℂ) : algPair (Falg *ᵥ u) (Falg *ᵥ v) = q * algPair u v := by
  rw [Falg_mulVec, Falg_mulVec]
  simp [algPair, q]
  ring

/-- **`prop:formal-curve` (iv)**: the eigenvalues of `F` on `H⁰ ⊕ H²` are `1` and `q = 3`. -/
theorem hasEigenvalue_Falg_iff (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toLin' Falg) μ ↔ μ = 1 ∨ μ = 3 := by
  constructor
  · intro hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hFv := hv.apply_eq_smul
    rw [Matrix.toLin'_apply, Falg_mulVec] at hFv
    have h0 : v 0 = μ * v 0 := by
      have := congrFun hFv 0
      simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] using this
    have h1 : 3 * v 1 = μ * v 1 := by
      have := congrFun hFv 1
      simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        using this
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1; apply hv.2; ext i; fin_cases i <;> simp [hv0, hv1]
      right
      have : (μ - 3) * v 1 = 0 := by linear_combination -h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv1)
    · left
      have : (μ - 1) * v 0 = 0 := by linear_combination -h0
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv0)
  · rintro (rfl | rfl)
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single 0 1) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Falg_mulVec]
        ext i; fin_cases i <;> simp
      · simp
    · refine Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single 1 1) ⟨?_, ?_⟩
      · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Falg_mulVec]
        ext i; fin_cases i <;> simp
      · simp

/-- **`prop:formal-curve` (iv)**: `F` is semisimple on `H⁰ ⊕ H²`, in the encoding of
`WeilConverse.lean`: its eigenspaces span. -/
theorem iSup_eigenspace_Falg : ⨆ μ, Module.End.eigenspace (Matrix.toLin' Falg) μ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    ext i; fin_cases i <;> simp
  rw [hx]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · refine Submodule.mem_iSup_of_mem 1 ?_
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Falg_mulVec]
    ext i; fin_cases i <;> simp
  · refine Submodule.mem_iSup_of_mem 3 ?_
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Falg_mulVec]
    ext i; fin_cases i <;> simp

end WeilRH.FormalCurve
