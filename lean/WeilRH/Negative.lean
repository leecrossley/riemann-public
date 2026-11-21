/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Negative results R2, R3, R12

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §3, Findings R2, R3, R12.

* **R2.** On `ℂ⁴` with `λ = 1/2 + a + iT`, `Θ = diag(λ, λ̄, 1-λ, 1-λ̄)`, the alternating form
  `Ω`, and the quaternionic structure `J v = S v̄` satisfy `Θᵀ Ω + Ω Θ = Ω`, `S S̄ = -1`,
  `Θ S = S Θ̄`; the induced Hermitian form `h(v, w) = vᵀ H w̄`, `H = Ω S`, is nondegenerate
  (`H² = 1`), has trace `0`, satisfies identity (P) with `j = 1`, yet is indefinite and `Θ` has
  the off-critical eigenvalue `λ` (`Re λ = 1/2 + a ≠ 1/2` when `a ≠ 0`). So duality plus a
  quaternionic structure plus (P) for an *indefinite* form do not force purity: positivity is
  essential. We prove this for all real `a`, `T` (the report takes `0 < a < 1/2`, `T > 0`;
  only `a ≠ 0` is used for the off-critical conclusion).
* **R3.** `det(s - Θ) = w⁴ + 2(T² - a²) w² + (T² + a²)²` with `w = s - 1/2`, it is invariant
  under `s ↦ 1 - s`, and for `T ≠ 0` it does not vanish at real `s`, so every integer twist
  `Θ - n` is invertible (the cones `[V → V]` are contractible).
* **`prop:R2-star` (iii).** No antilinear `J'` with `ΘJ' = J'Θ` makes `B(v, J'w) = vᵀΩJ'w` a
  positive definite Hermitian form (`not_exists_posStar`): (P) would force `Re λ = 1/2`.
* **`prop:R2-frob`.** `F = q^Θ` satisfies `Fᵀ Ω F = q Ω`, `F J = J F`, `J² = -1`, and its eigenvalues
  have moduli `q^{1/2+a}` and `q^{1/2-a}` (`WeilRH.R2.frob_counterexample`).
* **R12.** `cos z + cosh a` vanishes at `π ± i a`, and it is the Fourier transform
  `∫ e^{i z t} dμ(t)` of the positive measure `μ = cosh(a) δ₀ + (δ₁ + δ₋₁)/2`.

Conventions: the Hermitian form of R2 is `h(v, w) = vᵀ H w̄`, linear in the first argument,
as in the report. Complex conjugation of a matrix is `M.map conj`.
-/

open Matrix Complex
open scoped ComplexOrder
open scoped ComplexConjugate

namespace WeilRH.R2

variable (a T : ℝ)

/-- `λ = 1/2 + a + i T`. -/
noncomputable def lam : ℂ := 1 / 2 + a + T * I

/-- `Θ = diag(λ, λ̄, 1 - λ, 1 - λ̄)`. -/
noncomputable def Θ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![lam a T, 0, 0, 0;
     0, conj (lam a T), 0, 0;
     0, 0, 1 - lam a T, 0;
     0, 0, 0, 1 - conj (lam a T)]

/-- `Ω = [[0, I₂], [-I₂, 0]]`. -/
def Ω : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     -1, 0, 0, 0;
     0, -1, 0, 0]

/-- `S = diag(R, R)`, `R = [[0, -1], [1, 0]]`. -/
def S : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- `H = Ω S = [[0, R], [-R, 0]]`. -/
def H : Matrix (Fin 4) (Fin 4) ℂ := Ω * S

/-- The Hermitian form `h(v, w) = vᵀ H w̄` (linear in `v`). -/
def h (v w : Fin 4 → ℂ) : ℂ := v ⬝ᵥ (H *ᵥ (fun i => conj (w i)))

lemma H_eq : H = !![0, 0, 0, -1;
                   0, 0, 1, 0;
                   0, 1, 0, 0;
                   -1, 0, 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [H, Ω, S, mul_apply, Fin.sum_univ_four]

/-- Weight-one alternating duality: `Θᵀ Ω + Ω Θ = Ω`. -/
theorem duality : (Θ a T)ᵀ * Ω + Ω * Θ a T = Ω := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Θ, Ω, mul_apply, Fin.sum_univ_four] <;> ring

/-- Quaternionic structure: `S S̄ = -1`. -/
theorem quaternionic : S * S.map conj = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S, mul_apply, Fin.sum_univ_four]

/-- `J` commutes with the flow: `Θ S = S Θ̄`. -/
theorem commutes : Θ a T * S = S * (Θ a T).map conj := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Θ, S, mul_apply, Fin.sum_univ_four]

/-- `H` is Hermitian (real symmetric). -/
theorem H_isHermitian : H.IsHermitian := by
  rw [H_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]

/-- `H² = 1`: the form is nondegenerate. -/
theorem H_sq : H * H = 1 := by
  rw [H_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four, one_apply]

/-- `tr H = 0`. -/
theorem H_trace : H.trace = 0 := by
  rw [H_eq]; simp [trace, Fin.sum_univ_four]

/-- (P) with `j = 1` holds for `h`: `Θᵀ H + H Θ̄ = H`, i.e. `h(Θu, v) + h(u, Θv) = h(u, v)`. -/
theorem P_matrix : (Θ a T)ᵀ * H + H * (Θ a T).map conj = H := by
  rw [H, ← Matrix.mul_assoc, Matrix.mul_assoc Ω, ← commutes, ← Matrix.mul_assoc,
    ← Matrix.add_mul, duality]

/-- (P) with `j = 1`, in form language. -/
theorem P (u v : Fin 4 → ℂ) :
    h (Θ a T *ᵥ u) v + h u (Θ a T *ᵥ v) = h u v := by
  have hconj : (fun i => conj ((Θ a T *ᵥ v) i)) = (Θ a T).map conj *ᵥ (fun i => conj (v i)) := by
    ext i
    simp [mulVec, dotProduct, map_sum, Matrix.map_apply]
  have hT : ∀ y : Fin 4 → ℂ, (Θ a T *ᵥ u) ⬝ᵥ y = u ⬝ᵥ ((Θ a T)ᵀ *ᵥ y) := by
    intro y
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  simp only [h, hconj, hT, mulVec_mulVec, ← dotProduct_add, ← add_mulVec, P_matrix]

/-- The form is indefinite: `h(e₁ + f₂, e₁ + f₂) = -2` (`f₂` is the fourth basis vector). -/
theorem h_neg : h ![1, 0, 0, 1] ![1, 0, 0, 1] = -2 := by
  simp [h, H_eq, mulVec, dotProduct, Fin.sum_univ_four]; norm_num

/-- and `h(e₁ - f₂, e₁ - f₂) = 2`. -/
theorem h_pos : h ![1, 0, 0, -1] ![1, 0, 0, -1] = 2 := by
  simp [h, H_eq, mulVec, dotProduct, Fin.sum_univ_four]; norm_num

/-- `λ` is an eigenvalue of `Θ` (eigenvector `e₁`). -/
theorem eigen : Θ a T *ᵥ ![1, 0, 0, 0] = lam a T • ![1, 0, 0, 0] := by
  ext i; fin_cases i <;> simp [Θ, mulVec, dotProduct, Fin.sum_univ_four]

/-- The eigenvalue `λ` is off the critical line when `a ≠ 0`. -/
theorem lam_re_ne (ha : a ≠ 0) : (lam a T).re ≠ 1 / 2 := by
  simp [lam]; exact ha

/-- **R2, packaged.** For every real `a ≠ 0` and every real `T`: weight-one alternating duality,
a quaternionic structure commuting with the flow, a nondegenerate Hermitian form `h` of trace
zero satisfying (P) with `j = 1` — and yet `h` is indefinite and `Θ` has the off-critical
eigenvalue `λ`. -/
theorem counterexample (ha : a ≠ 0) :
    (Θ a T)ᵀ * Ω + Ω * Θ a T = Ω ∧ S * S.map conj = -1 ∧ Θ a T * S = S * (Θ a T).map conj ∧
    H.IsHermitian ∧ H * H = 1 ∧ H.trace = 0 ∧
    (∀ u v, h (Θ a T *ᵥ u) v + h u (Θ a T *ᵥ v) = h u v) ∧
    h ![1, 0, 0, 1] ![1, 0, 0, 1] = -2 ∧
    Θ a T *ᵥ ![1, 0, 0, 0] = lam a T • ![1, 0, 0, 0] ∧ (lam a T).re ≠ 1 / 2 :=
  ⟨duality a T, quaternionic, commutes a T, H_isHermitian, H_sq, H_trace, P a T, h_neg,
    eigen a T, lam_re_ne a T ha⟩

/-! ### R3: the determinant of the R2 block -/

/-- `p(s) = w⁴ + 2(T² - a²) w² + (T² + a²)²` with `w = s - 1/2`. -/
noncomputable def p (s : ℂ) : ℂ :=
  (s - 1 / 2) ^ 4 + 2 * ((T : ℂ) ^ 2 - (a : ℂ) ^ 2) * (s - 1 / 2) ^ 2 + ((T : ℂ) ^ 2 + (a : ℂ) ^ 2) ^ 2

lemma Θ_eq_diagonal :
    Θ a T = diagonal ![lam a T, conj (lam a T), 1 - lam a T, 1 - conj (lam a T)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Θ, diagonal]

lemma conj_lam : conj (lam a T) = 1 / 2 + a - T * I := by
  simp only [lam, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
    map_ofNat]
  ring

/-- **R3.** `det(s - Θ) = ((w - a)² + T²)((w + a)² + T²) = w⁴ + 2(T² - a²)w² + (T² + a²)²`. -/
theorem det_eq (s : ℂ) : (scalar (Fin 4) s - Θ a T).det = p a T s := by
  have hs : scalar (Fin 4) s = diagonal (fun _ => s) := rfl
  rw [Θ_eq_diagonal, hs, diagonal_sub, det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [conj_lam]
  have h1 : (s - lam a T) * (s - (1 / 2 + a - T * I)) = (s - 1 / 2 - a) ^ 2 + (T : ℂ) ^ 2 := by
    simp only [lam]; linear_combination (-(T : ℂ) ^ 2) * I_sq
  have h2 : (s - (1 - lam a T)) * (s - (1 - (1 / 2 + a - T * I))) =
      (s - 1 / 2 + a) ^ 2 + (T : ℂ) ^ 2 := by
    simp only [lam]; linear_combination (-(T : ℂ) ^ 2) * I_sq
  calc (s - lam a T) * (s - (1 / 2 + a - T * I)) * (s - (1 - lam a T)) *
        (s - (1 - (1 / 2 + a - T * I)))
      = ((s - lam a T) * (s - (1 / 2 + a - T * I))) *
        ((s - (1 - lam a T)) * (s - (1 - (1 / 2 + a - T * I)))) := by ring
    _ = p a T s := by rw [h1, h2, p]; ring

/-- **R3.** The determinant is invariant under `s ↦ 1 - s`. -/
theorem p_one_sub (s : ℂ) : p a T (1 - s) = p a T s := by
  simp only [p]; ring

/-- **R3.** For `T ≠ 0`, `p` has no real zeros. -/
theorem p_real_ne_zero (hT : T ≠ 0) (x : ℝ) : p a T x ≠ 0 := by
  have : p a T x = (((x - 1 / 2 - a) ^ 2 + T ^ 2) * ((x - 1 / 2 + a) ^ 2 + T ^ 2) : ℝ) := by
    simp only [p]; push_cast; ring
  rw [this, Complex.ofReal_ne_zero]
  have hT2 : 0 < T ^ 2 := by positivity
  positivity

/-- **R3.** For `T ≠ 0` and every integer `n`, the twist `Θ - n` is invertible, so the cone
`[V --(Θ - n)--> V]` is contractible. -/
theorem isUnit_sub_intCast (hT : T ≠ 0) (n : ℤ) : IsUnit (Θ a T - scalar (Fin 4) (n : ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have : Θ a T - scalar (Fin 4) (n : ℂ) = -(scalar (Fin 4) (n : ℂ) - Θ a T) := by abel
  rw [this, det_neg, det_eq]
  simpa using p_real_ne_zero a T hT n

/-! ### R2, second failed expectation: the positive star `J₊ v = -Ω v̄` -/

/-- The matrix of the antilinear positive star `J₊ v = -Ω v̄`. -/
def Jplus : Matrix (Fin 4) (Fin 4) ℂ := -Ω

/-- `J₊² = -1`: `(-Ω)(-Ω̄) = -1`. -/
theorem Jplus_sq : Jplus * Jplus.map conj = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jplus, Ω, mul_apply, Fin.sum_univ_four]

/-- `B(v, J₊ w) = vᵀ Ω (-Ω) w̄ = vᵀ w̄`: the star is positive (`Ω · (-Ω) = 1`). -/
theorem Ω_mul_Jplus : Ω * Jplus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jplus, Ω, mul_apply, Fin.sum_univ_four, one_apply]

/-- The block swap `[[0, I₂], [I₂, 0]]` (= `|Ω|` entrywise). -/
def swap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- The commutation defect of `J₊` with the flow: `Θ J₊ - J₊ Θ̄ = -2a · [[0, I₂], [I₂, 0]]`; its
four nonzero entries equal `-2a`, of modulus `2|a|`. -/
theorem commDefect_eq : Θ a T * Jplus - Jplus * (Θ a T).map conj = (-2 * a : ℂ) • swap := by
  rw [Θ_eq_diagonal, diagonal_map (map_zero _)]
  ext i j
  simp only [Matrix.sub_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [Jplus, Ω, swap, lam, map_ofNat] <;> ring

/-- The entries of the commutation defect have modulus `0` or `2|a|` (`2a` for `a > 0`). -/
theorem norm_commDefect_apply (i j : Fin 4) :
    ‖(Θ a T * Jplus - Jplus * (Θ a T).map conj) i j‖ = 0 ∨
      ‖(Θ a T * Jplus - Jplus * (Θ a T).map conj) i j‖ = 2 * |a| := by
  rw [commDefect_eq]
  fin_cases i <;> fin_cases j <;> simp [swap]

/-- **R2 (J₊).** For `a ≠ 0` the positive star `J₊` does not commute with the flow. -/
theorem Jplus_not_commute (ha : a ≠ 0) : Θ a T * Jplus ≠ Jplus * (Θ a T).map conj := by
  intro h
  have h' := commDefect_eq a T
  rw [h, sub_self] at h'
  have := congrFun (congrFun h' 0) 2
  simp [swap] at this
  exact ha this

/-! ### `prop:R2-star` (iii): no positive star commuting with the flow -/

/-- The form `h'(v, w) = B(v, J'w) = vᵀ Ω (J'w)` of an antilinear map `J'` (`def:R2-block`:
`B(v, w) = vᵀ Ω w`). -/
def starForm (J' : (Fin 4 → ℂ) →ₗ⋆[ℂ] (Fin 4 → ℂ)) (v w : Fin 4 → ℂ) : ℂ :=
  v ⬝ᵥ (Ω *ᵥ J' w)

/-- If `J'` commutes with `Θ`, the form `h'` satisfies (P) with `j = 1`. -/
theorem starForm_P (J' : (Fin 4 → ℂ) →ₗ⋆[ℂ] (Fin 4 → ℂ))
    (hcomm : ∀ v, Θ a T *ᵥ J' v = J' (Θ a T *ᵥ v)) (v w : Fin 4 → ℂ) :
    starForm J' (Θ a T *ᵥ v) w + starForm J' v (Θ a T *ᵥ w) = starForm J' v w := by
  have hT : ∀ y : Fin 4 → ℂ, (Θ a T *ᵥ v) ⬝ᵥ y = v ⬝ᵥ ((Θ a T)ᵀ *ᵥ y) := by
    intro y
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  simp only [starForm, hT, ← hcomm, mulVec_mulVec, ← dotProduct_add, ← add_mulVec, duality]

/-- **`prop:R2-star` (iii).** For `a ≠ 0` there is no antilinear `J' : V → V` with `ΘJ' = J'Θ`
for which `(v, w) ↦ B(v, J'w)` is a positive definite Hermitian form. (The manuscript assumes
`0 < a < 1/2`, `T > 0`; only `a ≠ 0` is used.) -/
theorem not_exists_posStar (ha : a ≠ 0) :
    ¬ ∃ J' : (Fin 4 → ℂ) →ₗ⋆[ℂ] (Fin 4 → ℂ),
      (∀ v, Θ a T *ᵥ J' v = J' (Θ a T *ᵥ v)) ∧
      (∀ v w, starForm J' w v = conj (starForm J' v w)) ∧
      (∀ v, v ≠ 0 → 0 < starForm J' v v) := by
  rintro ⟨J', hcomm, -, hpos⟩
  set e : Fin 4 → ℂ := ![1, 0, 0, 0]
  have he : e ≠ 0 := by
    intro h; have := congrFun h 0; simp [e] at this
  have hP := starForm_P a T J' hcomm e e
  rw [eigen] at hP
  have h1 : starForm J' (lam a T • e) e = lam a T * starForm J' e e := by
    simp [starForm, smul_dotProduct]
  have h2 : starForm J' e (lam a T • e) = conj (lam a T) * starForm J' e e := by
    simp [starForm, mulVec_smul, dotProduct_smul]
  rw [h1, h2, ← add_mul] at hP
  have hx : starForm J' e e ≠ 0 := (hpos e he).ne'
  have hsum : lam a T + conj (lam a T) = 1 := mul_right_cancel₀ hx (hP.trans (one_mul _).symm)
  apply lam_re_ne a T ha
  have := congrArg Complex.re hsum
  simp [Complex.conj_re] at this
  linarith

/-! ### `prop:R2-frob`: the block transported to `F = q^Θ` -/

/-- The diagonal of `F = q^Θ` (`prop:R2-frob`). -/
noncomputable def frobDiag (q : ℝ) : Fin 4 → ℂ :=
  ![(q : ℂ) ^ lam a T, (q : ℂ) ^ conj (lam a T), (q : ℂ) ^ (1 - lam a T),
    (q : ℂ) ^ (1 - conj (lam a T))]

/-- `F = q^Θ = diag(q^λ, q^λ̄, q^{1-λ}, q^{1-λ̄})` (`prop:R2-frob`). -/
noncomputable def F (q : ℝ) : Matrix (Fin 4) (Fin 4) ℂ := diagonal (frobDiag a T q)

lemma conj_cpow_real {q : ℝ} (hq : 0 < q) (z : ℂ) : conj ((q : ℂ) ^ z) = (q : ℂ) ^ conj z := by
  rw [Complex.cpow_conj _ _ (by simpa [Complex.arg_ofReal_of_nonneg hq.le] using Real.pi_pos.ne)]
  simp

lemma cpow_mul_one_sub {q : ℝ} (hq : 0 < q) (z : ℂ) : (q : ℂ) ^ z * (q : ℂ) ^ (1 - z) = q := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast hq.ne')]; simp

theorem F_transpose_mul_Ω {q : ℝ} (hq : 0 < q) : (F a T q)ᵀ * Ω * F a T q = (q : ℂ) • Ω := by
  have h1 := cpow_mul_one_sub hq (lam a T)
  have h2 := cpow_mul_one_sub hq (conj (lam a T))
  have h1' : (q : ℂ) ^ (1 - lam a T) * (q : ℂ) ^ lam a T = q := by rw [mul_comm, h1]
  have h2' : (q : ℂ) ^ (1 - conj (lam a T)) * (q : ℂ) ^ conj (lam a T) = q := by rw [mul_comm, h2]
  ext i j
  rw [F, diagonal_transpose, mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [Ω, frobDiag, h1, h2, h1', h2']

theorem F_mul_S {q : ℝ} (hq : 0 < q) : F a T q * S = S * (F a T q).map conj := by
  have c1 := conj_cpow_real hq (lam a T)
  have c2 := conj_cpow_real hq (conj (lam a T))
  have c3 := conj_cpow_real hq (1 - lam a T)
  have c4 := conj_cpow_real hq (1 - conj (lam a T))
  simp only [map_sub, map_one, Complex.conj_conj] at c1 c2 c3 c4
  have hm : (F a T q).map conj = diagonal (fun i => conj (frobDiag a T q i)) := by
    simp [F, diagonal_map]
  rw [hm]
  ext i j
  rw [F, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [S, frobDiag, c1, c2, c3, c4]

theorem norm_frobDiag {q : ℝ} (hq : 0 < q) (i : Fin 4) :
    ‖frobDiag a T q i‖ = q ^ (1 / 2 + a) ∨ ‖frobDiag a T q i‖ = q ^ (1 / 2 - a) := by
  fin_cases i <;>
    simp [frobDiag, Complex.norm_cpow_eq_rpow_re_of_pos hq, lam] <;> ring_nf <;> simp

theorem hasEigenvalue_F (q : ℝ) (i : Fin 4) :
    Module.End.HasEigenvalue (toLin' (F a T q)) (frobDiag a T q i) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := Pi.single i 1)
  refine ⟨?_, by simp⟩
  rw [Module.End.mem_eigenspace_iff, toLin'_apply, F]
  ext k
  rw [mulVec_diagonal]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

theorem eq_frobDiag_of_hasEigenvalue {q : ℝ} {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (toLin' (F a T q)) μ) : ∃ i, μ = frobDiag a T q i := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv.2 (funext h)
  refine ⟨i, ?_⟩
  have := congrFun (Module.End.mem_eigenspace_iff.mp hv.1) i
  rw [toLin'_apply, F, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ hi this).symm

/-- **`prop:R2-frob`.** `F = q^Θ` satisfies `Fᵀ Ω F = q Ω`, commutes with `J` (`J v = S v̄`, so
`F J = J F` reads `F S = S F̄`), `J² = -1` (`S S̄ = -1`), and its eigenvalues have moduli
`q^{1/2+a}` and `q^{1/2-a}`, both of which occur. -/
theorem frob_counterexample {q : ℝ} (hq : 0 < q) :
    (F a T q)ᵀ * Ω * F a T q = (q : ℂ) • Ω ∧ F a T q * S = S * (F a T q).map conj ∧
      S * S.map conj = -1 ∧
      (∀ μ, Module.End.HasEigenvalue (toLin' (F a T q)) μ →
        ‖μ‖ = q ^ (1 / 2 + a) ∨ ‖μ‖ = q ^ (1 / 2 - a)) ∧
      (∃ μ, Module.End.HasEigenvalue (toLin' (F a T q)) μ ∧ ‖μ‖ = q ^ (1 / 2 + a)) ∧
      (∃ μ, Module.End.HasEigenvalue (toLin' (F a T q)) μ ∧ ‖μ‖ = q ^ (1 / 2 - a)) := by
  refine ⟨F_transpose_mul_Ω a T hq, F_mul_S a T hq, quaternionic, fun μ hμ => ?_,
    ⟨_, hasEigenvalue_F a T q 0, ?_⟩, ⟨_, hasEigenvalue_F a T q 2, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := eq_frobDiag_of_hasEigenvalue a T hμ
    exact norm_frobDiag a T hq i
  · simp [frobDiag, Complex.norm_cpow_eq_rpow_re_of_pos hq, lam]
  · simp [frobDiag, Complex.norm_cpow_eq_rpow_re_of_pos hq, lam]; ring_nf

end WeilRH.R2

namespace WeilRH.R12

open MeasureTheory

/-- **R12, zeros.** `cos z + cosh a` vanishes at `z = π + i a`. -/
theorem cos_add_cosh_eq_zero_plus (a : ℝ) :
    Complex.cos (Real.pi + a * I) + Complex.cosh a = 0 := by
  rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **R12, zeros.** `cos z + cosh a` vanishes at `z = π - i a`. -/
theorem cos_add_cosh_eq_zero_minus (a : ℝ) :
    Complex.cos (Real.pi - a * I) + Complex.cosh a = 0 := by
  rw [Complex.cos_sub, Complex.cos_mul_I, Complex.sin_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- For `a ≠ 0` these zeros are not real. -/
theorem zero_not_real (a : ℝ) (ha : a ≠ 0) : (Real.pi + a * I).im ≠ 0 := by
  simpa using ha

/-- The positive measure `μ_a = cosh(a) δ₀ + (δ₁ + δ₋₁)/2` on `ℝ`. -/
noncomputable def μ (a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (Real.cosh a) • Measure.dirac 0 + (1 / 2 : ENNReal) • (Measure.dirac 1 + Measure.dirac (-1))

/-- **R12, Fourier positivity.** `cos z + cosh a = ∫ e^{i z t} dμ_a(t)`, with `μ_a` a positive
(finite) measure. -/
theorem fourier_eq (a : ℝ) (z : ℂ) :
    ∫ t, Complex.exp (z * t * I) ∂(μ a) = Complex.cos z + Complex.cosh a := by
  have hint : ∀ x : ℝ, Integrable (fun t : ℝ => Complex.exp (z * t * I)) (Measure.dirac x) :=
    fun x => integrable_dirac (by simp)
  unfold μ
  rw [integral_add_measure ((hint 0).smul_measure (by simp))
      (((hint 1).add_measure (hint (-1))).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_add_measure (hint 1) (hint (-1)),
    integral_dirac, integral_dirac, integral_dirac]
  rw [Complex.cos, ENNReal.toReal_ofReal (Real.cosh_pos a).le]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one,
    mul_one, Complex.ofReal_neg, mul_neg, neg_mul, one_div, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_cosh]
  push_cast
  ring_nf

end WeilRH.R12
