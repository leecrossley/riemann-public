/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Three linear-algebra obstructions: Serre's quaternion lemma and two BSD gaps

Source: the manuscript `latex/notes.tex`, `prop:R5` (Serre), `prop:bsd-positive-gap` and
`prop:bsd-jordan-gap`.

## Main results

* `WeilRH.LinearGaps.isEmpty_antihom`: **`prop:R5`**, there is no unital ring antihomomorphism
  `ℍ → M₂(ℝ)`. An antihomomorphism is encoded as a ring homomorphism into the opposite ring
  `M₂(ℝ)ᵐᵒᵖ`; `RingHom` is unital by definition.
* `WeilRH.LinearGaps.bsd_positive_gap`: **`prop:bsd-positive-gap`**, for every `r` and `k > 0`
  a positive Hermitian space with `Θ + Θ* = 2`, an isometric `ℂ^r ↪ ker(Θ - 1)`, and
  `dim ker(Θ - 1) = r + k`.
* `WeilRH.LinearGaps.rootMultiplicity_charpoly_jordan`,
  `WeilRH.LinearGaps.finrank_ker_jordan_sub_one`: **`prop:bsd-jordan-gap`**, for
  `J = [[1, 1], [0, 1]]`, `ord_{s=1} det(s - J) = 2` while `dim ker(J - 1) = 1`.

The proof of `prop:R5` differs from the manuscript's. The manuscript builds an algebra
isomorphism `ℍ ≅ M₂(ℝ)` from `X = ψ(i)`, `Y = ψ(j)` and uses that `M₂(ℝ)` has a nilpotent. Here
`X² = Y² = -1` and `XY = -YX` are shown to have no solution in `M₂(ℝ)` directly, from the
`(0,0)` entries alone: with `X = [[a, b], [c, ·]]`, `Y = [[p, f], [g, ·]]` they read
`a² + bc = -1`, `p² + fg = -1`, `2ap + bg + cf = 0`, and the form `a² + bc` has only one negative
direction, while `X` and `Y` would span a negative definite plane (Lagrange's identity).
-/

open Matrix

namespace WeilRH.LinearGaps

/-! ### `prop:R5` -/

/-- Two real `2 × 2` matrices with `X² = Y² = -1` cannot anticommute. -/
theorem not_anticomm (X Y : Matrix (Fin 2) (Fin 2) ℝ) (hX : X * X = -1) (hY : Y * Y = -1) :
    Y * X ≠ -(X * Y) := by
  intro hXY
  have hQX := congrFun (congrFun hX 0) 0
  have hQY := congrFun (congrFun hY 0) 0
  have hB := congrFun (congrFun hXY 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hQX hQY hB
  set a := X 0 0; set b := X 0 1; set c := X 1 0
  set p := Y 0 0; set f := Y 0 1; set g := Y 1 0
  -- The `(0,0)` entries: `a² + bc = -1`, `p² + fg = -1`, `2ap + bg + cf = 0`.
  have hB' : 2 * (a * p) + b * g + c * f = 0 := by linarith
  -- Coordinates `u = (b + c)/2`, `v = (b - c)/2` give `Q = a² + u² - v²`; the Gram identity
  -- `(a u' - p u)² = 1 - v² - v'²` then contradicts `v², v'² ≥ 1`.
  have E : (a * ((f + g) / 2) - p * ((b + c) / 2)) ^ 2 + ((b - c) / 2) ^ 2 + ((f - g) / 2) ^ 2
      - 1 = 0 := by
    linear_combination (p * p + f * g + 1 + ((f - g) / 2) ^ 2 - 1) * hQX
      + (((b - c) / 2) ^ 2 - 1) * hQY
      - (a * p + (b * g + c * f) / 2 + 2 * ((b - c) / 2) * ((f - g) / 2)) * (hB' / 2)
  nlinarith [sq_nonneg (a * ((f + g) / 2) - p * ((b + c) / 2)), sq_nonneg a, sq_nonneg p,
    sq_nonneg (b + c), sq_nonneg (f + g)]

/-- **`prop:R5`** (Serre): there is no unital ring antihomomorphism `ℍ → M₂(ℝ)`. -/
theorem isEmpty_antihom : IsEmpty (Quaternion ℝ →+* (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ) := by
  refine ⟨fun φ => ?_⟩
  let qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  have hi : qi * qi = -1 := by ext <;> simp [qi]
  have hj : qj * qj = -1 := by ext <;> simp [qj]
  have hij : qi * qj = -(qj * qi) := by ext <;> simp [qi, qj]
  set X := MulOpposite.unop (φ qi)
  set Y := MulOpposite.unop (φ qj)
  have hX : X * X = -1 := by
    simp only [X, ← MulOpposite.unop_mul, ← map_mul, hi, map_neg, map_one]; rfl
  have hY : Y * Y = -1 := by
    simp only [Y, ← MulOpposite.unop_mul, ← map_mul, hj, map_neg, map_one]; rfl
  have hXY : Y * X = -(X * Y) := by
    have h1 : MulOpposite.unop (φ (qi * qj)) = Y * X := by
      rw [map_mul, MulOpposite.unop_mul]
    have h2 : MulOpposite.unop (φ (-(qj * qi))) = -(X * Y) := by
      rw [map_neg, map_mul, MulOpposite.unop_neg, MulOpposite.unop_mul]
    rw [← h1, ← h2, hij]
  exact not_anticomm X Y hX hY hXY

/-! ### `prop:bsd-positive-gap` -/

/-- **`prop:bsd-positive-gap`**: for every `r` and `k > 0` there are a positive Hermitian space
`V`, an operator `Θ` with `Θ + Θ* = 2`, and an isometric injection `ℂ^r ↪ ker(Θ - 1)`, but
`dim ker(Θ - 1) = r + k`. -/
theorem bsd_positive_gap (r k : ℕ) (_hk : 0 < k) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (_ : FiniteDimensional ℂ V) (Θ : V →ₗ[ℂ] V)
      (ι : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ] V),
      (∀ x, ι x ∈ LinearMap.ker (Θ - 1)) ∧ Θ + LinearMap.adjoint Θ = 2 ∧
        Module.finrank ℂ (LinearMap.ker (Θ - 1)) = r + k := by
  refine ⟨EuclideanSpace ℂ (Fin (r + k)), inferInstance, inferInstance, inferInstance, 1,
    ?_, ?_, ?_, ?_⟩
  · -- include the first `r` coordinates
    exact
      { toFun := fun x => WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (0 : Fin k → ℂ))
        map_add' := by
          intro x y; ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
        map_smul' := by
          intro c x; ext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
        norm_map' := by
          intro x
          simp only [EuclideanSpace.norm_eq, LinearMap.coe_mk, AddHom.coe_mk]
          rw [Fin.sum_univ_add]
          simp }
  · intro x; simp
  · rw [LinearMap.adjoint_one]; norm_num [two_smul]
  · rw [sub_self, LinearMap.ker_zero, finrank_top, finrank_euclideanSpace_fin]

/-! ### `prop:bsd-jordan-gap` -/

/-- The Jordan matrix `J = [[1, 1], [0, 1]]` of `prop:bsd-jordan-gap`. -/
def jordanJ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]

/-- `det(s - J) = (s - 1)²`. -/
theorem charpoly_jordanJ : jordanJ.charpoly = (Polynomial.X - Polynomial.C 1) ^ 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp [jordanJ, sq]

/-- **`prop:bsd-jordan-gap`**, first clause: `ord_{s=1} det(s - J) = 2`. -/
theorem rootMultiplicity_charpoly_jordan : jordanJ.charpoly.rootMultiplicity 1 = 2 := by
  rw [charpoly_jordanJ, Polynomial.rootMultiplicity_X_sub_C_pow]

/-- The kernel of `J - 1` is the line through the first basis vector. -/
theorem ker_jordan_sub_one :
    LinearMap.ker (Matrix.toLin' (jordanJ - 1)) = ℂ ∙ (Pi.single 0 1 : Fin 2 → ℂ) := by
  ext v
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  constructor
  · intro hv
    have h0 := congrFun hv 0
    simp [jordanJ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    refine ⟨v 0, ?_⟩
    ext i; fin_cases i <;> simp [h0]
  · rintro ⟨c, rfl⟩
    ext i; fin_cases i <;> simp [jordanJ, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`prop:bsd-jordan-gap`**, second clause: `dim ker(J - 1) = 1`. -/
theorem finrank_ker_jordan_sub_one :
    Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (jordanJ - 1))) = 1 := by
  rw [ker_jordan_sub_one, finrank_span_singleton]
  intro h; simpa using congrFun h 0

end WeilRH.LinearGaps
