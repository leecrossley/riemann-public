/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Positivity of a tensor product of Hermitian forms (Künneth report, Prop. 5 / Theorem 6(ii))

Source: `ai/2026-09-25-arithmetic-kunneth-conjecture/report.md`, Prop. 5 (the tensor product of
positive definite forms is positive definite; Gram matrix = Kronecker product) and the proof of
Theorem 6(ii)/(iii) (a tensor product of Hermitian forms of signatures `(p, q)`, `(p', q')` has
signature `(pp' + qq', pq' + qp')`, so `h ⊗ h` is positive definite iff `pq = 0`).

We work with Gram matrices: a Hermitian form on `ℂⁿ` is a Hermitian matrix `A`, the tensor product
form on `ℂⁿ ⊗ ℂᵐ = ℂ^{n×m}` is the Kronecker product `A ⊗ₖ B`, and "positive definite" is Mathlib's
`Matrix.PosDef` (for the scoped order `ComplexOrder`).

## Main results

* `WeilRH.star_dotProduct_kronecker_mulVec`: on a pure tensor `x ⊗ y`,
  `(x ⊗ y)ᴴ (A ⊗ₖ B) (x ⊗ y) = (xᴴ A x) (yᴴ B y)`.
* `WeilRH.posDef_kronecker_iff`: for Hermitian `A`, `B` on nonempty index types,
  `A ⊗ₖ B` is positive definite iff `A`, `B` are both positive definite or both negative definite.
  (No nondegeneracy hypothesis is needed; positivity on pure tensors already forces this.)
* `WeilRH.posDef_kronecker_self_iff`: `A ⊗ₖ A` is positive definite iff `A` is definite.

The full signature formula `(pp' + qq', pq' + qp')` is **not** formalized (see `lean/README.md`);
only the positive-definiteness case used by Theorem 6 is.
-/

open Matrix
open scoped Kronecker ComplexOrder ComplexConjugate

namespace WeilRH

variable {n m : Type*}

/-- The pure tensor `x ⊗ y` as a vector indexed by `n × m`. -/
def pureTensor (x : n → ℂ) (y : m → ℂ) : n × m → ℂ := fun p => x p.1 * y p.2

lemma pureTensor_ne_zero {x : n → ℂ} {y : m → ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    pureTensor x y ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  intro h
  have := congrFun h (i, j)
  simp [pureTensor] at this
  tauto

variable [Fintype n] [Fintype m]

/-- The quadratic form of a Kronecker product on a pure tensor is the product of the quadratic
forms. -/
theorem star_dotProduct_kronecker_mulVec (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (x : n → ℂ) (y : m → ℂ) :
    star (pureTensor x y) ⬝ᵥ ((A ⊗ₖ B) *ᵥ pureTensor x y) =
      (star x ⬝ᵥ (A *ᵥ x)) * (star y ⬝ᵥ (B *ᵥ y)) := by
  simp only [dotProduct, mulVec, pureTensor, kroneckerMap_apply, Pi.star_apply, star_mul',
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Fintype.sum_congr _ _ fun _ => Fintype.sum_congr _ _ fun _ => by ring

/-- For a Hermitian matrix the quadratic form is real. -/
lemma im_quad_eq_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 :=
  hA.im_star_dotProduct_mulVec_self x

/-- Positive definiteness in terms of real parts of the quadratic form. -/
lemma posDef_iff_re {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨fun h x hx => (Complex.pos_iff.1 (h.2 hx)).1, fun h => ⟨hA, fun x hx => ?_⟩⟩
  exact Complex.pos_iff.2 ⟨h x hx, (im_quad_eq_zero hA x).symm⟩

/-- Negative definiteness (`-A` positive definite) in terms of real parts. -/
lemma neg_posDef_iff_re {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (-A).PosDef ↔ ∀ x : n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).re < 0 := by
  rw [posDef_iff_re hA.neg]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  simp [neg_mulVec, dotProduct_neg]

omit [Fintype n] in
lemma exists_ne_zero_vec [Nonempty n] : ∃ x : n → ℂ, x ≠ 0 :=
  ⟨fun _ => 1, fun h => by simpa using congrFun h (Classical.arbitrary n)⟩

/-- **Tensor positivity (Künneth report, Prop. 5 and Theorem 6(ii)).** For Hermitian `A`, `B` on
nonempty index types, the tensor-product form `A ⊗ₖ B` is positive definite iff `A` and `B` are
definite of the same sign. -/
theorem posDef_kronecker_iff [Nonempty n] [Nonempty m] {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).PosDef ↔ (A.PosDef ∧ B.PosDef) ∨ ((-A).PosDef ∧ (-B).PosDef) := by
  constructor
  · intro h
    have hAB : ∀ x y, x ≠ 0 → y ≠ 0 →
        0 < (star x ⬝ᵥ (A *ᵥ x)).re * (star y ⬝ᵥ (B *ᵥ y)).re := by
      intro x y hx hy
      have := (Complex.pos_iff.1 (h.dotProduct_mulVec_pos (pureTensor_ne_zero hx hy))).1
      rw [star_dotProduct_kronecker_mulVec, Complex.mul_re, im_quad_eq_zero hA,
        im_quad_eq_zero hB] at this
      simpa using this
    obtain ⟨x₀, hx₀⟩ := exists_ne_zero_vec (n := n)
    obtain ⟨y₀, hy₀⟩ := exists_ne_zero_vec (n := m)
    · by_cases hb : 0 < (star y₀ ⬝ᵥ (B *ᵥ y₀)).re
      · left
        have hApos : ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (A *ᵥ x)).re := fun x hx =>
          pos_of_mul_pos_left (hAB x y₀ hx hy₀) hb.le
        refine ⟨(posDef_iff_re hA).2 hApos, (posDef_iff_re hB).2 fun y hy => ?_⟩
        exact pos_of_mul_pos_right (hAB x₀ y hx₀ hy) (hApos x₀ hx₀).le
      · right
        push Not at hb
        have hb' : (star y₀ ⬝ᵥ (B *ᵥ y₀)).re < 0 := by
          rcases hb.lt_or_eq with hb | hb
          · exact hb
          · have := hAB x₀ y₀ hx₀ hy₀; rw [hb, mul_zero] at this; exact absurd this (lt_irrefl 0)
        have hAneg : ∀ x : n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).re < 0 := fun x hx => by
          have := hAB x y₀ hx hy₀
          nlinarith
        refine ⟨(neg_posDef_iff_re hA).2 hAneg, (neg_posDef_iff_re hB).2 fun y hy => ?_⟩
        have := hAB x₀ y hx₀ hy
        have := hAneg x₀ hx₀
        nlinarith
  · rintro (⟨hA', hB'⟩ | ⟨hA', hB'⟩)
    · exact hA'.kronecker hB'
    · have e : (-A) ⊗ₖ (-B) = A ⊗ₖ B := by ext; simp [kroneckerMap_apply]
      simpa [e] using hA'.kronecker hB'

/-- **Theorem 6(ii)/(iii), matrix core.** `A ⊗ₖ A` is positive definite iff `A` is definite
(positive or negative): for a signature `(p, q)` form the negative index of `h ⊗ h` is `2pq`. -/
theorem posDef_kronecker_self_iff [Nonempty n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A ⊗ₖ A).PosDef ↔ A.PosDef ∨ (-A).PosDef := by
  rw [posDef_kronecker_iff hA hA, and_self, and_self]

end WeilRH
