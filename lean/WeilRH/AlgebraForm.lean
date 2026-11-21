/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Hermitian

/-!
# The algebra form AW4-E of positivity (Q2 Theorem 1′)

Source: `ai/2026-09-25-finite-field-calibration/report.md`, §2 ("positive involution"), §4
Theorem 1′ (Kleiman 1968 Lemma 4.6(2); Milne 2016 Cor. 1.29) and Remark 4.4 (AW4-V vs AW4-E).

## Design (lean-design-definitions)

A finite-dimensional complex algebra `A` with an antilinear anti-involution `†` is Mathlib's
`[Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]` (`star` is additive, anti-multiplicative,
involutive, and `star (c • a) = conj c • star a`). A **positive trace** (`WeilRH.PositiveTrace`) is
a linear functional `τ : A →ₗ[ℂ] ℂ` with `τ(ab) = τ(ba)`, `τ(a†) = conj τ(a)` and
`0 < Re τ(a a†)` for `a ≠ 0` (Q2 §2 asks `τ(a a†) > 0`; realness of `τ(a a†)` follows from the
other two axioms, so we only require the real part to be positive). The Hermitian form of the proof
is `⟨a, b⟩ = τ(a b†)`, linear in `a` (report convention).

The report states Theorem 1′ over `k ∈ {ℚ, ℝ, ℂ}` and reduces to `k = ℂ` by `A ⊗_k ℂ`. We formalize
the `k = ℂ` case (the one the proof actually runs on); the base change from `ℚ`/`ℝ` (extending
`†` antilinearly and checking positive definiteness of the Hermitian extension) is **not**
formalized.

## Main results

* `PositiveTrace.form`: `⟨a, b⟩ = τ(a b†)` as a `PosHermForm`.
* `PositiveTrace.star_mul_self_eq`: in finite dimension, `g g† = c` (`c ≠ 0`) ⇒ `g† g = c`.
* `PositiveTrace.form_mulLeft_mulLeft`: `⟨g a, g b⟩ = q^j ⟨a, b⟩` if `g g† = q^j`.
* `PositiveTrace.norm_eq_rpow_of_mulLeft` / `isSemisimple_mulLeft` (**Q2 Theorem 1′**): every
  eigenvalue `α` of `L_g` has `‖α‖ = q^{j/2}` and `L_g` is semisimple.
* `PositiveTrace.minpoly_mulLeft` / `minpoly_squarefree` / `norm_eq_rpow_of_isRoot_minpoly`: the
  minimal polynomial of `g` equals that of `L_g`, is squarefree (separable over `ℂ`), and all its
  complex roots have modulus `q^{j/2}`, as in Theorem 1′. (The last clause of Theorem 1′,
  `ρ(g†) = conj ρ(g)`, is not formalized.)
* `PositiveTrace.form_P_mulLeft` / `re_eq_half_of_mulLeft` / `isSemisimple_mulLeft_of_add_star`
  (**AW4-E, additive form**, Remark 4.4): `Θ + Θ† = j` ⇒ `L_Θ` satisfies (P) of weight `j`, so its
  eigenvalues have `Re ρ = j/2` and it is semisimple.
* `matrixTrace`: `Matrix n n ℂ` with `† = ᴴ` and `τ = trace` is a positive trace (the hypotheses
  are satisfiable), and `matrix_norm_eq_rpow` is Theorem 1′ for matrix algebras.
-/

open scoped ComplexConjugate ComplexOrder

namespace WeilRH

/-- A **positive trace** on a complex `*`-algebra (Q2 §2): a trace functional `τ` with
`τ(a†) = conj τ(a)` for which `†` is a positive involution, `0 < Re τ(a a†)` for `a ≠ 0`. -/
structure PositiveTrace (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] where
  /-- The trace functional `τ`. -/
  τ : A →ₗ[ℂ] ℂ
  /-- `τ` is a trace: `τ(ab) = τ(ba)`. -/
  τ_comm : ∀ a b, τ (a * b) = τ (b * a)
  /-- `τ(a†) = conj τ(a)`. -/
  τ_star : ∀ a, τ (star a) = conj (τ a)
  /-- Positivity of the involution: `0 < Re τ(a a†)` for `a ≠ 0`. -/
  τ_pos : ∀ a, a ≠ 0 → 0 < (τ (a * star a)).re

namespace PositiveTrace

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (P : PositiveTrace A)

/-- The Hermitian form `⟨a, b⟩ = τ(a b†)` of Q2 Theorem 1′ (linear in `a`). -/
def form : PosHermForm A where
  toFun a b := P.τ (a * star b)
  add_left a a' b := by simp [add_mul]
  smul_left c a b := by simp
  conj_symm a b := by rw [← P.τ_star, star_mul, star_star]
  re_pos a ha := P.τ_pos a ha

lemma form_apply (a b : A) : P.form.toFun a b = P.τ (a * star b) := rfl

omit [StarModule ℂ A] in
/-- In a finite-dimensional algebra, a right inverse is a left inverse: `g g† = c` with `c ≠ 0`
forces `g† g = c`. -/
theorem star_mul_self_eq [FiniteDimensional ℂ A] {g : A} {c : ℂ} (hc : c ≠ 0)
    (hg : g * star g = c • (1 : A)) : star g * g = c • (1 : A) := by
  have h1 : Algebra.lmul ℂ A g * Algebra.lmul ℂ A (c⁻¹ • star g) = 1 := by
    rw [← map_mul, mul_smul_comm, hg, smul_smul, inv_mul_cancel₀ hc, one_smul, map_one]
  have h2 := (mul_eq_one_comm (M := Module.End ℂ A)).1 h1
  rw [← map_mul] at h2
  have h3 : c⁻¹ • (star g * g) = 1 := by
    have := congrArg (fun f : Module.End ℂ A => f 1) h2
    simpa [Algebra.coe_lmul_eq_mul, smul_mul_assoc] using this
  calc star g * g = c • (c⁻¹ • (star g * g)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • (1 : A) := by rw [h3]

/-- **Weil identity for `L_g`.** If `g g† = q^j` then `⟨g a, g b⟩ = q^j ⟨a, b⟩`. -/
theorem form_mulLeft_mulLeft [FiniteDimensional ℂ A] {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) (a b : A) :
    P.form.toFun (Algebra.lmul ℂ A g a) (Algebra.lmul ℂ A g b) =
      ((q ^ j : ℝ) : ℂ) * P.form.toFun a b := by
  have hc : ((q ^ j : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hq j).ne'
  have hg' := star_mul_self_eq hc hg
  simp only [form_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', star_mul]
  rw [show g * a * (star b * star g) = g * (a * star b * star g) by noncomm_ring, P.τ_comm,
    show a * star b * star g * g = a * star b * (star g * g) by noncomm_ring, hg',
    mul_smul_comm, mul_one, map_smul, smul_eq_mul]

include P in
/-- **Q2 Theorem 1′ (moduli).** If `g g† = q^j` with `q > 0`, every eigenvalue `α` of left
multiplication `L_g` satisfies `‖α‖ = q^{j/2}`. -/
theorem norm_eq_rpow_of_mulLeft [FiniteDimensional ℂ A] {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) {α : ℂ}
    (hα : (Algebra.lmul ℂ A g).HasEigenvalue α) : ‖α‖ = q ^ (j / 2) :=
  (P.form).norm_eq_rpow _ q j hq (P.form_mulLeft_mulLeft hq hg) hα

include P in
/-- **Q2 Theorem 1′ (semisimplicity).** `L_g` is semisimple. -/
theorem isSemisimple_mulLeft [FiniteDimensional ℂ A] {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) : (Algebra.lmul ℂ A g).IsSemisimple :=
  (P.form).isSemisimple_of_weil _ q j hq (P.form_mulLeft_mulLeft hq hg)

omit [StarRing A] [StarModule ℂ A] in
/-- The minimal polynomial of `g` equals that of `L_g` (`Algebra.lmul` is injective). -/
theorem minpoly_mulLeft (g : A) : minpoly ℂ (Algebra.lmul ℂ A g) = minpoly ℂ g :=
  minpoly.algHom_eq _ Algebra.lmul_injective g

include P in
/-- **Q2 Theorem 1′ (separability).** The minimal polynomial of `g` is squarefree. -/
theorem minpoly_squarefree [FiniteDimensional ℂ A] {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) : Squarefree (minpoly ℂ g) := by
  rw [← minpoly_mulLeft]
  exact (P.isSemisimple_mulLeft hq hg).minpoly_squarefree

/-- **AW4-E, additive form (Q2 Remark 4.4).** If `Θ + Θ† = j` in `A`, left multiplication `L_Θ`
satisfies (P) with weight `j` for `⟨a, b⟩ = τ(a b†)`. -/
theorem form_P_mulLeft {Θ : A} {j : ℝ} (hΘ : Θ + star Θ = (j : ℂ) • (1 : A)) (a b : A) :
    P.form.toFun (Algebra.lmul ℂ A Θ a) b + P.form.toFun a (Algebra.lmul ℂ A Θ b) =
      (j : ℂ) * P.form.toFun a b := by
  simp only [form_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', star_mul]
  have e1 : P.τ (Θ * a * star b) = P.τ (a * star b * Θ) := by rw [mul_assoc, P.τ_comm]
  have e2 : a * star b * Θ + a * (star b * star Θ) = (j : ℂ) • (a * star b) := by
    rw [show a * star b * Θ + a * (star b * star Θ) = a * star b * (Θ + star Θ) by noncomm_ring,
      hΘ, mul_smul_comm, mul_one]
  rw [e1, ← map_add, e2, map_smul, smul_eq_mul]

include P in
/-- **AW4-E ⇒ purity (Q2 Remark 4.4).** If `Θ + Θ† = j`, every eigenvalue of `L_Θ` has real part
`j / 2`. -/
theorem re_eq_half_of_mulLeft {Θ : A} {j : ℝ} (hΘ : Θ + star Θ = (j : ℂ) • (1 : A)) {ρ : ℂ}
    (hρ : (Algebra.lmul ℂ A Θ).HasEigenvalue ρ) : ρ.re = j / 2 :=
  (P.form).re_eq_half _ j (P.form_P_mulLeft hΘ) hρ

include P in
/-- **AW4-E ⇒ semisimplicity.** If `Θ + Θ† = j`, `L_Θ` is semisimple. -/
theorem isSemisimple_mulLeft_of_add_star [FiniteDimensional ℂ A] {Θ : A} {j : ℝ}
    (hΘ : Θ + star Θ = (j : ℂ) • (1 : A)) : (Algebra.lmul ℂ A Θ).IsSemisimple :=
  (P.form).isSemisimple _ j (P.form_P_mulLeft hΘ)

include P in
/-- **Q2 Theorem 1′ (roots of the minimal polynomial).** Every complex root `α` of the minimal
polynomial of `g` has `‖α‖ = q^{j/2}`. -/
theorem norm_eq_rpow_of_isRoot_minpoly [FiniteDimensional ℂ A] {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) {α : ℂ} (hα : (minpoly ℂ g).IsRoot α) :
    ‖α‖ = q ^ (j / 2) := by
  refine P.norm_eq_rpow_of_mulLeft hq hg ?_
  rw [Module.End.hasEigenvalue_iff_isRoot, minpoly_mulLeft]
  exact hα

/-! ### Representations (`prop:algebra-form` (ii), `k = ℂ`) -/

section Representation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

include P in
/-- **`prop:algebra-form` (ii), semisimplicity** (Kleiman 1968, Lemma 4.6; `k = ℂ`). For any unital
`ℂ`-algebra map `ι : A → End V`, `ι(g)` is semisimple when `g g† = q^j`: it is killed by the
squarefree minimal polynomial of `g`. Injectivity of `ι` is not needed. -/
theorem rep_isSemisimple [FiniteDimensional ℂ A] (ι : A →ₐ[ℂ] Module.End ℂ V) {g : A} {q j : ℝ}
    (hq : 0 < q) (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) : (ι g).IsSemisimple :=
  Module.End.isSemisimple_of_squarefree_aeval_eq_zero (P.minpoly_squarefree hq hg)
    (by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero])

include P in
/-- **`prop:algebra-form` (ii), moduli** (`k = ℂ`). Every eigenvalue of `ι(g)` has modulus
`q^{j/2}`: it is a root of the minimal polynomial of `ι(g)`, which divides that of `g`. -/
theorem rep_norm_eq_rpow [FiniteDimensional ℂ A] [FiniteDimensional ℂ V]
    (ι : A →ₐ[ℂ] Module.End ℂ V) {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) {α : ℂ} (hα : (ι g).HasEigenvalue α) :
    ‖α‖ = q ^ (j / 2) := by
  have hdvd : minpoly ℂ (ι g) ∣ minpoly ℂ g :=
    minpoly.dvd ℂ (ι g) (by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero])
  refine P.norm_eq_rpow_of_isRoot_minpoly hq hg ?_
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd
    ((Module.End.hasEigenvalue_iff_isRoot).1 hα)

include P in
/-- **`prop:algebra-form` (ii), diagonalizability** (`k = ℂ`): the eigenspaces of `ι(g)` span `V`. -/
theorem rep_iSup_eigenspace [FiniteDimensional ℂ A] [FiniteDimensional ℂ V]
    (ι : A →ₐ[ℂ] Module.End ℂ V) {g : A} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : A)) : ⨆ α, (ι g).eigenspace α = ⊤ := by
  have hs := (P.rep_isSemisimple ι hq hg).isFinitelySemisimple
  rw [← (ι g).iSup_maxGenEigenspace_eq_top]
  exact iSup_congr fun μ => (hs.maxGenEigenspace_eq_eigenspace μ).symm

end Representation

end PositiveTrace

/-! ### Matrix algebras -/

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Matrix n n ℂ` with `† = ᴴ` (conjugate transpose) and `τ = trace` is a positive trace. -/
noncomputable def matrixTrace : PositiveTrace (Matrix n n ℂ) where
  τ := Matrix.traceLinearMap n ℂ ℂ
  τ_comm a b := Matrix.trace_mul_comm a b
  τ_star a := by simp [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  τ_pos a ha := by
    have h0 : 0 ≤ (a * star a).trace := (Matrix.posSemidef_self_mul_conjTranspose a).trace_nonneg
    have h1 : (a * star a).trace ≠ 0 := fun h => ha (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.1 h)
    exact (Complex.pos_iff.1 (lt_of_le_of_ne h0 (Ne.symm h1))).1

/-- **Q2 Theorem 1′ for matrix algebras.** If `g gᴴ = q^j` (`q > 0`), every eigenvalue of left
multiplication by `g` on `Matrix n n ℂ` has modulus `q^{j/2}`. -/
theorem matrix_norm_eq_rpow {g : Matrix n n ℂ} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : Matrix n n ℂ)) {α : ℂ}
    (hα : (Algebra.lmul ℂ (Matrix n n ℂ) g).HasEigenvalue α) : ‖α‖ = q ^ (j / 2) :=
  PositiveTrace.norm_eq_rpow_of_mulLeft matrixTrace hq hg hα

/-- **Q2 Theorem 1′ for matrix algebras (semisimplicity).** -/
theorem matrix_isSemisimple {g : Matrix n n ℂ} {q j : ℝ} (hq : 0 < q)
    (hg : g * star g = ((q ^ j : ℝ) : ℂ) • (1 : Matrix n n ℂ)) :
    (Algebra.lmul ℂ (Matrix n n ℂ) g).IsSemisimple :=
  PositiveTrace.isSemisimple_mulLeft matrixTrace hq hg

end Matrix

end WeilRH
