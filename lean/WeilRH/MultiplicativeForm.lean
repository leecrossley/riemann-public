/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.AlgebraForm
import WeilRH.Calibration
import WeilRH.Phantom

/-!
# The multiplicative algebra form AW4-E_F (`def:aw4-EF`, `prop:aw4-EF`, `prop:rosati-EF`)

Source: `latex/notes.tex`, §`subsec:mult-form`: Definition `def:aw4-EF`, Proposition
`prop:aw4-EF` (i)–(iv) and Proposition `prop:rosati-EF`; background Definition
`def:pos-involution`, Proposition `prop:algebra-form`, Definition `def:log-susp`.

## Design (lean-design-definitions)

*Algebra.* Definition `def:aw4-EF`(a) asks for a subalgebra `A ⊂ End_ℂ(V)` containing `id_V` and
`F`, a positive trace involution `(τ, †)` on `A` over `ℂ`, and `F F^† = q^j`. We encode `A` as an
abstract finite-dimensional complex `*`-algebra together with an **injective** unital algebra
map `ι : A →ₐ[ℂ] End_ℂ(V)` and an element `f` with `ι f = F` (`AW4EFDatum`); the subalgebra of the
notes is `ι(A)` with `†` transported along `ι`, so the two formulations are equivalent. The
positive trace involution is the existing `WeilRH.PositiveTrace` (AlgebraForm) — `†` is Mathlib's
`star` (`StarRing`, `StarModule ℂ`), so it is additive, antilinear, product-reversing and
involutive, `τ` is a trace with `τ(a†) = conj τ(a)` and `0 < Re τ(a a†)` for `a ≠ 0`.
`SatisfiesAW4EF V F q j := Nonempty (AW4EFDatum V F q j)`.

*Sheets.* A sheet (`def:aw4-EF`(b)) is `σ : ℂ → ℂ` with `σ(α) ∈ Σ_q(α)`, i.e.
`exp(σ(α) log q) = α` (`WeilRH.progression`), for every eigenvalue `α` of `F` (`IsSheet`). Its
interpolation polynomial `p_σ` (`def:aw4-EF`(d)) is the Lagrange interpolant on the roots of the
minimal polynomial of `f` (= the eigenvalues of `F`), and `θ_σ = p_σ(F)` is `sheetElem`, an element
of `A`. The logarithmic suspension `(V̂, Θ)` itself is **not** built (as in `Calibration.lean`);
the relation `Θ ι_σ = ι_σ θ_σ` of `prop:aw4-EF`(ii) is encoded eigenvector-wise:
`θ_σ` acts on `V_(α) = ker(F - α)` by `σ(α)`, which is `Θ` on `V̂_{σ(α)} = V_(α)`
(`ι_sheetElem_apply`). The `k`-th copy of `Calibration.lean`'s suspension is the sheet
`suspEigen q k` (`isSheet_suspEigen`).

*Finite truncations of `V̂`* (`prop:aw4-EF`(iii)). For finitely many sheets `σ_0, …, σ_{n-1}`
the space `V̂' = ⨁_i V̂_{σ_i}` is `Fin n → V` via the sheet maps, `Θ' = Θ|V̂'` acts on the `i`-th
copy by `ι θ_{σ_i}` (`truncTheta`), the algebra `A'` is `Fin n → A` acting componentwise
(`piRep`, injective), with trace `τ' = ∑_i τ` (`PositiveTrace.pi`) and componentwise `†`.
`AW4EAddDatum` packages the additive algebra form AW4-E on a finite-dimensional `(W, Θ)`.

*Dual* (`prop:aw4-EF`(iv)). `A^t` is `Aᵐᵒᵖ` acting on `V* = Module.Dual ℂ V` by transposition
(`a ↦ (ι a).dualMap`, `transposeRep`, injective), with trace `a^t ↦ τ(a)` and involution
`a^t ↦ (a†)^t` (`PositiveTrace.op`).

## Main results

* `AW4EFDatum.mul_inv`, `inv_mul`, `isSemisimple`, `iSup_eigenspace_eq_top`, `norm_eq`
  (**`prop:aw4-EF`(i)**): `F` invertible with inverse `ι(q^{-j} f^†) ∈ ι(A)`, diagonalizable
  (semisimple and spanned by eigenvectors), all eigenvalues of modulus `q^{j/2}`.
* `AW4EFDatum.ι_sheetElem_apply`, `star_sheetElem` (**`prop:aw4-EF`(ii)**): `θ_σ` acts by `σ(α)`
  on `V_(α)` and `θ_σ^† = j - θ_σ`.
* `AW4EFDatum.truncation` (**`prop:aw4-EF`(iii)**) and `AW4EAddDatum.re_eq_half`,
  `AW4EAddDatum.isSemisimple` (consequence: additive AW4-E ⇒ purity/semisimplicity of `Θ'`);
  `isSheet_add_int` (the sheets `σ + 2πim/log q`).
* `AW4EFDatum.dual` (**`prop:aw4-EF`(iv)**).
* `rosati_aw4EF`, `rosati_gram_posDef` (**`prop:rosati-EF`**, linear-algebra content): an
  abstract positive involution on a complex algebra acting faithfully on `V` with `π π^† = q`
  gives AW4-E_F of weight one; a rational symmetric Gram matrix positive on `ℚⁿ` is positive
  definite as a Hermitian matrix on `ℂⁿ` (the step `(ii)` of the notes' proof). The geometric
  input — `End⁰(J)`, injectivity on `V_ℓ J`, Weil/Milne positivity of the Rosati form and
  `π π^† = q` (Theorem `thm:imp-rosati`) — enters as explicit hypotheses.
-/

open Polynomial Complex
open scoped ComplexConjugate Real ComplexOrder Matrix

namespace WeilRH

universe u

/-! ### The datum -/

/-- **AW4-E_F of weight `j`** (`def:aw4-EF`(a)): a finite-dimensional complex `*`-algebra `A`
with a positive trace involution, acting faithfully and unitally on `V` by `ι`, and `f ∈ A` with
`ι f = F` and `f f^† = q^j`. (The subalgebra `A ⊂ End_ℂ(V)` of the notes is `ι(A)`.) -/
structure AW4EFDatum (V : Type u) [AddCommGroup V] [Module ℂ V] (F : Module.End ℂ V)
    (q j : ℝ) where
  /-- The algebra. -/
  A : Type u
  [ring : Ring A]
  [algebra : Algebra ℂ A]
  [starRing : StarRing A]
  [starModule : StarModule ℂ A]
  /-- The positive trace involution `(τ, †)` (`† = star`). -/
  P : PositiveTrace A
  /-- The (faithful, unital) action on `V`. -/
  ι : A →ₐ[ℂ] Module.End ℂ V
  ι_injective : Function.Injective ι
  /-- The element of `A` acting as `F`. -/
  f : A
  ι_f : ι f = F
  /-- `F F^† = q^j`. -/
  weil : f * star f = ((q ^ j : ℝ) : ℂ) • (1 : A)

attribute [instance] AW4EFDatum.ring AW4EFDatum.algebra AW4EFDatum.starRing
  AW4EFDatum.starModule

/-- `(V, F)` satisfies the multiplicative algebra form AW4-E_F of weight `j`. -/
def SatisfiesAW4EF (V : Type u) [AddCommGroup V] [Module ℂ V] (F : Module.End ℂ V) (q j : ℝ) :
    Prop :=
  Nonempty (AW4EFDatum V F q j)

/-- A **sheet** (`def:aw4-EF`(b)): `σ(α) ∈ Σ_q(α)` for every eigenvalue `α` of `F`. -/
def IsSheet {V : Type*} [AddCommGroup V] [Module ℂ V] (F : Module.End ℂ V) (q : ℝ)
    (σ : ℂ → ℂ) : Prop :=
  ∀ α, F.HasEigenvalue α → σ α ∈ progression q α

/-- The suspended eigenvalues `ρ_k(α) = (log α + 2πik)/log q` of `Calibration.lean` form a sheet
when `F` is invertible. -/
theorem isSheet_suspEigen {V : Type*} [AddCommGroup V] [Module ℂ V] {F : Module.End ℂ V} {q : ℝ}
    (hq : 1 < q) (hF : ∀ α, F.HasEigenvalue α → α ≠ 0) (k : ℤ) :
    IsSheet F q (suspEigen q k) := by
  intro α hα
  simp only [progression, Set.mem_ofPred_eq]
  rw [mul_comm]
  exact exp_suspEigen hq k (hF α hα)

/-- Shifting a sheet by `2πim/log q` gives a sheet (`def:aw4-EF`, remark after (d)). -/
theorem isSheet_add_int {V : Type*} [AddCommGroup V] [Module ℂ V] {F : Module.End ℂ V} {q : ℝ}
    (hq : 1 < q) {σ : ℂ → ℂ} (hσ : IsSheet F q σ) (m : ℤ) :
    IsSheet F q (fun α => σ α + 2 * π * I * m / Real.log q) := by
  intro α hα
  have h := hσ α hα
  simp only [progression, Set.mem_ofPred_eq] at h ⊢
  have hL : (Real.log q : ℂ) ≠ 0 := log_ne_zero_of_one_lt hq
  rw [add_mul, div_mul_cancel₀ _ hL, Complex.exp_add, h,
    show 2 * π * I * (m : ℂ) = m * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- On a sheet, `Re σ(α) = j/2` when `|α| = q^{j/2}`. -/
lemma re_of_mem_progression {q j : ℝ} (hq : 1 < q) {α ρ : ℂ} (hρ : ρ ∈ progression q α)
    (hα : ‖α‖ = q ^ (j / 2)) : ρ.re = j / 2 := by
  simp only [progression, Set.mem_ofPred_eq] at hρ
  have hq0 : 0 < q := by linarith
  rw [← hρ, Complex.norm_exp] at hα
  have : (ρ * Real.log q).re = ρ.re * Real.log q := by simp
  rw [this, Real.rpow_def_of_pos hq0] at hα
  have h := Real.exp_injective hα
  have hL := (Real.log_pos hq).ne'
  field_simp at h
  linarith

/-! ### Star of a polynomial expression -/

section StarAeval

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]


/-- `p(a)^† = p̄(a^†)`, `p̄` having the conjugate coefficients. -/
lemma star_aeval (a : A) (p : ℂ[X]) :
    star (aeval a p) = aeval (star a) (p.map (starRingEnd ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [hp, hr]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, star_mul, star_pow,
      ← algebraMap_star_comm, Algebra.commutes]
    rfl

end StarAeval

/-! ### Positive traces on products and opposites -/

namespace PositiveTrace

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

lemma re_nonneg (P : PositiveTrace A) (a : A) : 0 ≤ (P.τ (a * star a)).re := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · exact (P.τ_pos a ha).le

/-- The positive trace `τ' = ∑_i τ` on the product algebra `ι → A`, with componentwise `†`
(`prop:aw4-EF`(iii)). -/
noncomputable def pi {ι : Type*} [Fintype ι] (P : PositiveTrace A) : PositiveTrace (ι → A) where
  τ := ∑ i, P.τ ∘ₗ LinearMap.proj i
  τ_comm a b := by simp [LinearMap.sum_apply, P.τ_comm]
  τ_star a := by simp [LinearMap.sum_apply, P.τ_star]
  τ_pos a ha := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_proj, Function.eval, Pi.mul_apply, Pi.star_apply, re_sum]
    exact Finset.sum_pos' (fun k _ => P.re_nonneg (a k)) ⟨i, Finset.mem_univ _, P.τ_pos _ hi⟩

instance : StarModule ℂ Aᵐᵒᵖ where
  star_smul c a := MulOpposite.unop_injective (star_smul c a.unop)

/-- The positive trace `a^t ↦ τ(a)` on the opposite algebra `A^t = Aᵐᵒᵖ`, with involution
`a^t ↦ (a^†)^t` (`prop:aw4-EF`(iv)). -/
noncomputable def op (P : PositiveTrace A) : PositiveTrace Aᵐᵒᵖ where
  τ :=
    { toFun := fun a => P.τ a.unop
      map_add' := by simp
      map_smul' := by simp }
  τ_comm a b := by simp [P.τ_comm]
  τ_star a := by simp [P.τ_star]
  τ_pos a ha := by
    have ha' : a.unop ≠ 0 := by simpa using ha
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_mul, MulOpposite.unop_star]
    rw [P.τ_comm]
    exact P.τ_pos _ ha'

end PositiveTrace

/-! ### Consequences of AW4-E_F -/

namespace AW4EFDatum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q j : ℝ} (D : AW4EFDatum V F q j)

instance finiteDimensional : FiniteDimensional ℂ D.A :=
  FiniteDimensional.of_injective D.ι.toLinearMap D.ι_injective

omit [FiniteDimensional ℂ V] in
lemma c_ne_zero (hq : 0 < q) : ((q ^ j : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.rpow_pos_of_pos hq j).ne'

lemma star_mul_self (hq : 0 < q) : star D.f * D.f = ((q ^ j : ℝ) : ℂ) • (1 : D.A) :=
  PositiveTrace.star_mul_self_eq (c_ne_zero (j := j) hq) D.weil

omit [FiniteDimensional ℂ V] in
/-- `F^{-1} = q^{-j} F^†` in `A`: right inverse. -/
theorem mul_inv (hq : 0 < q) : F * D.ι (((q ^ j : ℝ) : ℂ)⁻¹ • star D.f) = 1 := by
  refine Eq.trans (by rw [D.ι_f]) (?_ : D.ι D.f * D.ι (((q ^ j : ℝ) : ℂ)⁻¹ • star D.f) = 1)
  rw [← map_mul, mul_smul_comm, D.weil, smul_smul, inv_mul_cancel₀ (c_ne_zero (j := j) hq),
    one_smul, map_one]

/-- `F^{-1} = q^{-j} F^†` in `A`: left inverse. -/
theorem inv_mul (hq : 0 < q) : D.ι (((q ^ j : ℝ) : ℂ)⁻¹ • star D.f) * F = 1 := by
  refine Eq.trans (by rw [D.ι_f]) (?_ : D.ι (((q ^ j : ℝ) : ℂ)⁻¹ • star D.f) * D.ι D.f = 1)
  rw [← map_mul, smul_mul_assoc, D.star_mul_self hq, smul_smul,
    inv_mul_cancel₀ (c_ne_zero (j := j) hq), one_smul, map_one]

include D in
/-- **`prop:aw4-EF`(i), invertibility.** -/
theorem isUnit (hq : 0 < q) : IsUnit F :=
  ⟨⟨F, _, D.mul_inv hq, D.inv_mul hq⟩, rfl⟩

omit [FiniteDimensional ℂ V] in
include D in
lemma minpoly_eq : minpoly ℂ F = minpoly ℂ D.f := by
  refine Eq.trans (by rw [D.ι_f]) (minpoly.algHom_eq D.ι D.ι_injective D.f)

omit [FiniteDimensional ℂ V] in
include D in
lemma isRoot_of_hasEigenvalue {α : ℂ} (hα : F.HasEigenvalue α) : (minpoly ℂ D.f).IsRoot α := by
  rw [← D.minpoly_eq]
  exact Module.End.isRoot_of_hasEigenvalue hα

include D in
/-- **`prop:aw4-EF`(i), purity.** Every eigenvalue of `F` has modulus `q^{j/2}`. -/
theorem norm_eq (hq : 0 < q) {α : ℂ} (hα : F.HasEigenvalue α) : ‖α‖ = q ^ (j / 2) :=
  D.P.norm_eq_rpow_of_isRoot_minpoly hq D.weil (D.isRoot_of_hasEigenvalue hα)

include D in
/-- **`prop:aw4-EF`(i), semisimplicity.** -/
theorem isSemisimple (hq : 0 < q) : F.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (D.P.minpoly_squarefree hq D.weil) ?_
  rw [← D.minpoly_eq]
  exact minpoly.aeval ℂ F

include D in
/-- **`prop:aw4-EF`(i), diagonalizability.** The eigenspaces of `F` span `V`. -/
theorem iSup_eigenspace_eq_top (hq : 0 < q) : ⨆ α, F.eigenspace α = ⊤ :=
  (D.isSemisimple hq).iSup_eigenspace_eq_top

/-- `F^†` acts on `ker(F - α)` by `ᾱ`. -/
lemma ι_star_f_apply (hq : 0 < q) {α : ℂ} {v : V} (hv : F v = α • v) :
    D.ι (star D.f) v = conj α • v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hα : F.HasEigenvalue α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hn := D.norm_eq hq hα
  have hα0 : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact (Real.rpow_pos_of_pos hq _).ne' hn.symm
  have key : D.ι (star D.f) (F v) = ((q ^ j : ℝ) : ℂ) • v := by
    have h1 := congrArg D.ι (D.star_mul_self hq)
    rw [map_mul, map_smul, map_one, D.ι_f] at h1
    have := congrArg (fun g : Module.End ℂ V => g v) h1
    simpa only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] using this
  rw [hv, map_smul] at key
  have hc : ((q ^ j : ℝ) : ℂ) = α * conj α := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, ← Real.rpow_natCast,
      ← Real.rpow_mul hq.le]
    norm_num
  rw [hc, ← smul_smul] at key
  exact smul_right_injective V hα0 key

/-! #### Sheets (`prop:aw4-EF`(ii)) -/

/-- The interpolation polynomial `p_σ` of a sheet (`def:aw4-EF`(d)): `p_σ(α) = σ(α)` on the
eigenvalues `α` of `F` (the roots of the minimal polynomial of `f`). -/
noncomputable def sheetPoly (σ : ℂ → ℂ) : ℂ[X] :=
  Lagrange.interpolate (minpoly ℂ D.f).roots.toFinset id σ

/-- `θ_σ = p_σ(F) ∈ A`. -/
noncomputable def sheetElem (σ : ℂ → ℂ) : D.A := aeval D.f (D.sheetPoly σ)

lemma eval_sheetPoly (σ : ℂ → ℂ) {α : ℂ} (hα : F.HasEigenvalue α) :
    (D.sheetPoly σ).eval α = σ α := by
  have hroot : α ∈ (minpoly ℂ D.f).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots
      (minpoly.ne_zero (Algebra.IsIntegral.isIntegral D.f))]
    exact D.isRoot_of_hasEigenvalue hα
  exact Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hroot

/-- **`prop:aw4-EF`(ii), `Θ ι_σ = ι_σ θ_σ`.** `θ_σ` acts on `V_(α) = ker(F - α)` by `σ(α)`. -/
theorem ι_sheetElem_apply (σ : ℂ → ℂ) {α : ℂ} {v : V} (hv : F v = α • v) :
    D.ι (D.sheetElem σ) v = σ α • v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hα : F.HasEigenvalue α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  rw [sheetElem, ← Polynomial.aeval_algHom_apply, D.ι_f,
    Module.End.aeval_apply_of_mem_apply_eq_smul hv, D.eval_sheetPoly σ hα]

/-- Two elements of `A` agreeing on every eigenvector of `F` are equal. -/
lemma ext_of_eigen (hq : 0 < q) {a b : D.A}
    (h : ∀ (α : ℂ) (v : V), F v = α • v → D.ι a v = D.ι b v) : a = b := by
  apply D.ι_injective
  ext x
  have hx : x ∈ ⨆ α, F.eigenspace α := (D.iSup_eigenspace_eq_top hq) ▸ Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun x => D.ι a x = D.ι b x) _ hx ?_ ?_ ?_
  · intro α v hv
    exact h α v (Module.End.mem_eigenspace_iff.1 hv)
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- **`prop:aw4-EF`(ii), additive relation.** For a sheet `σ`, `θ_σ^† = j - θ_σ`. -/
theorem star_sheetElem (hq : 1 < q) {σ : ℂ → ℂ} (hσ : IsSheet F q σ) :
    star (D.sheetElem σ) = (j : ℂ) • (1 : D.A) - D.sheetElem σ := by
  have hq0 : 0 < q := by linarith
  refine D.ext_of_eigen hq0 fun α v hv => ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hα : F.HasEigenvalue α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hre := re_of_mem_progression hq (hσ α hα) (D.norm_eq hq0 hα)
  rw [sheetElem, star_aeval, ← Polynomial.aeval_algHom_apply,
    Module.End.aeval_apply_of_mem_apply_eq_smul (D.ι_star_f_apply hq0 hv), eval_map,
    eval₂_at_apply, ← sheetElem, map_sub, LinearMap.sub_apply, D.ι_sheetElem_apply σ hv,
    D.eval_sheetPoly σ hα, map_smul, map_one, LinearMap.smul_apply, Module.End.one_apply,
    ← sub_smul]
  congr 1
  apply Complex.ext <;> simp [hre]
  ring

/-! #### The dual (`prop:aw4-EF`(iv)) -/

/-- Transposition `A^t → End(V*)`, `a^t ↦ (ι a)^t`, as an algebra map on `Aᵐᵒᵖ`. -/
noncomputable def transposeRep : D.Aᵐᵒᵖ →ₐ[ℂ] Module.End ℂ (Module.Dual ℂ V) where
  toFun a := (D.ι a.unop).dualMap
  map_one' := by simp; rfl
  map_mul' a b := by
    simp only [MulOpposite.unop_mul, map_mul]
    rfl
  map_zero' := by ext; simp
  map_add' a b := by ext; simp
  commutes' c := by
    ext φ v
    simp [Algebra.algebraMap_eq_smul_one]

lemma transposeRep_injective : Function.Injective D.transposeRep := by
  intro a b h
  apply MulOpposite.unop_injective
  apply D.ι_injective
  ext v
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ (D.ι a.unop v - D.ι b.unop v) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact sub_ne_zero.2 hne (Module.forall_dual_apply_eq_zero_iff ℂ _ |>.1 hall)
  have := congrArg (fun g : Module.End ℂ (Module.Dual ℂ V) => g φ v) h
  simp only [transposeRep, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.dualMap_apply] at this
  exact hφ (by rw [map_sub, this, sub_self])

/-- **`prop:aw4-EF`(iv).** The dual `(V*, F^t)` satisfies AW4-E_F of weight `j` with the algebra
`A^t = Aᵐᵒᵖ`, the trace `a^t ↦ τ(a)` and the involution `a^t ↦ (a^†)^t`. -/
noncomputable def dual (hq : 0 < q) : AW4EFDatum (Module.Dual ℂ V) F.dualMap q j where
  A := D.Aᵐᵒᵖ
  P := D.P.op
  ι := D.transposeRep
  ι_injective := D.transposeRep_injective
  f := MulOpposite.op D.f
  ι_f := by simp [transposeRep, D.ι_f]
  weil := by
    apply MulOpposite.unop_injective
    simp [D.star_mul_self hq]

end AW4EFDatum

/-! ### The additive algebra form AW4-E and finite truncations (`prop:aw4-EF`(iii)) -/

/-- **The additive algebra form AW4-E of weight `j`** on a finite-dimensional `(W, Θ)`: a
finite-dimensional complex `*`-algebra with positive trace involution acting faithfully on `W`,
containing `θ` with `ι θ = Θ` and `θ^† = j - θ`. -/
structure AW4EAddDatum (W : Type u) [AddCommGroup W] [Module ℂ W] (Θ : Module.End ℂ W)
    (j : ℝ) where
  /-- The algebra. -/
  A : Type u
  [ring : Ring A]
  [algebra : Algebra ℂ A]
  [starRing : StarRing A]
  [starModule : StarModule ℂ A]
  /-- The positive trace involution. -/
  P : PositiveTrace A
  /-- The faithful action on `W`. -/
  ι : A →ₐ[ℂ] Module.End ℂ W
  ι_injective : Function.Injective ι
  /-- The element acting as `Θ`. -/
  θ : A
  ι_θ : ι θ = Θ
  /-- `θ^† = j - θ`. -/
  add_star : star θ = (j : ℂ) • (1 : A) - θ

attribute [instance] AW4EAddDatum.ring AW4EAddDatum.algebra AW4EAddDatum.starRing
  AW4EAddDatum.starModule

namespace AW4EAddDatum

variable {W : Type u} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {Θ : Module.End ℂ W}
  {j : ℝ} (D : AW4EAddDatum W Θ j)

instance finiteDimensional : FiniteDimensional ℂ D.A :=
  FiniteDimensional.of_injective D.ι.toLinearMap D.ι_injective

omit [FiniteDimensional ℂ W] in
lemma add_star' : D.θ + star D.θ = (j : ℂ) • (1 : D.A) := by
  rw [D.add_star]; abel

omit [FiniteDimensional ℂ W] in
lemma minpoly_eq : minpoly ℂ Θ = minpoly ℂ (Algebra.lmul ℂ D.A D.θ) := by
  refine Eq.trans (by rw [D.ι_θ] : minpoly ℂ Θ = minpoly ℂ (D.ι D.θ)) ?_
  rw [minpoly.algHom_eq D.ι D.ι_injective, PositiveTrace.minpoly_mulLeft]

include D in
/-- **AW4-E ⇒ purity.** Every eigenvalue of `Θ` has real part `j/2`. -/
theorem re_eq_half {ρ : ℂ} (hρ : Θ.HasEigenvalue ρ) : ρ.re = j / 2 := by
  refine D.P.re_eq_half_of_mulLeft D.add_star' ?_
  rw [Module.End.hasEigenvalue_iff_isRoot, ← D.minpoly_eq]
  exact Module.End.isRoot_of_hasEigenvalue hρ

include D in
/-- **AW4-E ⇒ semisimplicity** of `Θ`. -/
theorem isSemisimple : Θ.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := minpoly ℂ (Algebra.lmul ℂ D.A D.θ)) ?_ ?_
  · exact (D.P.isSemisimple_mulLeft_of_add_star D.add_star').minpoly_squarefree
  · rw [← D.minpoly_eq]; exact minpoly.aeval ℂ Θ

end AW4EAddDatum

section Truncation

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {A : Type u} [Ring A] [Algebra ℂ A]

/-- The componentwise action of `Fin n → A` on `Fin n → V`. -/
noncomputable def piRep (n : ℕ) (ι : A →ₐ[ℂ] Module.End ℂ V) :
    (Fin n → A) →ₐ[ℂ] Module.End ℂ (Fin n → V) where
  toFun x := LinearMap.pi fun i => ι (x i) ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' c := by ext; simp [Algebra.algebraMap_eq_smul_one]

lemma piRep_apply (n : ℕ) (ι : A →ₐ[ℂ] Module.End ℂ V) (x : Fin n → A) (v : Fin n → V)
    (i : Fin n) : piRep n ι x v i = ι (x i) (v i) := rfl

lemma piRep_injective (n : ℕ) {ι : A →ₐ[ℂ] Module.End ℂ V} (hι : Function.Injective ι) :
    Function.Injective (piRep n ι) := by
  intro x y h
  funext i
  apply hι
  ext v
  have := congrArg (fun g : Module.End ℂ (Fin n → V) => g (Pi.single i v) i) h
  simpa [piRep_apply] using this

end Truncation

namespace AW4EFDatum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q j : ℝ} (D : AW4EFDatum V F q j)

/-- `Θ' = Θ|V̂'` on the truncation `V̂' = ⨁_{i<n} V̂_{σ_i} ≅ Fin n → V`: it acts on the `i`-th
copy by `θ_{σ_i}`. -/
noncomputable def truncTheta {n : ℕ} (σ : Fin n → ℂ → ℂ) : Module.End ℂ (Fin n → V) :=
  piRep n D.ι (fun i => D.sheetElem (σ i))

/-- `Θ'` acts on the `i`-th copy of `v ∈ V_(α)` by `σ_i(α)`: it is `Θ` on `V̂_{σ_i(α)}`. -/
theorem truncTheta_apply {n : ℕ} (σ : Fin n → ℂ → ℂ) {α : ℂ} {v : V} (hv : F v = α • v)
    (i : Fin n) (w : Fin n → V) (hw : w i = v) : D.truncTheta σ w i = σ i α • v := by
  rw [truncTheta, piRep_apply, hw, D.ι_sheetElem_apply _ hv]

/-- **`prop:aw4-EF`(iii).** For finitely many sheets `σ_0, …, σ_{n-1}`, the finite-dimensional
truncation `V̂' ≅ Fin n → V` with `Θ' = Θ|V̂'` satisfies the additive algebra form AW4-E of
weight `j`, with `A' = Fin n → A` acting componentwise, `τ' = ∑ τ` and componentwise `†`. -/
noncomputable def truncation (hq : 1 < q) {n : ℕ} (σ : Fin n → ℂ → ℂ)
    (hσ : ∀ i, IsSheet F q (σ i)) : AW4EAddDatum (Fin n → V) (D.truncTheta σ) j where
  A := Fin n → D.A
  P := D.P.pi
  ι := piRep n D.ι
  ι_injective := piRep_injective n D.ι_injective
  θ := fun i => D.sheetElem (σ i)
  ι_θ := rfl
  add_star := by
    funext i
    simp [D.star_sheetElem hq (hσ i)]

/-- **`prop:aw4-EF`(iii) ⇒ purity of the suspension.** On every finite truncation, `Θ'` is
semisimple and its eigenvalues have real part `j/2`. -/
theorem truncTheta_re_eq_half (hq : 1 < q) {n : ℕ} (σ : Fin n → ℂ → ℂ)
    (hσ : ∀ i, IsSheet F q (σ i)) {ρ : ℂ} (hρ : (D.truncTheta σ).HasEigenvalue ρ) :
    ρ.re = j / 2 :=
  (D.truncation hq σ hσ).re_eq_half hρ

end AW4EFDatum

/-! ### A concrete AW4-E_F datum -/

namespace AW4EFDatum

/-- **A concrete AW4-E_F datum** (`def:aw4-EF`(a)): `V = ℂ^n`, `F = α·1` with `α ᾱ = q^j`,
`A = M_n(ℂ)` acting by matrices, `(τ, †) = (trace, conjugate transpose)` (`matrixTrace`) and
`f = α·1`. -/
noncomputable def scalarModel (n : Type) [Fintype n] [DecidableEq n] (q j : ℝ) (α : ℂ)
    (hα : α * star α = ((q ^ j : ℝ) : ℂ)) :
    AW4EFDatum (n → ℂ) (α • (1 : Module.End ℂ (n → ℂ))) q j where
  A := Matrix n n ℂ
  P := matrixTrace
  ι := (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)).toAlgHom
  ι_injective := (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)).injective
  f := α • (1 : Matrix n n ℂ)
  ι_f := by simp
  weil := by rw [star_smul, star_one, smul_mul_smul_comm, one_mul, hα]

lemma rpow_half_mul_star {q j : ℝ} (hq : 0 < q) :
    ((q ^ (j / 2) : ℝ) : ℂ) * star ((q ^ (j / 2) : ℝ) : ℂ) = ((q ^ j : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.rpow_add hq]
  norm_num

/-- `F = q^{j/2}·1` on `ℂ^n` satisfies AW4-E_F of weight `j`. -/
theorem satisfiesAW4EF_scalar (n : Type) [Fintype n] [DecidableEq n] {q : ℝ} (hq : 0 < q)
    (j : ℝ) :
    SatisfiesAW4EF (n → ℂ) (((q ^ (j / 2) : ℝ) : ℂ) • (1 : Module.End ℂ (n → ℂ))) q j :=
  ⟨scalarModel n q j _ (rpow_half_mul_star hq)⟩

/-- **Nonvacuity of `AW4EFDatum`**: for every `q > 0` and weight `j` there is a nonzero space with
an AW4-E_F datum. -/
theorem exists_nontrivial {q : ℝ} (hq : 0 < q) (j : ℝ) :
    ∃ F : Module.End ℂ (Fin 1 → ℂ), Nontrivial (Fin 1 → ℂ) ∧ SatisfiesAW4EF (Fin 1 → ℂ) F q j :=
  ⟨_, inferInstance, satisfiesAW4EF_scalar (Fin 1) hq j⟩

end AW4EFDatum

/-! ### `prop:rosati-EF` -/

section Rosati

/-- **`prop:rosati-EF`(iii), abstract form.** Let `A` be a complex `*`-algebra with a positive
trace involution (in the notes, the image of `End⁰(J) ⊗ ℂ` with the complexified Rosati
involution and `τ` the trace on `V`: item (ii), a hypothesis here), acting faithfully on `V`
(item (i), a hypothesis here), and let `π ∈ A` satisfy `π π^† = q` (Theorem `thm:imp-rosati`(iii),
a hypothesis here). Then `(V, ι π)` satisfies AW4-E_F of weight one. -/
noncomputable def rosati_aw4EF {V : Type u} [AddCommGroup V] [Module ℂ V] {A : Type u} [Ring A]
    [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (P : PositiveTrace A)
    (ι : A →ₐ[ℂ] Module.End ℂ V) (hι : Function.Injective ι) (fr : A) {q : ℝ}
    (hfr : fr * star fr = (q : ℂ) • (1 : A)) : AW4EFDatum V (ι fr) q 1 where
  A := A
  P := P
  ι := ι
  ι_injective := hι
  f := fr
  ι_f := rfl
  weil := by rw [Real.rpow_one]; exact hfr

/-- **`prop:rosati-EF`(ii), linear-algebra step.** A symmetric rational matrix `G` with
`xᵀ G x > 0` for all nonzero `x ∈ ℚⁿ` (the Gram matrix `Tr(a_i a_k^†)` of the Rosati form in a
`ℚ`-basis, positive by Weil/Milne: a hypothesis) is positive definite as a Hermitian matrix on
`ℂⁿ`: `∑_{i,k} z̄_i G_{ik} z_k > 0` for `z ≠ 0`. -/
theorem rosati_gram_posDef {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℚ)
    (hsymm : G.IsSymm) (hpos : ∀ x : n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x) :
    (G.map (fun r : ℚ => (r : ℂ))).PosDef := by
  classical
  set GR : Matrix n n ℝ := G.map (fun r : ℚ => (r : ℝ)) with hGR
  -- the rational quadratic form, read over `ℝ`
  have hcast : ∀ y : n → ℚ, (fun i => (y i : ℝ)) ⬝ᵥ GR *ᵥ (fun i => (y i : ℝ)) =
      ((y ⬝ᵥ G *ᵥ y : ℚ) : ℝ) := by
    intro y
    simp [hGR, dotProduct, Matrix.mulVec, Rat.cast_sum, Rat.cast_mul]
  -- (a) nonnegativity on `ℝⁿ` by density of `ℚⁿ`
  have hnn : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ GR *ᵥ x := by
    intro x
    have hd : DenseRange (Pi.map fun _ : n => (fun r : ℚ => (r : ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on x (isClosed_le continuous_const (by fun_prop)) fun y => ?_
    change 0 ≤ (fun i => (y i : ℝ)) ⬝ᵥ GR *ᵥ (fun i => (y i : ℝ))
    rw [hcast]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · exact_mod_cast (hpos y hy).le
  -- (b) `det G ≠ 0`
  have hdet : G.det ≠ 0 := by
    intro h
    obtain ⟨y, hy, hGy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have := hpos y hy
    rw [hGy, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hdetR : GR.det ≠ 0 := by
    have h := (Rat.castHom ℝ).map_det G
    simp only [RingHom.mapMatrix_apply, Rat.coe_castHom] at h
    rw [hGR, ← h]
    exact_mod_cast hdet
  have hGRsymm : GR.IsHermitian := by
    ext i k
    simp [hGR, ← hsymm.apply i k]
  have hpsd : GR.PosSemidef :=
    Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hGRsymm, fun x => by simpa using hnn x⟩
  -- (c) positivity on `ℝⁿ`
  have hR : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ GR *ᵥ x := by
    intro x hx
    refine lt_of_le_of_ne (hnn x) (Ne.symm fun h0 => hx ?_)
    have : GR *ᵥ x = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by simpa using h0)
    exact Matrix.eq_zero_of_mulVec_eq_zero hdetR this
  -- (d) the Hermitian form on `ℂⁿ`: `z̄ᵀ G z = uᵀ G u + vᵀ G v` for `z = u + i v`
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun z hz => ?_⟩
  · ext i k
    simp [← hsymm.apply i k]
  set u : n → ℝ := fun i => (z i).re
  set v : n → ℝ := fun i => (z i).im
  have hre : (star z ⬝ᵥ (G.map (fun r : ℚ => (r : ℂ))) *ᵥ z).re =
      u ⬝ᵥ GR *ᵥ u + v ⬝ᵥ GR *ᵥ v := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, re_sum, u, v, hGR,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
  have him : (star z ⬝ᵥ (G.map (fun r : ℚ => (r : ℂ))) *ᵥ z).im = 0 := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, im_sum,
      Finset.mul_sum]
    have e : ∀ i k, (star (z i) * ((G i k : ℂ) * z k)).im =
        (G i k : ℝ) * ((z i).re * (z k).im - (z i).im * (z k).re) := by
      intro i k
      simp [Complex.mul_re, Complex.mul_im]
      ring
    simp_rw [e, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← hsymm.apply k i]
    ring
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext i
    apply Complex.ext
    · simpa [u] using congrFun h.1 i
    · simpa [v] using congrFun h.2 i
  rw [Complex.lt_def]
  refine ⟨?_, by simp [him]⟩
  rw [hre, Complex.zero_re]
  rcases huv with hu | hv
  · exact add_pos_of_pos_of_nonneg (hR u hu) (hnn v)
  · exact add_pos_of_nonneg_of_pos (hnn u) (hR v hv)

/-- **`prop:rosati-EF`(ii), positivity of the complexified trace form.** Let `A` be a complex
`*`-algebra with a `ℂ`-basis `b` (in the notes, the image of a `ℚ`-basis `a_i` of `End⁰(J)`, with
`b_i^† = ` the image of `a_i^†`), `τ` a linear functional with `τ(b_i b_k^†) = G_{ik}` rational,
and `G` symmetric and positive on `ℚⁿ` (Weil/Milne positivity of the Rosati form, a hypothesis).
Then `Re τ(x x^†) > 0` for every `x ≠ 0` — the positivity axiom of a positive trace involution. -/
theorem rosati_trace_pos {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [Ring A]
    [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (b : Module.Basis n ℂ A) (τ : A →ₗ[ℂ] ℂ)
    (G : Matrix n n ℚ) (hsymm : G.IsSymm) (hpos : ∀ x : n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x)
    (hG : ∀ i k, τ (b i * star (b k)) = (G i k : ℂ)) {x : A} (hx : x ≠ 0) :
    0 < (τ (x * star x)).re := by
  set c := b.repr x
  have hc : (c : n → ℂ) ≠ 0 := by
    intro h
    apply hx
    rw [← b.linearCombination_repr x]
    simp [c] at h
    simp [h]
  have hxs : x = ∑ i, c i • b i := (b.sum_repr x).symm
  have key : τ (x * star x) = star (fun i => c i) ⬝ᵥ (G.map (fun r : ℚ => (r : ℂ))) *ᵥ
      (fun i => c i) := by
    rw [hxs, star_sum, Finset.sum_mul_sum, map_sum]
    simp only [star_smul, smul_mul_smul_comm, map_sum, map_smul, hG, smul_eq_mul, dotProduct,
      Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [← hsymm.apply k i]
    simp only [RCLike.star_def]
    ring
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 (rosati_gram_posDef G hsymm hpos)).2 hc
  rw [key]
  exact (Complex.lt_def.1 this).1

end Rosati

end WeilRH
