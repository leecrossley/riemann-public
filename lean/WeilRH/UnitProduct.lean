/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Unit

/-!
# The degree-zero suspended datum is `𝟙_q` with its product (`prop:unit`, first clause)

Source: `latex/notes.tex`, Proposition `prop:unit` and Definition `def:susp-datum` (a).

In degree zero `H⁰ = ℂ · 1` with `F = 1`. Its logarithmic suspension is `unitSpace q =
SuspSpace 1 q` (`WeilRH.KunOrbits`), with one line `ℂ 1_ρ` for each `ρ ∈ Σ_q(1) = (2πi/log q) ℤ`.
`def:susp-datum` (a) multiplies the copy of `u` in `V̂_ρ` and the copy of `v` in `V̂_{ρ'}` to the
copy of `u v` in `V̂_{ρ+ρ'}` (`q^{ρ+ρ'} = 1` is always an eigenvalue here, so the "`0` otherwise"
case does not occur).

* `UnitProduct.suspMul`: that product on `unitSpace q`.
* `UnitProduct.equiv`: the linear isomorphism `unitSpace q ≃ 𝟙_q = Periodic`, `1_{shift q n} ↦ vⁿ`.
* `UnitProduct.equiv_mul`, `equiv_unit`, `equiv_theta` (**`prop:unit`, first clause**): it is
  multiplicative, sends the unit `1_0` to `1`, and intertwines `Θ` with `Θ_{𝟙_q}`.

The remaining clauses of `prop:unit` (spectrum, simplicity, and `𝟙_q ≇ 𝟙`) are in `WeilRH.Unit`
and `WeilRH.KunOrbits`. The identification `H⁰ = ℂ · 1` with `F = 1` is the input
`thm:imp-weil-coh` and is not formalized; the theorem here starts from `(ℂ, 1)`.
-/

namespace WeilRH.UnitProduct

open WeilRH.Spectral WeilRH.Suspension WeilRH.KunFq WeilRH.KunOrbits WeilRH.Unit
open scoped DirectSum

variable {q : ℝ}

local notation "S" q => unitSpace q

/-- Every index of the suspension of `(ℂ, 1)` has `q^ρ = 1`. -/
lemma qpow_idx (ρ : Idx (1 : Module.End ℂ ℂ) q) : qpow q ρ.1 = 1 :=
  (hasEigenvalue_one_iff _).1 ρ.2

lemma qpow_add' (a b : ℂ) : qpow q (a + b) = qpow q a * qpow q b := by
  rw [qpow, qpow, qpow, mul_add, Complex.exp_add]

/-- The index `ρ + ρ'`. -/
def addIdx (ρ ρ' : Idx (1 : Module.End ℂ ℂ) q) : Idx (1 : Module.End ℂ ℂ) q :=
  ⟨ρ.1 + ρ'.1, (hasEigenvalue_one_iff _).2 (by rw [qpow_add', qpow_idx, qpow_idx, one_mul])⟩

/-- The index `0`. -/
def zeroIdx : Idx (1 : Module.End ℂ ℂ) q :=
  ⟨0, (hasEigenvalue_one_iff _).2 (by simp [qpow])⟩

/-- Each summand `V̂_ρ = V_{(1)}` is all of `ℂ`. -/
lemma summand_eq_top (ρ : Idx (1 : Module.End ℂ ℂ) q) : Summand 1 q ρ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Summand, Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  rw [qpow_idx, pow_one, one_smul, sub_self, LinearMap.zero_apply]

/-- The coordinate `V̂_ρ ≃ ℂ`. -/
noncomputable def coord (ρ : Idx (1 : Module.End ℂ ℂ) q) : Summand 1 q ρ ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofEq _ _ (summand_eq_top ρ)).trans (LinearEquiv.ofTop ⊤ rfl)

@[simp] lemma coord_apply (ρ : Idx (1 : Module.End ℂ ℂ) q) (u : Summand 1 q ρ) :
    coord ρ u = (u : ℂ) := rfl

/-- The component `V̂_ρ × V̂_{ρ'} → V̂_{ρ+ρ'}`, `(u, v) ↦ u v` (`def:susp-datum` (a)). -/
noncomputable def mulComp (ρ ρ' : Idx (1 : Module.End ℂ ℂ) q) :
    Summand 1 q ρ →ₗ[ℂ] Summand 1 q ρ' →ₗ[ℂ] (S q) :=
  ((LinearMap.mul ℂ ℂ).compl₁₂ (coord ρ).toLinearMap (coord ρ').toLinearMap).compr₂
    (DirectSum.lof ℂ _ (fun ρ => Summand 1 q ρ) (addIdx ρ ρ') ∘ₗ
      (coord (addIdx ρ ρ')).symm.toLinearMap)

/-- **The product of the degree-zero suspended datum** (`def:susp-datum` (a)). -/
noncomputable def suspMul : (S q) →ₗ[ℂ] (S q) →ₗ[ℂ] (S q) :=
  DirectSum.toModule ℂ _ _ fun ρ =>
    (DirectSum.toModule ℂ _ _ fun ρ' => (mulComp ρ ρ').flip).flip

lemma suspMul_lof (ρ ρ' : Idx (1 : Module.End ℂ ℂ) q) (u : Summand 1 q ρ)
    (v : Summand 1 q ρ') :
    suspMul (DirectSum.lof ℂ _ _ ρ u) (DirectSum.lof ℂ _ _ ρ' v) =
      DirectSum.lof ℂ _ (fun ρ => Summand 1 q ρ) (addIdx ρ ρ')
        ((coord (addIdx ρ ρ')).symm ((u : ℂ) * v)) := by
  simp [suspMul, DirectSum.toModule_lof, mulComp]

/-- The unit `1_0` of the suspended datum. -/
noncomputable def unitElt : (S q) :=
  DirectSum.lof ℂ _ (fun ρ => Summand 1 q ρ) zeroIdx ((coord zeroIdx).symm 1)

variable (hq : 1 < q)
include hq

/-- The integer `n` with `ρ = shift q n`. -/
noncomputable def idxInt (ρ : Idx (1 : Module.End ℂ ℂ) q) : ℤ :=
  ((qpow_eq_one_iff hq ρ.1).1 (qpow_idx ρ)).choose

lemma shift_idxInt (ρ : Idx (1 : Module.End ℂ ℂ) q) : shift q (idxInt hq ρ) = ρ.1 :=
  ((qpow_eq_one_iff hq ρ.1).1 (qpow_idx ρ)).choose_spec.symm

/-- `Idx 1 q ≃ ℤ`, `ρ ↦ n` with `ρ = 2πin/log q`. -/
noncomputable def idxEquiv : Idx (1 : Module.End ℂ ℂ) q ≃ ℤ where
  toFun := idxInt hq
  invFun n := ⟨shift q n, (hasEigenvalue_one_iff _).2 ((qpow_eq_one_iff hq _).2 ⟨n, rfl⟩)⟩
  left_inv ρ := Subtype.ext (shift_idxInt hq ρ)
  right_inv _ := shift_injective hq (shift_idxInt hq _)

lemma idxInt_addIdx (ρ ρ' : Idx (1 : Module.End ℂ ℂ) q) :
    idxInt hq (addIdx ρ ρ') = idxInt hq ρ + idxInt hq ρ' := by
  apply shift_injective hq
  rw [shift_add', shift_idxInt, shift_idxInt, shift_idxInt]
  rfl

lemma idxInt_zeroIdx : idxInt hq (zeroIdx (q := q)) = 0 := by
  apply shift_injective hq
  rw [shift_idxInt]
  simp [zeroIdx, shift]

/-- **The isomorphism `V̂⁰ ≃ 𝟙_q`**, `1_{2πin/log q} ↦ vⁿ`. -/
noncomputable def equiv : (S q) ≃ₗ[ℂ] Periodic :=
  ((DFinsupp.mapRange.linearEquiv fun ρ => coord ρ).trans
    (DirectSum.lequivCongrLeft ℂ (idxEquiv hq))).trans periodicEquiv.symm

omit hq in
lemma coord_lof (ρ σ : Idx (1 : Module.End ℂ ℂ) q) (u : Summand 1 q ρ) :
    coord σ ((DirectSum.lof ℂ _ (fun ρ => Summand 1 q ρ) ρ u) σ) = if σ = ρ then (u : ℂ) else 0 := by
  by_cases h : σ = ρ
  · subst h
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_same, if_pos rfl, coord_apply]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h, if_neg h, map_zero]

lemma equiv_lof (ρ : Idx (1 : Module.End ℂ ℂ) q) (u : Summand 1 q ρ) :
    equiv hq (DirectSum.lof ℂ _ _ ρ u) = AddMonoidAlgebra.single (idxInt hq ρ) (u : ℂ) := by
  apply periodicEquiv.injective
  rw [periodicEquiv_single, equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext m
  rw [LinearEquiv.trans_apply, DirectSum.lequivCongrLeft_apply,
    DFinsupp.mapRange.linearEquiv_apply, DFinsupp.mapRange_apply, coord_lof, DirectSum.of_apply]
  have hiff : (idxEquiv hq).symm m = ρ ↔ idxInt hq ρ = m :=
    ⟨fun h => by rw [← h]; exact (idxEquiv hq).apply_symm_apply m,
      fun h => by rw [← h]; exact (idxEquiv hq).symm_apply_apply ρ⟩
  by_cases h : idxInt hq ρ = m
  · rw [dif_pos h, if_pos (hiff.2 h)]
    subst h; rfl
  · rw [dif_neg h, if_neg (fun h' => h (hiff.1 h'))]

/-- **`prop:unit`, first clause: the isomorphism is multiplicative.** -/
theorem equiv_mul (x y : S q) : equiv hq (suspMul x y) = equiv hq x * equiv hq y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [map_add, hx, hx', add_mul]
  | of ρ u =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [map_add, hy, hy', mul_add]
    | of ρ' v =>
      rw [← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, suspMul_lof, equiv_lof, equiv_lof,
        equiv_lof, AddMonoidAlgebra.single_mul_single, idxInt_addIdx]
      rw [show (((coord (addIdx ρ ρ')).symm ((u : ℂ) * v) : Summand 1 q (addIdx ρ ρ')) : ℂ) =
        (u : ℂ) * v from (coord (addIdx ρ ρ')).apply_symm_apply ((u : ℂ) * v)]

/-- **`prop:unit`, first clause: the unit `1_0` goes to `1`.** -/
theorem equiv_unit : equiv hq unitElt = 1 := by
  rw [unitElt, equiv_lof, idxInt_zeroIdx,
    show (((coord (zeroIdx (q := q))).symm 1 : Summand 1 q zeroIdx) : ℂ) = 1 from
      (coord (zeroIdx (q := q))).apply_symm_apply 1]
  rfl

omit hq in
lemma logNil_one (α : ℂ) (hα : α = 1) : logNil (1 : Module.End ℂ ℂ) α = 0 := by
  have hr : restrictF (1 : Module.End ℂ ℂ) α = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rfl
  rw [logNil, hr, hα, inv_one, one_smul, sub_self]
  refine Finset.sum_eq_zero fun k hk => ?_
  have : k ≠ 0 := by simp at hk; omega
  rw [zero_pow this, smul_zero]

/-- **`prop:unit`, first clause: the isomorphism intertwines `Θ` with `Θ_{𝟙_q}`.** -/
theorem equiv_theta (x : S q) : equiv hq (unitTheta q x) = periodicTheta q (equiv hq x) := by
  have : (equiv hq).toLinearMap ∘ₗ unitTheta q = periodicTheta q ∘ₗ (equiv hq).toLinearMap := by
    refine DirectSum.linearMap_ext ℂ fun ρ => LinearMap.ext fun u => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    have hθ : unitTheta q (DirectSum.lof ℂ _ _ ρ u) =
        DirectSum.lof ℂ _ (fun ρ => Summand 1 q ρ) ρ (ρ.1 • u) := by
      rw [unitTheta, theta, diag, DirectSum.lmap_lof, thetaBlock, logNil_one _ (qpow_idx ρ)]
      simp
    rw [hθ, equiv_lof, equiv_lof, periodicTheta_single, shift_idxInt]
    simp
  exact LinearMap.congr_fun this x

end WeilRH.UnitProduct
