/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Flow

/-!
# Finite-field calibration: logarithmic suspension and (P) (Q2 Prop. 6.2, Thm 6.5(4) core)

Source: `ai/2026-09-25-finite-field-calibration/report.md`, §6.1 Definition 6.1 (logarithmic
suspension), §6.2 Proposition 6.2 ("the finite-field AW4 identity (P) is the logarithm of
`F*F = q^j`"), §6.4 Theorem 6.5(4).

## Design

Let `E` be a finite-dimensional complex inner product space (report: `V^j = H^j ⊗_ι ℂ` with a
positive form `h`, Mathlib inner product, report-convention `hForm`), `F : E → E` linear with
`h(Fu, Fv) = q^j h(u, v)`, `q > 1`. By C-WEIL (`isSemisimple_of_weil`, `norm_eq_rpow_of_weil`)
`F` is semisimple with `|α| = q^{j/2}`, so we are in the semisimple case of Definition 6.1
(`N = 0`).

Definition 6.1 builds `V̂ = ⨁_{ρ : q^ρ ∈ Spec F} V_{(q^ρ)}`, i.e. **one copy of `V` for each
`k ∈ ℤ`**, the `k`-th copy carrying `Θ = (log α + 2πik)/log q` on the `α`-eigenspace. We formalize
**one copy at a time**: for each `k : ℤ`, `suspension F q k : Module.End ℂ E` acts on the
`α`-eigenspace by `suspEigen q k α = (log α + 2πik)/log q` (principal `Complex.log`; the set over
all `k` is branch-free). It is constructed as a polynomial in `F` (Lagrange interpolation on the
roots of the minimal polynomial of `F`). The full suspension is the algebraic direct sum over
`k ∈ ℤ` of these copies with the orthogonal-sum form; since (P) and the flow identity are checked
copy by copy, the statements below are the whole content of Proposition 6.2 in the semisimple case.
The regularized-determinant part (Thm 6.3), the duality/star on the suspension, and the
nonsemisimple case (`N ≠ 0`, where positivity fails, §7) are **not** formalized.

## Main results

* `exp_suspEigen`: `exp(log q · ρ_k(α)) = α` (so `q^Θ = F` eigenvalue-wise, every `k`).
* `suspension_apply_of_apply_eq_smul`: `Θ_k v = ρ_k(α) v` for `F v = α v`.
* `suspension_P` (**Q2 Prop. 6.2(a)**): the Weil identity `h(Fu, Fv) = q^j h(u, v)` implies (P)
  with weight `j` for `Θ_k`, for every `k`.
* `flow_suspension`: `exp(log q · Θ_k) = F` (as continuous linear maps).
* `weil_of_P_of_flow` (**Q2 Prop. 6.2(b)**): conversely, (P) with weight `j` for any `Θ` with
  `exp(log q · Θ) = F` implies the Weil identity.
* `suspension_P_iff_weil`: for the suspension, (P) ⇔ Weil identity (under `q > 1`).
-/

open scoped InnerProductSpace ComplexConjugate
open Complex Polynomial

namespace WeilRH

/-- The suspended eigenvalue `ρ_k(α) = (log α + 2πik)/log q` (Q2 Definition 6.1). -/
noncomputable def suspEigen (q : ℝ) (k : ℤ) (α : ℂ) : ℂ :=
  (Complex.log α + 2 * Real.pi * I * k) / (Real.log q : ℂ)

lemma log_ne_zero_of_one_lt {q : ℝ} (hq : 1 < q) : (Real.log q : ℂ) ≠ 0 := by
  exact_mod_cast (Real.log_pos hq).ne'

/-- `q^{ρ_k(α)} = α`: `exp(log q · ρ_k(α)) = α` for every `k`. -/
theorem exp_suspEigen {q : ℝ} (hq : 1 < q) (k : ℤ) {α : ℂ} (hα : α ≠ 0) :
    Complex.exp ((Real.log q : ℂ) * suspEigen q k α) = α := by
  rw [suspEigen, mul_div_cancel₀ _ (log_ne_zero_of_one_lt hq), Complex.exp_add,
    Complex.exp_log hα, show 2 * Real.pi * I * (k : ℂ) = k * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `Re ρ_k(α) = log |α| / log q`. -/
theorem re_suspEigen (q : ℝ) (k : ℤ) (α : ℂ) :
    (suspEigen q k α).re = Real.log ‖α‖ / Real.log q := by
  rw [suspEigen, Complex.div_ofReal_re]
  simp [Complex.log_re]

/-- If `|α| = q^{j/2}` then `Re ρ_k(α) = j/2`. -/
theorem re_suspEigen_of_norm {q j : ℝ} (hq : 1 < q) (k : ℤ) {α : ℂ} (hα : ‖α‖ = q ^ (j / 2)) :
    (suspEigen q k α).re = j / 2 := by
  rw [re_suspEigen, hα, Real.log_rpow (by linarith), mul_div_cancel_right₀ _ (Real.log_pos hq).ne']

section Suspension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The interpolating polynomial `p` with `p(α) = ρ_k(α)` on the roots of the minimal polynomial
of `F` (= the eigenvalues of `F`). -/
noncomputable def suspPoly (F : Module.End ℂ E) (q : ℝ) (k : ℤ) : ℂ[X] :=
  Lagrange.interpolate (minpoly ℂ F).roots.toFinset id (suspEigen q k)

/-- The `k`-th copy of the logarithmic suspension `Θ_k = p(F)` (Q2 Definition 6.1, semisimple
case, one `k`). -/
noncomputable def suspension (F : Module.End ℂ E) (q : ℝ) (k : ℤ) : Module.End ℂ E :=
  aeval F (suspPoly F q k)

/-- `Θ_k` acts on the `α`-eigenspace of `F` by `ρ_k(α)`. -/
theorem suspension_apply_of_apply_eq_smul (F : Module.End ℂ E) (q : ℝ) (k : ℤ) {α : ℂ} {v : E}
    (hv : F v = α • v) : suspension F q k v = suspEigen q k α • v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hα : F.HasEigenvalue α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hroot : α ∈ (minpoly ℂ F).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (minpoly.ne_zero (Algebra.IsIntegral.isIntegral F))]
    exact Module.End.isRoot_of_hasEigenvalue hα
  rw [suspension, Module.End.aeval_apply_of_mem_apply_eq_smul hv, suspPoly]
  congr 1
  exact Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hroot

variable (F : Module.End ℂ E) {q j : ℝ} (hq : 1 < q)
  (hW : ∀ u v, hForm (F u) (F v) = ((q ^ j : ℝ) : ℂ) * hForm u v)
include hq hW

/-- Under the Weil identity, the eigenspaces of `F` span `E`. -/
lemma iSup_eigenspace_eq_top : ⨆ α, F.eigenspace α = ⊤ := by
  have hq0 : 0 < q := by linarith
  rw [← Module.End.iSup_maxGenEigenspace_eq_top F]
  congr 1
  funext α
  exact (maxGenEigenspace_eq_eigenspace_of_mul F (q ^ j) (Real.rpow_pos_of_pos hq0 j) hW α).symm

/-- (P) for eigenvectors of `F`. -/
lemma suspension_P_eigen (k : ℤ) {α β : ℂ} {u v : E} (hu : F u = α • u) (hv : F v = β • v) :
    hForm (suspension F q k u) v + hForm u (suspension F q k v) = (j : ℂ) * hForm u v := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [hForm]
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [hForm]
  have hαe : F.HasEigenvalue α :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hu, hu0⟩
  have hβe : F.HasEigenvalue β :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hαn := norm_eq_rpow_of_weil F q j hq0 hW hαe
  have hβn := norm_eq_rpow_of_weil F q j hq0 hW hβe
  rw [suspension_apply_of_apply_eq_smul F q k hu, suspension_apply_of_apply_eq_smul F q k hv,
    hForm_smul_left, hForm_smul_right]
  by_cases hαβ : α = β
  · subst hαβ
    have hre := re_suspEigen_of_norm hq k hαn
    have : suspEigen q k α + conj (suspEigen q k α) = (j : ℂ) := by
      rw [Complex.add_conj, hre]; push_cast; try ring
    linear_combination (hForm u v) * this
  · -- distinct eigenspaces are `h`-orthogonal
    have h0 : hForm u v = 0 := by
      have key := hW u v
      rw [hu, hv, hForm_smul_left, hForm_smul_right] at key
      by_contra hne
      have hprod : α * conj β = ((q ^ j : ℝ) : ℂ) := by
        have h2 : α * conj β * hForm u v = ((q ^ j : ℝ) : ℂ) * hForm u v := by
          linear_combination key
        exact mul_right_cancel₀ hne h2
      have hββ : β * conj β = ((q ^ j : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hβn, ← Real.rpow_natCast,
          ← Real.rpow_mul hq0.le]
        norm_num
      have hβ0 : conj β ≠ 0 := by
        have : β ≠ 0 := by
          intro h
          rw [h, norm_zero] at hβn
          exact (Real.rpow_pos_of_pos hq0 (j / 2)).ne' hβn.symm
        simpa using this
      exact hαβ (mul_right_cancel₀ hβ0 (hprod.trans hββ.symm))
    rw [h0]
    ring

/-- **Q2 Proposition 6.2(a) (semisimple case, one copy `k`).** If `h(Fu, Fv) = q^j h(u, v)` with
`h` positive definite and `q > 1`, the suspended generator `Θ_k` satisfies (P) with weight `j`:
`h(Θ_k u, v) + h(u, Θ_k v) = j h(u, v)`. -/
theorem suspension_P (k : ℤ) (u v : E) :
    hForm (suspension F q k u) v + hForm u (suspension F q k v) = (j : ℂ) * hForm u v := by
  have htop := iSup_eigenspace_eq_top F hq hW
  have hmem : ∀ x : E, x ∈ ⨆ α, F.eigenspace α := fun x => htop ▸ Submodule.mem_top
  -- first `v` in an eigenspace, `u` arbitrary
  have step : ∀ β, ∀ v ∈ F.eigenspace β, ∀ u : E,
      hForm (suspension F q k u) v + hForm u (suspension F q k v) = (j : ℂ) * hForm u v := by
    intro β v hv u
    refine Submodule.iSup_induction (motive := fun u =>
      hForm (suspension F q k u) v + hForm u (suspension F q k v) = (j : ℂ) * hForm u v)
      _ (hmem u) ?_ ?_ ?_
    · intro α x hx
      exact suspension_P_eigen F hq hW k (Module.End.mem_eigenspace_iff.1 hx)
        (Module.End.mem_eigenspace_iff.1 hv)
    · simp [hForm]
    · intro x y hx hy
      simp only [hForm, map_add, inner_add_right] at hx hy ⊢
      linear_combination hx + hy
  refine Submodule.iSup_induction (motive := fun v =>
      hForm (suspension F q k u) v + hForm u (suspension F q k v) = (j : ℂ) * hForm u v)
    _ (hmem v) ?_ ?_ ?_
  · intro β x hx
    exact step β x hx u
  · simp [hForm]
  · intro x y hx hy
    simp only [hForm, map_add, inner_add_left] at hx hy ⊢
    linear_combination hx + hy

/-- `Θ_k` is semisimple and all its eigenvalues have real part `j/2` (C-PUR for the suspension). -/
theorem suspension_isSemisimple (k : ℤ) : (suspension F q k).IsSemisimple :=
  isSemisimple_of_additive _ j (suspension_P F hq hW k)

end Suspension

/-! ### The flow of an eigenvector and `q^Θ = F` -/

section FlowEigen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On an eigenvector `Θ v = ρ v`, the flow is `φ^t v = e^{tρ} v`. -/
theorem flow_apply_of_apply_eq_smul (Θ : E →L[ℂ] E) {ρ : ℂ} {v : E} (hv : Θ v = ρ • v) (t : ℝ) :
    flow Θ t v = Complex.exp (t * ρ) • v := by
  have hcomm : ∀ s : ℝ, Θ (flow Θ s v) = ρ • flow Θ s v := by
    intro s
    have hc : Commute Θ (flow Θ s) := ((Commute.refl Θ).smul_right (s : ℝ)).exp_right
    have := congrArg (fun f : E →L[ℂ] E => f v) hc.eq
    simp only [mul_apply_eq_comp] at this
    rw [this, hv, map_smul]
  set G : ℝ → E := fun s => Complex.exp (-((s : ℂ) * ρ)) • flow Θ s v with hG
  have hGd : ∀ s, HasDerivAt G 0 s := by
    intro s
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * ρ)))
        (Complex.exp (-((s : ℂ) * ρ)) * (-ρ)) s := by
      have := (((hasDerivAt_id (s : ℝ)).ofReal_comp.mul_const ρ).neg).cexp
      simpa using this
    have := he.smul (hasDerivAt_flow_apply Θ v s)
    convert this using 1
    rw [hcomm s, smul_smul, ← add_smul]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hGd s).differentiableAt)
    (fun s => (hGd s).deriv) t 0
  simp only [hG, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_smul,
    flow_zero, one_apply_eq_self] at hconst
  calc flow Θ t v = Complex.exp (t * ρ) • (Complex.exp (-((t : ℂ) * ρ)) • flow Θ t v) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp (t * ρ) • v := by rw [hconst]

end FlowEigen

section Converse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **`q^{Θ_k} = F`.** Under the Weil identity (`q > 1`), `exp(log q · Θ_k) = F`. -/
theorem flow_suspension (F : Module.End ℂ E) {q j : ℝ} (hq : 1 < q)
    (hW : ∀ u v, hForm (F u) (F v) = ((q ^ j : ℝ) : ℂ) * hForm u v) (k : ℤ) :
    flow (LinearMap.toContinuousLinearMap (suspension F q k)) (Real.log q) =
      LinearMap.toContinuousLinearMap F := by
  have htop := iSup_eigenspace_eq_top F hq hW
  ext x
  have hx : x ∈ ⨆ α, F.eigenspace α := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun x =>
    flow (LinearMap.toContinuousLinearMap (suspension F q k)) (Real.log q) x =
      LinearMap.toContinuousLinearMap F x) _ hx ?_ ?_ ?_
  · intro α v hv
    have hFv := Module.End.mem_eigenspace_iff.1 hv
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hα0 : α ≠ 0 := by
      rintro rfl
      have hq0 : 0 < q := by linarith
      have := norm_eq_rpow_of_weil F q j hq0 hW
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
      rw [norm_zero] at this
      exact (Real.rpow_pos_of_pos hq0 _).ne' this.symm
    rw [flow_apply_of_apply_eq_smul _ (suspension_apply_of_apply_eq_smul F q k hFv),
      exp_suspEigen hq k hα0]
    simp [hFv]
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- **Q2 Proposition 6.2(b).** If `Θ` satisfies (P) with weight `j` and `exp(log q · Θ) = F`
(`q > 0`), then `h(Fu, Fv) = q^j h(u, v)`. -/
theorem weil_of_P_of_flow (F Θ : Module.End ℂ E) {q j : ℝ} (hq : 0 < q)
    (hP : ∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v)
    (hexp : flow (LinearMap.toContinuousLinearMap Θ) (Real.log q) =
      LinearMap.toContinuousLinearMap F) (u v : E) :
    hForm (F u) (F v) = ((q ^ j : ℝ) : ℂ) * hForm u v := by
  have := (P_iff_flow_of_finiteDimensional Θ j).1 hP (Real.log q) u v
  rw [hexp] at this
  rw [Real.rpow_def_of_pos hq, mul_comm (Real.log q)]
  simpa using this

/-- **Q2 Proposition 6.2 (both directions, semisimple case).** For `q > 1` and any `k : ℤ`: the
Weil identity for `F` implies (P) for `Θ_k` and `q^{Θ_k} = F`; conversely (P) for `Θ_k` together
with `q^{Θ_k} = F` gives back the Weil identity. -/
theorem suspension_P_iff_weil (F : Module.End ℂ E) {q j : ℝ} (hq : 1 < q) (k : ℤ) :
    (∀ u v, hForm (F u) (F v) = ((q ^ j : ℝ) : ℂ) * hForm u v) ↔
      ((∀ u v, hForm (suspension F q k u) v + hForm u (suspension F q k v) =
          (j : ℂ) * hForm u v) ∧
        flow (LinearMap.toContinuousLinearMap (suspension F q k)) (Real.log q) =
          LinearMap.toContinuousLinearMap F) :=
  ⟨fun hW => ⟨suspension_P F hq hW k, flow_suspension F hq hW k⟩,
    fun ⟨hP, hexp⟩ => weil_of_P_of_flow F _ (by linarith) hP hexp⟩

end Converse

end WeilRH
