/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.RH

/-!
# The flow form of (P)

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §4.3 AW4, identity (P):

  `h_j(φ^t u, φ^t v) = e^{j t} h_j(u, v)`,   `h_j(Θ u, v) + h_j(u, Θ v) = j h_j(u, v)`,

with `φ^t = e^{tΘ}` on each finite-dimensional block (AW1).

We prove the two forms are equivalent for any *bounded* generator on a complete complex inner
product space (`P_iff_flow`), with `φ^t = NormedSpace.exp (t • Θ)` in the Banach algebra
`E →L[ℂ] E`. The finite-dimensional statement for `Θ : Module.End ℂ E`
(`P_iff_flow_of_finiteDimensional`) and the block statement for `ArithmeticWeilCohomologyQ`
(`ArithmeticWeilCohomologyQ.flow_restrict`; the structure is the degree-one slice of a
polarized Deninger structure, notes `def:deninger-structure`, `def:polarizable`) follow. The
proof is by differentiation:
`F(t) = h(φ^t u, φ^t v)` satisfies `F' = j F` under (P), so `e^{-jt} F(t)` is constant; conversely
differentiate at `t = 0`.
-/

open scoped InnerProductSpace

namespace WeilRH

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The flow `φ^t = exp(t Θ)` of a bounded generator. -/
noncomputable def flow (Θ : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := NormedSpace.exp (t • Θ)

@[simp] lemma flow_zero (Θ : E →L[ℂ] E) : flow Θ 0 = 1 := by simp [flow]

lemma hasDerivAt_flow_apply (Θ : E →L[ℂ] E) (u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow Θ s u) (Θ (flow Θ t u)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Θ t
  have := ((ContinuousLinearMap.apply ℂ E u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  exact this

lemma hasDerivAt_hForm_flow (Θ : E →L[ℂ] E) (u v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hForm (flow Θ s u) (flow Θ s v))
      (hForm (Θ (flow Θ t u)) (flow Θ t v) + hForm (flow Θ t u) (Θ (flow Θ t v))) t := by
  have := (hasDerivAt_flow_apply Θ v t).inner ℂ (hasDerivAt_flow_apply Θ u t)
  simp only [hForm]
  convert this using 1

/-- **Flow form of (P)** for a bounded generator: (P) holds iff `h(φ^t u, φ^t v) = e^{jt} h(u,v)`
for all real `t`. -/
theorem P_iff_flow (Θ : E →L[ℂ] E) (j : ℝ) :
    (∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) ↔
      ∀ (t : ℝ) (u v : E),
        hForm (flow Θ t u) (flow Θ t v) = (Real.exp (j * t) : ℂ) * hForm u v := by
  constructor
  · intro hP t u v
    set F : ℝ → ℂ := fun s => hForm (flow Θ s u) (flow Θ s v) with hF
    have hFd : ∀ s, HasDerivAt F ((j : ℂ) * F s) s := fun s => by
      have := hasDerivAt_hForm_flow Θ u v s
      rwa [hP] at this
    set G : ℝ → ℂ := fun s => (Real.exp (-(j * s)) : ℂ) * F s with hG
    have hEd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (Real.exp (-(j * s)) : ℂ))
        ((Real.exp (-(j * s)) * (-j) : ℝ) : ℂ) s := fun s => by
      have := ((((hasDerivAt_id s).const_mul j).neg).exp).ofReal_comp
      simpa using this
    have hGd : ∀ s, HasDerivAt G 0 s := fun s => by
      have := (hEd s).mul (hFd s)
      convert this using 1
      push_cast
      ring
    have hconst := is_const_of_deriv_eq_zero (fun s => (hGd s).differentiableAt)
      (fun s => (hGd s).deriv) t 0
    simp only [hG, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
      hF, flow_zero, one_apply_eq_self] at hconst
    rw [← hconst, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  · intro hflow u v
    have h1 := hasDerivAt_hForm_flow Θ u v 0
    have h2 : HasDerivAt (fun s : ℝ => hForm (flow Θ s u) (flow Θ s v))
        ((Real.exp (j * 0) * j : ℝ) * hForm u v) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).const_mul j).exp).ofReal_comp).mul_const (hForm u v)
      simp only [funext fun t => hflow t u v]
      simpa using this
    have := h1.unique h2
    simp only [flow_zero, one_apply_eq_self, mul_zero, Real.exp_zero, one_mul] at this
    rw [this]

/-- **Flow form of (P), finite dimension**, for `Θ : Module.End ℂ E` with
`φ^t = exp(t Θ)` computed in `E →L[ℂ] E`. -/
theorem P_iff_flow_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : Module.End ℂ E) (j : ℝ) :
    (∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) ↔
      ∀ (t : ℝ) (u v : E),
        hForm (flow (LinearMap.toContinuousLinearMap Θ) t u)
            (flow (LinearMap.toContinuousLinearMap Θ) t v) =
          (Real.exp (j * t) : ℂ) * hForm u v :=
  P_iff_flow (LinearMap.toContinuousLinearMap Θ) j

/-- On every finite-dimensional `Θ₁`-stable block of an `ArithmeticWeilCohomologyQ`, the flow
`φ^t = exp(tΘ₁)` scales `h₁` by `e^t` (AW4's (P) in flow form, `j = 1`). -/
theorem ArithmeticWeilCohomologyQ.flow_restrict (H : ArithmeticWeilCohomologyQ)
    {W : Submodule ℂ H.V} [FiniteDimensional ℂ W] (hW : W ∈ Module.End.invtSubmodule H.Θ)
    (t : ℝ) (u v : W) :
    hForm (flow (LinearMap.toContinuousLinearMap
          (H.Θ.restrict (p := W) (q := W) (fun _ hx => hW hx))) t u)
        (flow (LinearMap.toContinuousLinearMap
          (H.Θ.restrict (p := W) (q := W) (fun _ hx => hW hx))) t v) =
      (Real.exp t : ℂ) * hForm u v := by
  have := (P_iff_flow_of_finiteDimensional
    (H.Θ.restrict (p := W) (q := W) (fun _ hx => hW hx)) 1).1 (fun u v => by
      have := H.P u v
      simpa [hForm, Submodule.coe_inner] using this) t u v
  simpa using this

end WeilRH
