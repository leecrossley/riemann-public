/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.RH

/-!
# The converse: bare spectral existence is a reformulation of RH (claim C-CONV)

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §5 ("reformulation warning").

`WeilRH.ArithmeticWeilCohomologyQ.riemannHypothesis` shows that the degree-one data recorded in
`ArithmeticWeilCohomologyQ` (the degree-one slice of a polarized Deninger structure satisfying
AW2, notes `thm:rh`, `def:deninger-structure`, `def:polarizable`; the name is historical) imply
`RiemannHypothesis`. This file proves the converse: assuming
`RiemannHypothesis`, we build a (non-arithmetic) *diagonal model* `diagonalModel`, so that

  `Nonempty ArithmeticWeilCohomologyQ ↔ RiemannHypothesis`.

This is the formal version of the report's warning in §5: the bare existence of a spectral
realization (a positive definite form, a flow generator satisfying (P), and spectrum equal to the
nontrivial zeros) is merely a reformulation of RH, and carries no evidence for it. All the
mathematical content of a genuine Deninger cohomology theory (`def:deninger-theory`) lies in the
parts that
`ArithmeticWeilCohomologyQ` does not encode.

## The construction

Let `NontrivialZeros` be the *set* of nontrivial zeros of `ζ`. Inside the Hilbert space
`ℓ²(NontrivialZeros)` take the subspace `V` of finitely supported vectors, and let `Θ` act
diagonally, `(Θ f)(ρ) = ρ · f(ρ)`. Under RH, `ρ + conj ρ = 2 Re ρ = 1`, which is (P); the
eigenvalues of `Θ` are exactly the nontrivial zeros; and every vector lies in the
finite-dimensional `Θ`-stable subspace of vectors supported in its own support.

## Caveats

* Multiplicities are dropped: zeros are indexed as a set, and each has a one-dimensional
  eigenspace. So this model does **not** satisfy AW2's order condition
  `m₁(ρ) = ord_ρ ξ` (which `ArithmeticWeilCohomologyQ` does not encode).
* The model is not arithmetic and not functorial: it is built from the zeros themselves.
-/

open scoped InnerProductSpace ComplexConjugate

namespace WeilRH

/-- The index set of the diagonal model: the nontrivial zeros of `ζ`, as a set (multiplicities
dropped). -/
def NontrivialZeros : Type := {ρ : ℂ // IsNontrivialZetaZero ρ}

noncomputable section

namespace DiagonalModel

noncomputable instance : DecidableEq NontrivialZeros := Classical.decEq _

/-- The ambient Hilbert space `ℓ²(NontrivialZeros)`. -/
abbrev E : Type := lp (fun _ : NontrivialZeros => ℂ) 2

/-- The finitely supported vectors of `ℓ²(NontrivialZeros)`. -/
def finSupp : Submodule ℂ E where
  carrier := {f | Set.Finite {i | f i ≠ 0}}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    refine (hf.union hg).subset fun i hi => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h hi
    exact hi (by simp [h.1, h.2])
  smul_mem' c f hf := by
    refine hf.subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi ⊢
    intro h
    exact hi (by simp [h])

/-- The spectral core of the diagonal model. -/
abbrev V : Type := ↥finSupp

lemma finite_support (f : V) : Set.Finite {i | (f : E) i ≠ 0} := f.2

/-- The diagonal vector `ρ ↦ ρ · f(ρ)`, as an element of `ℓ²`. -/
def mulVec (f : V) : E :=
  ⟨fun i => (i.1 : ℂ) * (f : E) i,
    (memℓp_zero ((finite_support f).subset fun i hi => by
      simp only [Set.mem_ofPred_eq] at hi ⊢
      intro h
      exact hi (by simp [h]))).of_exponent_ge (by simp)⟩

@[simp] lemma mulVec_apply (f : V) (i : NontrivialZeros) : mulVec f i = (i.1 : ℂ) * (f : E) i :=
  rfl

lemma mulVec_mem (f : V) : mulVec f ∈ finSupp :=
  (finite_support f).subset fun i hi => by
    simp only [Set.mem_ofPred_eq, mulVec_apply] at hi ⊢
    intro h
    exact hi (by simp [h])

/-- The flow generator: multiplication by `ρ` in the `ρ`-th coordinate. -/
def Θ : Module.End ℂ V where
  toFun f := ⟨mulVec f, mulVec_mem f⟩
  map_add' f g := by
    ext i
    simp [mul_add]
  map_smul' c f := by
    ext i
    simp only [mulVec_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] lemma Θ_apply (f : V) (i : NontrivialZeros) :
    ((Θ f : V) : E) i = (i.1 : ℂ) * (f : E) i := rfl

lemma re_eq_half (hRH : RiemannHypothesis) (i : NontrivialZeros) : (i.1 : ℂ).re = 1 / 2 :=
  hRH i.1 i.2.1 i.2.2.1 i.2.2.2

lemma add_conj_eq_one (hRH : RiemannHypothesis) (i : NontrivialZeros) :
    (i.1 : ℂ) + conj (i.1 : ℂ) = 1 := by
  rw [Complex.add_conj, re_eq_half hRH i]
  norm_num

/-- Identity (P) for the diagonal model, under RH. -/
lemma P (hRH : RiemannHypothesis) (u v : V) : hForm (Θ u) v + hForm u (Θ v) = hForm u v := by
  simp only [hForm_def, Submodule.coe_inner, lp.inner_eq_tsum]
  rw [← (lp.summable_inner _ _).tsum_add (lp.summable_inner _ _)]
  congr 1
  funext i
  simp only [Θ_apply, RCLike.inner_apply, map_mul]
  linear_combination ((u : E) i * conj ((v : E) i)) * add_conj_eq_one hRH i

/-- The basis vector at `i`, as an element of `V`. -/
def basisVec (i : NontrivialZeros) : V :=
  ⟨lp.single 2 i 1, (Set.finite_singleton i).subset fun j hj => by
    by_contra h
    exact hj (lp.single_apply_ne 2 i 1 h)⟩

lemma basisVec_ne_zero (i : NontrivialZeros) : basisVec i ≠ 0 := by
  intro h
  have := congrArg (fun f : V => (f : E) i) h
  simp [basisVec] at this

lemma Θ_basisVec (i : NontrivialZeros) : Θ (basisVec i) = (i.1 : ℂ) • basisVec i := by
  ext j
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, Pi.single_eq_of_ne h]

lemma hasEigenvalue (i : NontrivialZeros) : Module.End.HasEigenvalue Θ (i.1 : ℂ) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (Θ_basisVec i), basisVec_ne_zero i⟩

lemma isNontrivialZetaZero_of_hasEigenvalue {μ : ℂ} (h : Module.End.HasEigenvalue Θ μ) :
    IsNontrivialZetaZero μ := by
  obtain ⟨f, hf⟩ := h.exists_hasEigenvector
  have hΘ := Module.End.mem_eigenspace_iff.1 hf.1
  obtain ⟨i, hi⟩ : ∃ i, (f : E) i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hf.2 (by ext i; simp [h' i])
  have := congrArg (fun g : V => (g : E) i) hΘ
  simp only [Θ_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at this
  have hμ : μ = i.1 := (mul_right_cancel₀ hi this).symm
  exact hμ ▸ i.2

/-- The `Θ`-stable subspace of vectors supported in the support of `f`. -/
def supportedIn (f : V) : Submodule ℂ V where
  carrier := {g | ∀ i, (f : E) i = 0 → (g : E) i = 0}
  zero_mem' _ _ := rfl
  add_mem' hg hh i hi := by simp [hg i hi, hh i hi]
  smul_mem' c g hg i hi := by simp [hg i hi]

lemma finiteDimensional_supportedIn (f : V) : FiniteDimensional ℂ (supportedIn f) := by
  let s := {i | (f : E) i ≠ 0}
  let L : supportedIn f →ₗ[ℂ] (s → ℂ) :=
    { toFun g i := ((g : V) : E) i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Finite s := (finite_support f).to_subtype
  refine Module.Finite.of_injective L fun g h hgh => ?_
  ext i
  by_cases hi : (f : E) i = 0
  · rw [g.2 i hi, h.2 i hi]
  · exact congrFun hgh ⟨i, hi⟩

lemma locallyFinite (f : V) : ∃ W : Submodule ℂ V,
    f ∈ W ∧ FiniteDimensional ℂ W ∧ W ∈ Module.End.invtSubmodule Θ := by
  refine ⟨supportedIn f, fun i hi => hi, finiteDimensional_supportedIn f, ?_⟩
  rw [Module.End.mem_invtSubmodule]
  intro g hg i hi
  simp [hg i hi]

end DiagonalModel

end

open DiagonalModel in
/-- **The diagonal model (C-CONV).** Under RH, a (non-arithmetic) `ArithmeticWeilCohomologyQ`
(degree-one slice of a Deninger structure, notes `def:deninger-structure`):
finitely supported vectors in `ℓ²(NontrivialZeros)` with `Θ` acting diagonally by the zeros.
Multiplicities are dropped (each eigenspace is a line), so this model does not implement AW2's
order condition `m₁(ρ) = ord_ρ ξ`. -/
noncomputable def diagonalModel (hRH : RiemannHypothesis) : ArithmeticWeilCohomologyQ where
  V := DiagonalModel.V
  Θ := DiagonalModel.Θ
  locallyFinite := DiagonalModel.locallyFinite
  P := DiagonalModel.P hRH
  zero_isEigenvalue ρ hρ := hasEigenvalue ⟨ρ, hρ⟩
  isEigenvalue_zero _ h := isNontrivialZetaZero_of_hasEigenvalue h

/-- **C-CONV.** The existence of an `ArithmeticWeilCohomologyQ` is equivalent to RH: bare
spectral existence is a reformulation of RH (report §5). -/
theorem nonempty_arithmeticWeilCohomologyQ_iff :
    Nonempty ArithmeticWeilCohomologyQ ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_nonempty, fun hRH => ⟨diagonalModel hRH⟩⟩

end WeilRH
