/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Completed
import WeilRH.Converse

/-!
# Multiplicity-faithful AW2 and its converse

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §4.3 (AW2: "local zero order
exactly `m_j(ρ) = dim V^j_{Θ∼ρ}`"), §5 (only the divisor of `D₁` is used: `D₁` and `ξ` have the
same zeros with multiplicity, which a nonzero constant does not change; "AW2 identifies its zeros
with the entire degree-one spectral divisor, *with multiplicity*"), and the converse remark at
the end of §5 ("a basis for every zero counted with order").

`ArithmeticWeilCohomologyQMult` is the degree-one slice of a polarized Deninger structure on
`X̄_ℚ` satisfying AW2 with multiplicities (notes `prop:rh-positive-zero`; `def:deninger-structure`,
`def:polarizable`); the name is historical. It replaces the set-level spectral axioms of
`ArithmeticWeilCohomologyQ` by the order condition

  `finrank ℂ (Θ.eigenspace ρ) = analyticOrderNatAt ξ ρ`   for every `ρ : ℂ`,

with every eigenspace finite-dimensional, where `ξ = WeilRH.completedXi` is the entire completed
zeta function. By (P), eigenspaces equal generalized eigenspaces
(`maxGenEigenspace_eq_eigenspace`), so this is AW2's `dim V¹_{Θ∼ρ} = ord_ρ ξ`.

Main results:
* `ArithmeticWeilCohomologyQMult.riemannHypothesis`;
* `ArithmeticWeilCohomologyQMult.toArithmeticWeilCohomologyQ` (forgets multiplicities);
* `multDiagonalModel`: under RH, a diagonal model on finitely supported vectors of
  `ℓ²(Σ ρ, Fin (ord_ρ ξ))`;
* `nonempty_arithmeticWeilCohomologyQMult_iff : Nonempty _ ↔ RiemannHypothesis`.

The regularized determinants `det_∞` and (AW-det) are still **not** encoded: the structure takes
the *divisor* of `ξ` (now with multiplicities) as the spectral axiom. The exact zeta-regularized
value is `D₁ = ∏^reg (s - ρ)/2π = 2^{-1/2} ξ/2π²` (Deninger 1998, p. 168; cited in the notes as
`thm:imp-deninger-product`). Identity (1) of the Sept-19 record, `D₁ = ξ/2π²`, holds only up to
this nonzero constant and is superseded by that record's erratum (ruling R-1).
-/

open scoped InnerProductSpace ComplexConjugate

namespace WeilRH

/-! ## (P) forces generalized eigenspaces to be eigenspaces (any dimension) -/

section NoJordan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Under (P) with weight `j`, `Θ - ρ` is skew for `hForm` whenever `ρ.re = j / 2`. -/
lemma skew_sub_of_P (Θ : Module.End ℂ E) (j : ℝ)
    (hP : ∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) {ρ : ℂ}
    (hρ : ρ.re = j / 2) (u v : E) :
    hForm ((Θ - ρ • 1) u) v + hForm u ((Θ - ρ • 1) v) = 0 := by
  have hc : ρ + conj ρ = j := by
    rw [Complex.add_conj, hρ]; push_cast; ring
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hForm, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right]
  have := hP u v
  simp only [hForm] at this
  linear_combination this - ⟪v, u⟫_ℂ * hc

/-- Under (P) (any weight, any dimension), `(Θ - ρ)^k v = 0` implies `(Θ - ρ) v = 0`:
there are no Jordan chains. -/
lemma sub_apply_eq_zero_of_pow_of_P (Θ : Module.End ℂ E) (j : ℝ)
    (hP : ∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) (ρ : ℂ) :
    ∀ (k : ℕ) (v : E), ((Θ - ρ • 1) ^ k) v = 0 → (Θ - ρ • 1) v = 0 := by
  intro k
  induction k with
  | zero => intro v hv; simp only [pow_zero, Module.End.one_apply] at hv; simp [hv]
  | succ k ih =>
    intro v hv
    set A := Θ - ρ • 1 with hA
    rw [pow_succ, Module.End.mul_apply] at hv
    have hw : A (A v) = 0 := ih (A v) hv
    by_contra h0
    have hev : Θ.HasEigenvalue ρ := Module.End.hasEigenvalue_of_hasEigenvector
      ⟨by show A v ∈ Θ.eigenspace ρ
          rw [Module.End.eigenspace_def, LinearMap.mem_ker]; exact hw, h0⟩
    have hρ := re_eq_half_of_hasEigenvalue Θ j hP hev
    have hs := skew_sub_of_P Θ j hP hρ (A v) v
    rw [← hA, hw, show hForm (0 : E) v = 0 by simp [hForm], zero_add] at hs
    have hpos := hForm_self_re_pos h0
    rw [hs] at hpos
    simp at hpos

/-- Under (P), the maximal generalized eigenspace is the eigenspace (any dimension). -/
theorem maxGenEigenspace_eq_eigenspace_of_P (Θ : Module.End ℂ E) (j : ℝ)
    (hP : ∀ u v, hForm (Θ u) v + hForm u (Θ v) = (j : ℂ) * hForm u v) (ρ : ℂ) :
    Θ.maxGenEigenspace ρ = Θ.eigenspace ρ := by
  refine le_antisymm ?_ (Module.End.eigenspace_le_maxGenEigenspace)
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  rw [Module.End.eigenspace_def, LinearMap.mem_ker]
  exact sub_apply_eq_zero_of_pow_of_P Θ j hP ρ k v hk

end NoJordan

/-! ## The structure -/

/-- The degree-one slice of a polarized Deninger structure on `X̄_ℚ` (notes
`prop:rh-positive-zero`; `def:deninger-structure`, `def:polarizable`), with AW2 encoded **with
multiplicities**: the dimension of each `Θ₁`-eigenspace is the zero order of `ξ`. The name is
historical. -/
structure ArithmeticWeilCohomologyQMult where
  /-- The degree-one spectral core `V¹(X̄_ℚ)`. -/
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  /-- The positive definite Hermitian form `h₁` of AW4, as an inner product. -/
  [instInnerProductSpace : InnerProductSpace ℂ V]
  /-- The flow generator `Θ₁` (AW1). -/
  Θ : Module.End ℂ V
  /-- AW1: every vector lies in a finite-dimensional `Θ₁`-invariant subspace. -/
  locallyFinite : ∀ v : V, ∃ W : Submodule ℂ V,
    v ∈ W ∧ FiniteDimensional ℂ W ∧ W ∈ Module.End.invtSubmodule Θ
  /-- AW4 ⇒ identity (P) in degree `j = 1`. -/
  P : ∀ u v : V, hForm (Θ u) v + hForm u (Θ v) = hForm u v
  /-- AW2/AW6: eigenspaces are finite-dimensional. -/
  finiteDimensional_eigenspace : ∀ ρ : ℂ, FiniteDimensional ℂ (Θ.eigenspace ρ)
  /-- AW2 + (1), with multiplicity: `dim V¹_{Θ=ρ} = ord_ρ ξ` for every `ρ`. -/
  finrank_eigenspace : ∀ ρ : ℂ,
    Module.finrank ℂ (Θ.eigenspace ρ) = analyticOrderNatAt completedXi ρ

attribute [instance] ArithmeticWeilCohomologyQMult.instNormedAddCommGroup
  ArithmeticWeilCohomologyQMult.instInnerProductSpace

namespace ArithmeticWeilCohomologyQMult

variable (H : ArithmeticWeilCohomologyQMult)

lemma P' (u v : H.V) : hForm (H.Θ u) v + hForm u (H.Θ v) = ((1 : ℝ) : ℂ) * hForm u v := by
  simpa using H.P u v

/-- The eigenspace equals the generalized eigenspace, so the order condition is AW2's
`dim V¹_{Θ∼ρ} = ord_ρ ξ` for generalized eigenspaces. -/
theorem finrank_maxGenEigenspace (ρ : ℂ) :
    Module.finrank ℂ (H.Θ.maxGenEigenspace ρ) = analyticOrderNatAt completedXi ρ := by
  rw [maxGenEigenspace_eq_eigenspace_of_P H.Θ 1 H.P' ρ, H.finrank_eigenspace]

/-- Eigenvalues of `Θ₁` are exactly the nontrivial zeros of `ζ`. -/
theorem hasEigenvalue_iff (ρ : ℂ) : H.Θ.HasEigenvalue ρ ↔ IsNontrivialZetaZero ρ := by
  have := H.finiteDimensional_eigenspace ρ
  rw [Module.End.hasEigenvalue_iff, ← Submodule.one_le_finrank_iff, H.finrank_eigenspace,
    ← analyticOrderNatAt_completedXi_pos_iff]
  rfl

/-- Forgetting multiplicities gives an `ArithmeticWeilCohomologyQ`. -/
def toArithmeticWeilCohomologyQ : ArithmeticWeilCohomologyQ where
  V := H.V
  Θ := H.Θ
  locallyFinite := H.locallyFinite
  P := H.P
  zero_isEigenvalue ρ hρ := (H.hasEigenvalue_iff ρ).2 hρ
  isEigenvalue_zero ρ hρ := (H.hasEigenvalue_iff ρ).1 hρ

/-- **C-RH with multiplicities.** The multiplicity-faithful structure implies RH. -/
theorem riemannHypothesis (H : ArithmeticWeilCohomologyQMult) : RiemannHypothesis :=
  ArithmeticWeilCohomologyQ.riemannHypothesis H.toArithmeticWeilCohomologyQ

end ArithmeticWeilCohomologyQMult

/-! ## A diagonal model over an arbitrary index type -/

noncomputable section

namespace GenDiag

variable {ι : Type}

/-- `ℓ²(ι)`. -/
abbrev E (ι : Type) : Type := lp (fun _ : ι => ℂ) 2

/-- The finitely supported vectors of `ℓ²(ι)`. -/
def finSupp : Submodule ℂ (E ι) where
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

/-- The spectral core: finitely supported vectors. -/
abbrev V (ι : Type) : Type := ↥(finSupp (ι := ι))

lemma finite_support (f : V ι) : Set.Finite {i | (f : E ι) i ≠ 0} := f.2

variable (lam : ι → ℂ)

/-- `i ↦ lam i * f i`. -/
def mulVec (f : V ι) : E ι :=
  ⟨fun i => lam i * (f : E ι) i,
    (memℓp_zero ((finite_support f).subset fun i hi => by
      simp only [Set.mem_ofPred_eq] at hi ⊢
      intro h
      exact hi (by simp [h]))).of_exponent_ge (by simp)⟩

@[simp] lemma mulVec_apply (f : V ι) (i : ι) : mulVec lam f i = lam i * (f : E ι) i := rfl

lemma mulVec_mem (f : V ι) : mulVec lam f ∈ finSupp :=
  (finite_support f).subset fun i hi => by
    simp only [Set.mem_ofPred_eq, mulVec_apply] at hi ⊢
    intro h
    exact hi (by simp [h])

/-- The diagonal operator with eigenvalues `lam`. -/
def Θ : Module.End ℂ (V ι) where
  toFun f := ⟨mulVec lam f, mulVec_mem lam f⟩
  map_add' f g := by
    ext i
    simp [mul_add]
  map_smul' c f := by
    ext i
    simp only [mulVec_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] lemma Θ_apply (f : V ι) (i : ι) :
    ((Θ lam f : V ι) : E ι) i = lam i * (f : E ι) i := rfl

/-- (P) with `j = 1` when every `lam i` has real part `1/2`. -/
lemma P (hlam : ∀ i, (lam i).re = 1 / 2) (u v : V ι) :
    hForm (Θ lam u) v + hForm u (Θ lam v) = hForm u v := by
  simp only [hForm_def, Submodule.coe_inner, lp.inner_eq_tsum]
  rw [← (lp.summable_inner _ _).tsum_add (lp.summable_inner _ _)]
  congr 1
  funext i
  have hc : lam i + conj (lam i) = 1 := by
    rw [Complex.add_conj, hlam i]; norm_num
  simp only [Θ_apply, RCLike.inner_apply, map_mul]
  linear_combination ((u : E ι) i * conj ((v : E ι) i)) * hc

/-- The `Θ`-stable subspace of vectors supported in the support of `f`. -/
def supportedIn (f : V ι) : Submodule ℂ (V ι) where
  carrier := {g | ∀ i, (f : E ι) i = 0 → (g : E ι) i = 0}
  zero_mem' _ _ := rfl
  add_mem' hg hh i hi := by simp [hg i hi, hh i hi]
  smul_mem' c g hg i hi := by simp [hg i hi]

lemma finiteDimensional_supportedIn (f : V ι) : FiniteDimensional ℂ (supportedIn f) := by
  let s := {i | (f : E ι) i ≠ 0}
  let L : supportedIn f →ₗ[ℂ] (s → ℂ) :=
    { toFun g i := ((g : V ι) : E ι) i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Finite s := (finite_support f).to_subtype
  refine Module.Finite.of_injective L fun g h hgh => ?_
  ext i
  by_cases hi : (f : E ι) i = 0
  · rw [g.2 i hi, h.2 i hi]
  · exact congrFun hgh ⟨i, hi⟩

lemma locallyFinite (f : V ι) : ∃ W : Submodule ℂ (V ι),
    f ∈ W ∧ FiniteDimensional ℂ W ∧ W ∈ Module.End.invtSubmodule (Θ lam) := by
  refine ⟨supportedIn f, fun i hi => hi, finiteDimensional_supportedIn f, ?_⟩
  rw [Module.End.mem_invtSubmodule]
  intro g hg i hi
  simp [hg i hi]

lemma mem_eigenspace_iff (μ : ℂ) (f : V ι) :
    f ∈ (Θ lam).eigenspace μ ↔ ∀ i, lam i ≠ μ → (f : E ι) i = 0 := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h i hi
    have := congrArg (fun g : V ι => (g : E ι) i) h
    simp only [Θ_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hi
  · intro h
    ext i
    simp only [Θ_apply, SetLike.val_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hi : lam i = μ
    · rw [hi]
    · rw [h i hi, mul_zero, mul_zero]

variable {lam}

/-- The eigenspace for `μ` is `ℂ^{fiber of lam over μ}` when that fiber is finite. -/
def eigenspaceEquiv (μ : ℂ) (hfin : {i | lam i = μ}.Finite) :
    (Θ lam).eigenspace μ ≃ₗ[ℂ] ({i | lam i = μ} → ℂ) where
  toFun f k := (((f : V ι)) : E ι) k.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g :=
    ⟨⟨⟨fun i => if h : lam i = μ then g ⟨i, h⟩ else 0,
      (memℓp_zero (hfin.subset fun i hi => by
        by_contra h
        exact hi (by simp [dite_eq_right (show ¬lam i = μ from h)]))).of_exponent_ge (by simp)⟩,
      hfin.subset fun i hi => by
        by_contra h
        exact hi (by simp [dite_eq_right (show ¬lam i = μ from h)])⟩,
      (mem_eigenspace_iff lam μ _).2 fun i hi => by simp [hi]⟩
  left_inv f := by
    ext i
    by_cases h : lam i = μ
    · simp [h]
    · simp [h, (mem_eigenspace_iff lam μ _).1 f.2 i h]
  right_inv g := by
    funext k
    have hk : lam k.1 = μ := k.2
    simp [hk]

theorem finiteDimensional_eigenspace (μ : ℂ) (hfin : {i | lam i = μ}.Finite) :
    FiniteDimensional ℂ ((Θ lam).eigenspace μ) := by
  have : Finite {i | lam i = μ} := hfin.to_subtype
  exact LinearEquiv.finiteDimensional (eigenspaceEquiv μ hfin).symm

theorem finrank_eigenspace (μ : ℂ) (hfin : {i | lam i = μ}.Finite) :
    Module.finrank ℂ ((Θ lam).eigenspace μ) = Nat.card {i | lam i = μ} := by
  have : Fintype {i | lam i = μ} := hfin.fintype
  rw [(eigenspaceEquiv μ hfin).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end GenDiag

/-! ## The diagonal model with multiplicities -/

/-- The zero order of `ξ` at a nontrivial zero. -/
def zeroOrder (ρ : NontrivialZeros) : ℕ := analyticOrderNatAt completedXi ρ.1

/-- Index type: every nontrivial zero `ρ`, repeated `ord_ρ ξ` times. -/
abbrev ZerosWithMult : Type := Σ ρ : NontrivialZeros, Fin (zeroOrder ρ)

/-- The eigenvalue attached to an index. -/
def zerosWithMultVal (i : ZerosWithMult) : ℂ := i.1.1

def fiber_equiv {μ : ℂ} (h : IsNontrivialZetaZero μ) :
    {i : ZerosWithMult | zerosWithMultVal i = μ} ≃ Fin (zeroOrder ⟨μ, h⟩) :=
  (Equiv.subtypeEquivRight fun i => by
    change i.1.1 = μ ↔ i.1 = ⟨μ, h⟩
    exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩).trans (Equiv.sigmaSubtype (⟨μ, h⟩ : NontrivialZeros))

lemma fiber_isEmpty {μ : ℂ} (h : ¬IsNontrivialZetaZero μ) :
    IsEmpty {i : ZerosWithMult | zerosWithMultVal i = μ} :=
  ⟨fun i => h (i.2 ▸ i.1.1.2)⟩

lemma fiber_finite (μ : ℂ) : {i : ZerosWithMult | zerosWithMultVal i = μ}.Finite := by
  by_cases h : IsNontrivialZetaZero μ
  · exact Set.finite_coe_iff.1 (Finite.of_equiv _ (fiber_equiv h).symm)
  · have := fiber_isEmpty h
    exact Set.finite_coe_iff.1 inferInstance

lemma fiber_card (μ : ℂ) :
    Nat.card {i : ZerosWithMult | zerosWithMultVal i = μ} = analyticOrderNatAt completedXi μ := by
  by_cases h : IsNontrivialZetaZero μ
  · rw [Nat.card_congr (fiber_equiv h), Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  · have := fiber_isEmpty h
    rw [Nat.card_of_isEmpty, eq_comm, ← Nat.le_zero]
    exact not_lt.1 fun hpos => h ((analyticOrderNatAt_completedXi_pos_iff μ).1 hpos)

end

/-- **Diagonal model with multiplicities (C-CONV, faithful to AW2's order condition).** Under RH,
the finitely supported vectors of `ℓ²(Σ ρ, Fin (ord_ρ ξ))` with `Θ` acting on the `(ρ, k)`
coordinate by `ρ`. Each eigenspace `ρ` has dimension `ord_ρ ξ`. -/
noncomputable def multDiagonalModel (hRH : RiemannHypothesis) : ArithmeticWeilCohomologyQMult where
  V := GenDiag.V ZerosWithMult
  Θ := GenDiag.Θ zerosWithMultVal
  locallyFinite := GenDiag.locallyFinite zerosWithMultVal
  P := GenDiag.P zerosWithMultVal fun i => hRH i.1.1 i.1.2.1 i.1.2.2.1 i.1.2.2.2
  finiteDimensional_eigenspace μ := GenDiag.finiteDimensional_eigenspace μ (fiber_finite μ)
  finrank_eigenspace μ := by
    rw [GenDiag.finrank_eigenspace μ (fiber_finite μ), fiber_card]

/-- **C-CONV with multiplicities.** The multiplicity-faithful structure exists iff RH holds. -/
theorem nonempty_arithmeticWeilCohomologyQMult_iff :
    Nonempty ArithmeticWeilCohomologyQMult ↔ RiemannHypothesis :=
  ⟨fun ⟨H⟩ => H.riemannHypothesis, fun hRH => ⟨multDiagonalModel hRH⟩⟩

end WeilRH
