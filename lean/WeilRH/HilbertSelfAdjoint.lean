/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.Hilbert

/-!
# The self-adjoint operator `T = diag(τ_k)` (`prop:hilbert`, self-adjointness)

Given a Hilbert basis `(b_k)` of a complex Hilbert space `H` and real numbers `τ_k`, the diagonal
operator `diag(τ_k)` is the partially defined operator with domain
`{x | (τ_k ⟪b_k, x⟫)_k ∈ ℓ²}` (its maximal domain) and `x ↦ Σ τ_k ⟪b_k, x⟫ b_k`.

## Main results

* `Diag.op b τ`: `diag(τ_k)` as a `LinearPMap` on `H`.
* `Diag.op_symm`: `diag(τ_k)` is symmetric.
* `Diag.dense_domain`: its domain is dense.
* `Diag.isSelfAdjoint`: **`diag(τ_k)` is self-adjoint**, `T† = T`.
* `Hilbert.exists_selfAdjoint`: **`prop:hilbert`, self-adjointness clause.** For a spectral core
  `(V, Θ)` with a positive infinitesimal polarization `h` of weight `j`, the completion `𝓗` has a
  Hilbert basis `(b_k)` of eigenvectors from `V` for which `T = diag(τ_k)` is self-adjoint on `𝓗`
  and extends `-i(Θ - j/2)` on `V`, so `Θ = j/2 + iT` on `V`.

* `Diag.spectral_clause`, `Hilbert.exists_spectral`: **`prop:hilbert`, spectral clause.**
  `T` has pure point spectrum `{τ_k}` with finite multiplicities and no finite accumulation. Mathlib
  has no spectrum for unbounded operators, so this is stated by its content: each `b_k` is an
  eigenvector, every eigenvector lies in the finite span of the `b_k` with that eigenvalue
  (`Diag.mem_span_of_op_eq_smul`), and for `μ ∉ {τ_k}` the map `T - μ` is a bijection from the
  domain onto `𝓗` (`Diag.existsUnique_sub_smul_eq`).
-/

open Complex LinearPMap
open scoped ComplexConjugate

noncomputable section

namespace WeilRH.Hilbert.Diag

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (b : HilbertBasis ι ℂ H) (τ : ι → ℝ)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The coefficient sequence `(τ_k ⟪b_k, x⟫)_k`. -/
def coef (x : H) : ι → ℂ := fun k => (τ k : ℂ) * ⟪b k, x⟫

/-- The maximal domain of `diag(τ_k)`: those `x` with `(τ_k ⟪b_k, x⟫)_k ∈ ℓ²`. -/
def domain : Submodule ℂ H where
  carrier := {x | Memℓp (coef b τ x) 2}
  zero_mem' := by
    have : coef b τ 0 = 0 := by funext k; simp [coef]
    change Memℓp (coef b τ 0) 2
    rw [this]; exact zero_memℓp
  add_mem' {x y} hx hy := by
    have : coef b τ (x + y) = coef b τ x + coef b τ y := by
      funext k; simp [coef, mul_add]
    change Memℓp (coef b τ (x + y)) 2
    rw [this]; exact hx.add hy
  smul_mem' c x hx := by
    have : coef b τ (c • x) = c • coef b τ x := by
      funext k; simp only [coef, inner_smul_right, Pi.smul_apply, smul_eq_mul]; ring
    change Memℓp (coef b τ (c • x)) 2
    rw [this]; exact hx.const_smul c

omit [CompleteSpace H] in
theorem mem_domain_iff (x : H) : x ∈ domain b τ ↔ Memℓp (coef b τ x) 2 := Iff.rfl

/-- The `ℓ²` element `(τ_k ⟪b_k, x⟫)_k` for `x` in the domain. -/
def coefLp (x : domain b τ) : lp (fun _ : ι => ℂ) 2 := ⟨coef b τ x, x.2⟩

/-- `diag(τ_k)` as a partially defined operator on `H`. -/
noncomputable def op : H →ₗ.[ℂ] H where
  domain := domain b τ
  toFun :=
    { toFun := fun x => b.repr.symm (coefLp b τ x)
      map_add' := fun x y => by
        rw [← _root_.map_add]; congr 1
        apply lp.ext; funext k
        simp [coefLp, coef, mul_add]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← _root_.map_smul]; congr 1
        apply lp.ext; funext k
        simp only [coefLp, coef, Submodule.coe_smul, inner_smul_right, lp.coeFn_smul,
          Pi.smul_apply, smul_eq_mul]
        ring }

omit [CompleteSpace H] in
theorem repr_op (x : (op b τ).domain) (k : ι) : b.repr (op b τ x) k = (τ k : ℂ) * ⟪b k, x⟫ := by
  change b.repr (b.repr.symm (coefLp b τ x)) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]; rfl

omit [CompleteSpace H] in
theorem inner_op (x : (op b τ).domain) (k : ι) : ⟪b k, op b τ x⟫ = (τ k : ℂ) * ⟪b k, x⟫ := by
  rw [← b.repr_apply_apply]; exact repr_op b τ x k

omit [CompleteSpace H] in
/-- `diag(τ_k)` is symmetric: `⟪Tx, y⟫ = ⟪x, Ty⟫` on its domain. -/
theorem op_symm (x y : (op b τ).domain) : ⟪op b τ x, (y : H)⟫ = ⟪(x : H), op b τ y⟫ := by
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map (x : H), lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  rw [repr_op, repr_op, b.repr_apply_apply, b.repr_apply_apply, RCLike.inner_apply',
    RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

omit [CompleteSpace H] in
theorem basis_mem_domain (i : ι) : b i ∈ domain b τ := by
  classical
  have : coef b τ (b i) = Pi.single i (τ i : ℂ) := by
    funext k
    simp only [coef, orthonormal_iff_ite.1 b.orthonormal k i, Pi.single_apply]
    split_ifs with h1 <;> simp_all
  rw [mem_domain_iff, this]
  have := (lp.single (E := fun _ : ι => ℂ) 2 i (τ i : ℂ)).2
  rwa [lp.coeFn_single] at this

omit [CompleteSpace H] in
theorem op_basis (i : ι) : op b τ ⟨b i, basis_mem_domain b τ i⟩ = (τ i : ℂ) • b i := by
  classical
  apply b.repr.injective
  apply lp.ext; funext k
  rw [repr_op, _root_.map_smul, lp.coeFn_smul, Pi.smul_apply, b.repr_self, smul_eq_mul]
  simp only [orthonormal_iff_ite.1 b.orthonormal k i, lp.single_apply, Pi.single_apply]
  split_ifs with h1 <;> simp_all

omit [CompleteSpace H] in
/-- The domain of `diag(τ_k)` is dense: it contains every `b_k`. -/
theorem dense_domain : Dense ((op b τ).domain : Set H) := by
  have hle : Submodule.span ℂ (Set.range b) ≤ domain b τ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact basis_mem_domain b τ i)
  have hd : Dense (Submodule.span ℂ (Set.range b) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact b.dense_span
  exact hd.mono hle

/-- **`diag(τ_k)` is self-adjoint**: `T† = T`. -/
theorem isSelfAdjoint : IsSelfAdjoint (op b τ) := by
  rw [isSelfAdjoint_def]
  have hT := dense_domain b τ
  have hsym : (op b τ).IsFormalAdjoint (op b τ) := fun x y => op_symm b τ x y
  refine le_antisymm ?_ (hsym.le_adjoint hT)
  -- `T† ≤ T`: the adjoint's coefficients are forced by testing on the basis.
  have key : ∀ y : (op b τ)†.domain, ∀ k, ⟪b k, (op b τ)† y⟫ = (τ k : ℂ) * ⟪b k, (y : H)⟫ := by
    intro y k
    have h1 := adjoint_isFormalAdjoint hT y ⟨b k, basis_mem_domain b τ k⟩
    -- `⟪T† y, b k⟫ = ⟪y, T b k⟫ = τ_k ⟪y, b k⟫`
    rw [op_basis, inner_smul_right] at h1
    rw [← inner_conj_symm, h1, map_mul, Complex.conj_ofReal, inner_conj_symm]
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · have hmem : coef b τ y = fun k => b.repr ((op b τ)† ⟨y, hy⟩) k := by
      funext k; rw [b.repr_apply_apply, key ⟨y, hy⟩ k]; rfl
    change Memℓp (coef b τ y) 2
    rw [hmem]
    exact (b.repr _).2
  · apply b.repr.injective
    apply lp.ext; funext k
    rw [repr_op, b.repr_apply_apply, key, ← hyz]

/-! ### The spectral clause -/

omit [CompleteSpace H] in
/-- **Eigenvectors of `diag(τ_k)`**: `Tx = μx` iff every coefficient of `x` outside
`{k | τ_k = μ}` vanishes. -/
theorem op_eq_smul_iff (x : (op b τ).domain) (μ : ℂ) :
    op b τ x = μ • (x : H) ↔ ∀ k, (τ k : ℂ) ≠ μ → ⟪b k, (x : H)⟫ = 0 := by
  constructor
  · intro h k hk
    have h1 := congrArg (fun z => ⟪b k, z⟫) h
    simp only [inner_op, inner_smul_right] at h1
    have h2 : ((τ k : ℂ) - μ) * ⟪b k, (x : H)⟫ = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hk)
  · intro h
    apply b.repr.injective; apply lp.ext; funext k
    rw [repr_op, _root_.map_smul, lp.coeFn_smul, Pi.smul_apply, b.repr_apply_apply, smul_eq_mul]
    by_cases hk : (τ k : ℂ) = μ
    · rw [hk]
    · rw [h k hk]; simp

omit [CompleteSpace H] in
/-- **Finite multiplicities**: if only finitely many `τ_k` equal `μ`, every eigenvector of
`diag(τ_k)` with eigenvalue `μ` lies in the finite-dimensional span of those `b_k`. -/
theorem mem_span_of_op_eq_smul {μ : ℂ} (hfin : {k | (τ k : ℂ) = μ}.Finite)
    (x : (op b τ).domain) (hx : op b τ x = μ • (x : H)) :
    (x : H) ∈ Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ}) := by
  classical
  set F := hfin.toFinset
  have hsum : (x : H) = ∑ j ∈ F, ⟪b j, (x : H)⟫ • b j := by
    apply b.repr.injective; apply lp.ext; funext k
    rw [_root_.map_sum, lp.coeFn_sum, Finset.sum_apply]
    simp only [_root_.map_smul, lp.coeFn_smul, Pi.smul_apply, b.repr_self, lp.single_apply,
      Pi.single_apply, smul_eq_mul, b.repr_apply_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have : (τ k : ℂ) ≠ μ := fun h => hk (hfin.mem_toFinset.2 h)
      exact (op_eq_smul_iff b τ x μ).1 hx k this
  rw [hsum]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨j, hfin.mem_toFinset.1 hj, rfl⟩

omit [CompleteSpace H] in
/-- **The resolvent**: if `μ` keeps a positive distance `δ` from every `τ_k`, then
`T - μ` maps the domain of `diag(τ_k)` bijectively onto `H`. -/
theorem existsUnique_sub_smul_eq (μ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ k, δ ≤ ‖(τ k : ℂ) - μ‖) (y : H) :
    ∃! x : (op b τ).domain, op b τ x - μ • (x : H) = y := by
  have hne : ∀ k, (τ k : ℂ) - μ ≠ 0 := fun k h => by
    have := hgap k; rw [h, norm_zero] at this; linarith
  set c : ι → ℂ := fun k => ⟪b k, y⟫ / ((τ k : ℂ) - μ)
  have hc : Memℓp c 2 := by
    refine Memℓp.mono' (((b.repr y).2).const_mul ((δ : ℂ)⁻¹)) fun k => ?_
    rw [norm_div, norm_mul, b.repr_apply_apply, norm_inv, Complex.norm_real, Real.norm_of_nonneg hδ.le,
      div_eq_inv_mul]
    gcongr
    exact hgap k
  set x0 : H := b.repr.symm ⟨c, hc⟩
  have hx0 : ∀ k, ⟪b k, x0⟫ = c k := fun k => by
    rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : coef b τ x0 = fun k => b.repr y k + μ * c k := by
    funext k
    simp only [coef, hx0, b.repr_apply_apply, c]
    field_simp [hne k]
    ring
  have hdom : x0 ∈ (op b τ).domain := by
    change Memℓp (coef b τ x0) 2
    rw [hcoef]; exact (b.repr y).2.add (hc.const_mul μ)
  have heq : op b τ ⟨x0, hdom⟩ - μ • x0 = y := by
    apply b.repr.injective; apply lp.ext; funext k
    rw [_root_.map_sub, lp.coeFn_sub, Pi.sub_apply, repr_op, _root_.map_smul, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, b.repr_apply_apply, hx0, b.repr_apply_apply]
    simp only [c]
    field_simp [hne k]
  refine ⟨⟨x0, hdom⟩, heq, fun x hx => ?_⟩
  have hz : op b τ (x - ⟨x0, hdom⟩) = μ • ((x - ⟨x0, hdom⟩ : (op b τ).domain) : H) := by
    rw [LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hx.trans heq.symm
  have h0 : ((x - ⟨x0, hdom⟩ : (op b τ).domain) : H) = 0 := by
    apply b.repr.injective; apply lp.ext; funext k
    rw [b.repr_apply_apply, (op_eq_smul_iff b τ _ μ).1 hz k (sub_ne_zero.1 (hne k))]
    simp
  exact Subtype.ext (sub_eq_zero.1 (by simpa using h0))

omit [CompleteSpace H] in
/-- **`prop:hilbert`, spectral clause** (eigenvector form). Suppose every value is taken by only
finitely many `τ_k` and `{τ_k}` has no finite accumulation point. Then `T = diag(τ_k)` has pure
point spectrum `{τ_k}` with finite multiplicities:
1. each `b_k` is an eigenvector, `T b_k = τ_k b_k`;
2. every eigenvector with eigenvalue `μ` lies in the finite-dimensional span of `{b_k | τ_k = μ}`;
3. for `μ ∉ {τ_k}`, `T - μ` maps the domain of `T` bijectively onto `H`, so `μ` is in the
   resolvent set. -/
theorem spectral_clause (hfin : ∀ μ : ℂ, {k | (τ k : ℂ) = μ}.Finite)
    (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range fun k => (τ k : ℂ)))) :
    (∀ k, op b τ ⟨b k, basis_mem_domain b τ k⟩ = (τ k : ℂ) • b k) ∧
    (∀ (μ : ℂ) (x : (op b τ).domain), op b τ x = μ • (x : H) →
      (x : H) ∈ Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ})) ∧
    (∀ μ : ℂ, μ ∉ Set.range (fun k => (τ k : ℂ)) →
      ∀ y : H, ∃! x : (op b τ).domain, op b τ x - μ • (x : H) = y) := by
  refine ⟨op_basis b τ, fun μ x hx => mem_span_of_op_eq_smul b τ (hfin μ) x hx, fun μ hμ y => ?_⟩
  -- a positive gap around `μ`, from discreteness
  have h := hdisc μ
  rw [accPt_iff_nhds] at h
  push Not at h
  obtain ⟨U, hU, hUS⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine existsUnique_sub_smul_eq b τ μ hε (fun k => ?_) y
  by_contra hlt
  push Not at hlt
  have hmem : (τ k : ℂ) ∈ U := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt)
  exact hμ ⟨k, hUS _ ⟨hmem, k, rfl⟩⟩

end WeilRH.Hilbert.Diag

namespace WeilRH.Hilbert

open WeilRH.AW4Forms

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The inclusion `V → 𝓗`. -/
def incl (h : PosHermForm V) : V →ₗ[ℂ] Completion h :=
  (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := HSpace h)).toLinearMap

theorem incl_apply (h : PosHermForm V) (x : V) :
    incl h x = ((show HSpace h from x : HSpace h) : Completion h) := rfl

theorem inner_incl (h : PosHermForm V) (x y : V) : ⟪incl h x, incl h y⟫ = h.toFun y x := by
  rw [incl_apply, incl_apply, UniformSpace.Completion.inner_coe]; rfl

/-- **`prop:hilbert`, self-adjointness clause.** If `(V, Θ)` is a spectral core and `h` a positive
infinitesimal polarization of weight `j`, the completion `𝓗` of `(V, h)` has a Hilbert basis
`(b_k)` of images of eigenvectors `e_k ∈ V`, `Θ e_k = (j/2 + i τ_k) e_k` with `τ_k ∈ ℝ`, such that
`T = diag(τ_k)` (on its maximal domain) is self-adjoint and extends `-i(Θ - j/2)` on `V`; hence
`Θ = j/2 + iT` on `V` (`theta_eq`). -/
theorem exists_selfAdjoint {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hpol : Suspension.IsInfPol h Θ j) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ),
      (∀ k, b k = incl h (e k)) ∧
      (∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k) ∧
      IsSelfAdjoint (Diag.op b τ) ∧
      ∀ x : V, ∃ hx : incl h x ∈ (Diag.op b τ).domain,
        Diag.op b τ ⟨incl h x, hx⟩ = incl h (T Θ j x) := by
  obtain ⟨ι, b, e, τ, hb0, he⟩ := exists_hilbertBasis hS hpol
  have hb : ∀ k, b k = incl h (e k) := fun k => hb0 k
  refine ⟨ι, b, e, τ, hb, he, Diag.isSelfAdjoint b τ, ?_⟩
  have hE := aw4E_of_aw4V hS ⟨h, hpol⟩
  -- coefficientwise identity `τ_k ⟪b_k, x⟫ = ⟪b_k, T x⟫`, checked on eigenvectors
  have key : ∀ x : V, ∀ k, (τ k : ℂ) * ⟪b k, incl h x⟫ = ⟪b k, incl h (T Θ j x)⟫ := by
    intro x k
    have hx : x ∈ ⨆ ρ, Θ.eigenspace ρ := by rw [(AW4Forms.iSup_eigenspace_eq_top hE : ⨆ ρ, Θ.eigenspace ρ = ⊤)]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem ρ x hx =>
      by_cases hx0 : x = 0
      · subst hx0; simp
      have hρ : ρ.re = j / 2 :=
        re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)
      have hΘx : Θ x = ((j / 2 : ℂ) + I * (ρ.im : ℂ)) • x := by
        rw [Module.End.mem_eigenspace_iff.1 hx]; congr 1
        apply Complex.ext <;> simp [hρ]
      rw [T_apply_of_eq hΘx, _root_.map_smul, inner_smul_right, hb, inner_incl]
      by_cases hk : ρ = (j / 2 : ℂ) + I * (τ k : ℂ)
      · have : ρ.im = τ k := by rw [hk]; simp
        rw [this]
      · have hek : e k ∈ Θ.eigenspace ((j / 2 : ℂ) + I * (τ k : ℂ)) :=
          Module.End.mem_eigenspace_iff.2 (he k)
        rw [inner_eq_zero_of_ne hS hpol hk hx hek, mul_zero, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [_root_.map_add, _root_.map_add, _root_.map_add, inner_add_right,
        inner_add_right, mul_add, hx, hy]
  intro x
  have hcoef : Diag.coef b τ (incl h x) = fun k => b.repr (incl h (T Θ j x)) k := by
    funext k; rw [b.repr_apply_apply, ← key]; rfl
  have hdom : incl h x ∈ (Diag.op b τ).domain := by
    change Memℓp (Diag.coef b τ (incl h x)) 2
    rw [hcoef]; exact (b.repr _).2
  refine ⟨hdom, ?_⟩
  apply b.repr.injective
  apply lp.ext; funext k
  rw [Diag.repr_op, b.repr_apply_apply, key]

/-- The eigenvalues `τ_k` of `exists_selfAdjoint` take each value finitely often and have no
finite accumulation point: they inherit both from the spectral core. -/
theorem fin_disc_of_basis {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) {ι : Type u} (b : HilbertBasis ι ℂ (Completion h))
    (e : ι → V) (τ : ι → ℝ) (hb : ∀ k, b k = incl h (e k))
    (he : ∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k) :
    (∀ μ : ℂ, {k | (τ k : ℂ) = μ}.Finite) ∧
    (∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range fun k => (τ k : ℂ)))) := by
  have hli : LinearIndependent ℂ e := by
    have : LinearIndependent ℂ (incl h ∘ e) := by
      have hb' : (b : ι → Completion h) = incl h ∘ e := funext hb
      rw [← hb']; exact b.orthonormal.linearIndependent
    exact this.of_comp
  let f : ℂ → ℂ := fun c => (j / 2 : ℂ) + I * c
  have hf : ∀ c d, dist (f c) (f d) = dist c d := fun c d => by
    simp [f, dist_eq_norm, ← mul_sub]
  have hspec : ∀ k, f (τ k) ∈ Spectral.spec Θ := fun k => by
    have he0 : e k ≠ 0 := hli.ne_zero k
    intro hbot
    have hmem : e k ∈ Θ.maxGenEigenspace (f (τ k)) :=
      Θ.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (he k))
    rw [hbot] at hmem
    exact he0 hmem
  refine ⟨fun μ => ?_, fun z hz => ?_⟩
  · -- the `e_k` with `τ_k = μ` are independent vectors of one finite-dimensional eigenspace
    let E := Θ.maxGenEigenspace (f μ)
    have : FiniteDimensional ℂ E := hS.finiteDimensional _
    let s := {k | (τ k : ℂ) = μ}
    have hmemE : ∀ k : s, e k ∈ E := fun k => by
      have hk : (τ k : ℂ) = μ := k.2
      have := Θ.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (he k))
      rwa [hk] at this
    have hliE : LinearIndependent ℂ (fun k : s => (⟨e k, hmemE k⟩ : E)) := by
      apply LinearIndependent.of_comp E.subtype
      exact hli.comp (fun k : s => (k : ι)) Subtype.val_injective
    have := hliE.finite
    exact Set.toFinite s
  · -- an accumulation point of `{τ_k}` would give one of `spec Θ`
    apply hS.noAccPt (f z)
    rw [accPt_iff_nhds] at hz ⊢
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨y, ⟨hy, k, rfl⟩, hyz⟩ := hz (Metric.ball z ε) (Metric.ball_mem_nhds z hε)
    refine ⟨f (τ k), ⟨hball ?_, hspec k⟩, fun h' => hyz ?_⟩
    · rw [Metric.mem_ball, hf]; exact hy
    · have := hf (τ k) z
      rw [h', dist_self] at this
      exact dist_eq_zero.1 this.symm

/-- **`prop:hilbert`, spectral clause.** For a spectral core `(V, Θ)` with a positive
infinitesimal polarization `h` of weight `j`, the self-adjoint operator `T = diag(τ_k)` on the
completion `𝓗` (`exists_selfAdjoint`, extending `-i(Θ - j/2)`) has pure point spectrum `{τ_k}`
with finite multiplicities and no finite accumulation point: each `b_k` is an eigenvector, every
eigenvector lies in the finite-dimensional span of the `b_k` with that eigenvalue, and for every
`μ ∉ {τ_k}` the operator `T - μ` maps its domain bijectively onto `𝓗`. -/
theorem exists_spectral {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hpol : Suspension.IsInfPol h Θ j) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ),
      (∀ k, b k = incl h (e k)) ∧
      (∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k) ∧
      IsSelfAdjoint (Diag.op b τ) ∧
      (∀ x : V, ∃ hx : incl h x ∈ (Diag.op b τ).domain,
        Diag.op b τ ⟨incl h x, hx⟩ = incl h (T Θ j x)) ∧
      (∀ μ : ℂ, {k | (τ k : ℂ) = μ}.Finite) ∧
      (∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range fun k => (τ k : ℂ)))) ∧
      (∀ k, Diag.op b τ ⟨b k, Diag.basis_mem_domain b τ k⟩ = (τ k : ℂ) • b k) ∧
      (∀ (μ : ℂ) (x : (Diag.op b τ).domain), Diag.op b τ x = μ • (x : Completion h) →
        (x : Completion h) ∈ Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ})) ∧
      (∀ μ : ℂ, μ ∉ Set.range (fun k => (τ k : ℂ)) →
        ∀ y : Completion h, ∃! x : (Diag.op b τ).domain,
          Diag.op b τ x - μ • (x : Completion h) = y) := by
  obtain ⟨ι, b, e, τ, hb, he, hsa, hext⟩ := exists_selfAdjoint hS hpol
  obtain ⟨hfin, hdisc⟩ := fin_disc_of_basis hS b e τ hb he
  exact ⟨ι, b, e, τ, hb, he, hsa, hext, hfin, hdisc, Diag.spectral_clause b τ hfin hdisc⟩

end WeilRH.Hilbert

end
