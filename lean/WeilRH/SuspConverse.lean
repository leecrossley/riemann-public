/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Suspension

/-!
# The converse of the suspension (`notes.tex`, `prop:susp-converse`)

`prop:susp-converse`: if `ĥ` is a positive infinitesimal polarization of weight `j` on the
logarithmic suspension `(V̂, Θ)` of an invertible `F`, the restricted form `h` of `ĥ` for any
choice `(ρ_α)` (`def:log-susp` (b)) is a positive Frobenius polarization of weight `j` on `(V, F)`.

## Main results

* `WeilRH.Suspension.eq_zero_of_logSeries_eq_zero`: a nilpotent `U` whose truncated logarithm
  series `∑_{k=1}^n (-1)^{k+1} U^k / k` (`n ≥ 1`) vanishes is `0`.
* `WeilRH.Suspension.genProj`: the projection of `V` onto `V_{(α)}` along the other generalized
  eigenspaces.
* `WeilRH.Suspension.restrictedForm` (`def:log-susp` (b)): `h(u, v) = ∑_α ĥ(u_α, v_α)`, with
  `u_α ∈ V_{(α)}` placed in the summand `V̂_{ρ_α}`.
* `WeilRH.Suspension.thetaBlock_eq_of_infPol`, `re_eq_of_infPol`: under a positive infinitesimal
  polarization every block of `Θ` is the scalar `ρ` and `Re ρ = j/2` (the step of the proof that
  invokes `prop:purity`).
* `WeilRH.Suspension.isFrobPol_restrictedForm` (**`prop:susp-converse`**).

## Encoding

A choice `(ρ_α)` is a map `σ` from the eigenvalues `{α // F.HasEigenvalue α}` to `ℂ` with
`q^{σ α} = α` (a *sheet*, `def:aw4-EF` (b)). Its existence forces every eigenvalue to be nonzero,
so `F` is automatically invertible and no separate hypothesis is stated.
-/

open Module Complex
open scoped ComplexConjugate DirectSum

namespace WeilRH.Suspension

open WeilRH.Spectral

/-! ### The logarithm series of a nilpotent element -/

/-- **Injectivity of the logarithm on unipotents.** If `U` is nilpotent and the truncated
logarithm series `∑_{k=1}^n (-1)^{k+1} U^k / k` vanishes for some `n ≥ 1`, then `U = 0`: the series
is `U · W` with `W = 1 + (nilpotent)` a unit. -/
theorem eq_zero_of_logSeries_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {U : A}
    (hU : IsNilpotent U) {n : ℕ} (hn : 1 ≤ n)
    (h : ∑ k ∈ Finset.Icc 1 n, ((-1 : ℂ) ^ (k + 1) / k) • U ^ k = 0) : U = 0 := by
  classical
  set c : ℕ → ℂ := fun k => (-1 : ℂ) ^ (k + 1) / k
  set W : A := ∑ k ∈ Finset.Icc 1 n, c k • U ^ (k - 1)
  have hUW : U * W = ∑ k ∈ Finset.Icc 1 n, c k • U ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mul_smul_comm, ← pow_succ', Nat.sub_add_cancel (Finset.mem_Icc.1 hk).1]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
  have hW : W = 1 + ∑ k ∈ (Finset.Icc 1 n).erase 1, c k • U ^ (k - 1) := by
    rw [show W = ∑ k ∈ Finset.Icc 1 n, c k • U ^ (k - 1) from rfl, ← Finset.add_sum_erase _ _ h1]
    congr 1
    simp [c]
  have hnil : IsNilpotent (∑ k ∈ (Finset.Icc 1 n).erase 1, c k • U ^ (k - 1)) := by
    refine Commute.isNilpotent_sum (fun k hk => ?_) (fun k l _ _ => ?_)
    · have hk2 : 2 ≤ k := by
        have := Finset.mem_erase.1 hk
        have := Finset.mem_Icc.1 this.2
        omega
      exact (hU.pow_of_pos (by omega)).smul _
    · exact ((Commute.refl U).pow_pow _ _).smul_left _ |>.smul_right _
  have hunit : IsUnit W := hW ▸ hnil.isUnit_one_add
  rw [← hUW] at h
  exact (hunit.mul_left_eq_zero).1 h

/-! ### Generalized-eigenspace projections -/

section Proj

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (F : Module.End ℂ V)

/-- `V = ⊕_α V_{(α)}` (finite dimension over `ℂ`). -/
theorem isInternal_maxGenEigenspace : DirectSum.IsInternal fun α => F.maxGenEigenspace α :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨F.independent_maxGenEigenspace, F.iSup_maxGenEigenspace_eq_top⟩

/-- The decomposition `V ≃ ⨁_α V_{(α)}`. -/
noncomputable abbrev genEquiv : (⨁ α, F.maxGenEigenspace α) ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap fun α => F.maxGenEigenspace α)
    (isInternal_maxGenEigenspace F)

/-- The projection `V → V_{(α)}` along the other generalized eigenspaces. -/
noncomputable def genProj (α : ℂ) : V →ₗ[ℂ] F.maxGenEigenspace α :=
  DirectSum.component ℂ ℂ (fun α => F.maxGenEigenspace α) α ∘ₗ (genEquiv F).symm.toLinearMap

variable {F}

theorem genProj_of_mem {α : ℂ} {u : V} (hu : u ∈ F.maxGenEigenspace α) :
    genProj F α u = ⟨u, hu⟩ :=
  (isInternal_maxGenEigenspace F).ofBijective_coeLinearMap_of_mem hu

theorem genProj_of_mem_ne {α β : ℂ} (hαβ : α ≠ β) {u : V} (hu : u ∈ F.maxGenEigenspace α) :
    genProj F β u = 0 :=
  (isInternal_maxGenEigenspace F).ofBijective_coeLinearMap_of_mem_ne hαβ hu

omit [FiniteDimensional ℂ V] in
/-- `V_{(α)} = 0` when `α` is not an eigenvalue. -/
theorem maxGenEigenspace_eq_bot {α : ℂ} (hα : ¬ F.HasEigenvalue α) : F.maxGenEigenspace α = ⊥ :=
  not_not.1 fun h => hα ((Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one
    (f := F) (μ := α) (k := ⊤) (by simp)).1 h)

theorem genProj_eq_zero_of_not {α : ℂ} (hα : ¬ F.HasEigenvalue α) (u : V) : genProj F α u = 0 :=
  Subtype.ext ((Submodule.mem_bot ℂ).1 (maxGenEigenspace_eq_bot hα ▸ (genProj F α u).2))

/-- The eigenvalues of `F`, as a type. -/
abbrev Eig (F : Module.End ℂ V) : Type _ := {α : ℂ // F.HasEigenvalue α}

noncomputable instance (F : Module.End ℂ V) : Fintype (Eig F) :=
  (Module.End.finite_hasEigenvalue F).fintype

/-- `u = Σ_α u_α`, summed over the eigenvalues. -/
theorem sum_genProj (u : V) : ∑ α : Eig F, (genProj F α.1 u : V) = u := by
  classical
  have hu : DirectSum.coeLinearMap (fun α => F.maxGenEigenspace α) ((genEquiv F).symm u) = u :=
    (genEquiv F).apply_symm_apply u
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] at hu
  conv_rhs => rw [← hu]
  have hsub : ((genEquiv F).symm u).support ⊆ eigenFinset F := by
    intro α hα
    rw [eigenFinset, Set.Finite.mem_toFinset]
    by_contra hne
    exact (DFinsupp.mem_support_iff.1 hα) (genProj_eq_zero_of_not hne u)
  rw [← Finset.sum_subtype (eigenFinset F) (fun α => by
    rw [eigenFinset, Set.Finite.mem_toFinset]; exact Iff.rfl) (fun α => (genProj F α u : V))]
  refine (Finset.sum_subset hsub fun α _ hα => ?_).symm
  change (((genEquiv F).symm u) α : V) = 0
  rw [DFinsupp.notMem_support_iff.1 hα, ZeroMemClass.coe_zero]

/-- If `F = β` on every `V_{(β)}`, the projections intertwine `F` with the scalar `α`. -/
theorem genProj_apply_of_smul (hF : ∀ β, ∀ x ∈ F.maxGenEigenspace β, F x = β • x) (α : ℂ)
    (u : V) : (genProj F α (F u) : V) = α • (genProj F α u : V) := by
  classical
  conv_lhs => rw [← sum_genProj (F := F) u]
  rw [map_sum, map_sum, Submodule.coe_sum]
  simp_rw [hF _ _ (genProj F _ u).2, map_smul, Submodule.coe_smul]
  by_cases hα : F.HasEigenvalue α
  · rw [Finset.sum_eq_single (⟨α, hα⟩ : Eig F)
      (fun β _ hβ => by
        rw [genProj_of_mem_ne (fun h => hβ (Subtype.ext h)) (genProj F β.1 u).2,
          ZeroMemClass.coe_zero, smul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [genProj_of_mem (genProj F α u).2]
  · rw [genProj_eq_zero_of_not hα u, ZeroMemClass.coe_zero, smul_zero]
    exact Finset.sum_eq_zero fun β _ => by
      rw [genProj_eq_zero_of_not hα, ZeroMemClass.coe_zero, smul_zero]

end Proj

/-! ### The restricted form (`def:log-susp` (b)) -/

section Restricted

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q : ℝ}

/-- The pullback of a positive definite Hermitian form along an injective linear map. -/
def _root_.WeilRH.PosHermForm.comap {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (h : PosHermForm W) (f : U →ₗ[ℂ] W) (hf : Function.Injective f) : PosHermForm U where
  toFun u v := h.toFun (f u) (f v)
  add_left u u' v := by rw [map_add, h.add_left]
  smul_left c u v := by rw [map_smul, h.smul_left]
  conj_symm u v := h.conj_symm _ _
  re_pos u hu := h.re_pos _ fun h0 => hu (hf (h0.trans (map_zero f).symm))

/-- A *sheet*: a choice `ρ_α ∈ Σ_q(α)` for every eigenvalue `α` (`def:aw4-EF` (b)). -/
def IsSheet (F : Module.End ℂ V) (q : ℝ) (σ : Eig F → ℂ) : Prop := ∀ α, qpow q (σ α) = α.1

variable {σ : Eig F → ℂ}

/-- The index `ρ_α` of the summand `V̂_{ρ_α} = V_{(α)}`. -/
def sheetIdx (hσ : IsSheet F q σ) (α : Eig F) : Idx F q := ⟨σ α, by rw [hσ α]; exact α.2⟩

omit [FiniteDimensional ℂ V] in
lemma summand_sheetIdx (hσ : IsSheet F q σ) (α : Eig F) :
    Summand F q (sheetIdx hσ α) = F.maxGenEigenspace α.1 := by
  rw [Summand, sheetIdx, hσ α]

/-- The sheet map on `V_{(α)}`: `u ↦ u_α`, placed in the summand `V̂_{ρ_α}` of `V̂`. -/
noncomputable def sheetCopy (hσ : IsSheet F q σ) (α : Eig F) : V →ₗ[ℂ] SuspSpace F q :=
  DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) (sheetIdx hσ α) ∘ₗ
    Submodule.inclusion (summand_sheetIdx hσ α).ge ∘ₗ genProj F α.1

lemma sheetCopy_apply_self (hσ : IsSheet F q σ) (α : Eig F) (u : V) :
    ((sheetCopy hσ α u) (sheetIdx hσ α) : V) = genProj F α.1 u := by
  rw [sheetCopy, LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.lof_apply,
    Submodule.coe_inclusion]

/-- **`def:log-susp` (b)**: the restricted form `h(u, v) = Σ_α ĥ(u_α, v_α)` of a positive definite
Hermitian form `ĥ` on `V̂` for the choice `σ`, the orthogonal sum of the restrictions of `ĥ` to the
summands `V̂_{ρ_α} = V_{(α)}`. -/
noncomputable def restrictedForm (hh : PosHermForm (SuspSpace F q)) (hσ : IsSheet F q σ) :
    PosHermForm V where
  toFun u v := ∑ α : Eig F, hh.toFun (sheetCopy hσ α u) (sheetCopy hσ α v)
  add_left u u' v := by simp [hh.add_left, Finset.sum_add_distrib]
  smul_left c u v := by simp [hh.smul_left, Finset.mul_sum]
  conj_symm u v := by simp [map_sum, hh.conj_symm]
  re_pos u hu := by
    obtain ⟨α, hα0⟩ : ∃ α : Eig F, genProj F α.1 u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hu
      rw [← sum_genProj (F := F) u]
      exact Finset.sum_eq_zero fun α _ => by rw [hcon α, ZeroMemClass.coe_zero]
    have hc : sheetCopy hσ α u ≠ 0 := by
      intro h0
      have := sheetCopy_apply_self hσ α u
      rw [h0] at this
      exact hα0 (Subtype.ext (by simpa using this.symm))
    rw [Complex.re_sum]
    refine Finset.sum_pos' (fun β _ => ?_) ⟨α, Finset.mem_univ _, hh.re_pos _ hc⟩
    by_cases hβ : sheetCopy hσ β u = 0
    · rw [hβ, hh.zero_left]; simp
    · exact (hh.re_pos _ hβ).le

end Restricted

/-! ### Purity on each summand and `prop:susp-converse` -/

section Converse

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q j : ℝ} {hh : PosHermForm (SuspSpace F q)}

omit [FiniteDimensional ℂ V] in
lemma theta_lof (ρ : Idx F q) (x : Summand F q ρ) :
    theta F q (DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ x) =
      DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ (thetaBlock F q ρ x) :=
  DirectSum.lmap_lof _ _ _

omit [FiniteDimensional ℂ V] in
lemma lof_injective (ρ : Idx F q) :
    Function.Injective (DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ) := fun x y hxy => by
  simpa [DirectSum.lof_apply] using congrArg (fun z => z ρ) hxy

omit [FiniteDimensional ℂ V] in
/-- `ĥ` restricted to the summand `V̂_ρ`. -/
noncomputable def blockForm (hh : PosHermForm (SuspSpace F q)) (ρ : Idx F q) :
    PosHermForm (Summand F q ρ) :=
  hh.comap _ (lof_injective ρ)

omit [FiniteDimensional ℂ V] in
/-- The summand `V̂_ρ = V_{(q^ρ)}` is nonzero. -/
lemma exists_ne_zero_summand (ρ : Idx F q) : ∃ x : Summand F q ρ, x ≠ 0 := by
  obtain ⟨v, hv⟩ := ρ.2.exists_hasEigenvector
  exact ⟨⟨v, Module.End.eigenspace_le_maxGenEigenspace hv.1⟩,
    fun h => hv.2 (congrArg Subtype.val h)⟩

/-- **The purity step of `prop:susp-converse`.** Under a positive infinitesimal polarization of
weight `j` every block of `Θ` is the scalar `ρ`: `Θ - ρ` is nilpotent on `V̂_ρ` and, being
skew-adjoint up to a real scalar for a positive form, semisimple (`prop:purity`). -/
theorem thetaBlock_eq_of_infPol (hinf : IsInfPol hh (theta F q) j) (ρ : Idx F q) :
    thetaBlock F q ρ = ρ.1 • 1 := by
  set T := thetaBlock F q ρ - ρ.1 • 1
  have hP : ∀ u v, (blockForm hh ρ).toFun (T u) v + (blockForm hh ρ).toFun u (T v) =
      ((j - 2 * ρ.1.re : ℝ) : ℂ) * (blockForm hh ρ).toFun u v := by
    intro u v
    have h := hinf (DirectSum.lof ℂ _ _ ρ u) (DirectSum.lof ℂ _ _ ρ v)
    rw [theta_lof, theta_lof] at h
    change hh.toFun (DirectSum.lof ℂ _ _ ρ (T u)) (DirectSum.lof ℂ _ _ ρ v) +
      hh.toFun (DirectSum.lof ℂ _ _ ρ u) (DirectSum.lof ℂ _ _ ρ (T v)) = _
    have hT : ∀ x, DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ (T x) =
        DirectSum.lof ℂ _ _ ρ (thetaBlock F q ρ x) +
          (-ρ.1) • DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ x := fun x => by
      simp [T, sub_eq_add_neg, map_add, map_neg, map_smul]
      exact (neg_smul _ _).symm
    rw [hT, hT, hh.add_left, hh.smul_left, hh.add_right, hh.smul_right]
    change _ = _ * hh.toFun (DirectSum.lof ℂ _ _ ρ u) (DirectSum.lof ℂ _ _ ρ v)
    have h2 : (ρ.1 + conj ρ.1) = ((2 * ρ.1.re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
    rw [map_neg]
    push_cast at h2 ⊢
    linear_combination h - h2 * hh.toFun (DirectSum.lof ℂ _ _ ρ u) (DirectSum.lof ℂ _ _ ρ v)
  have hss := (blockForm hh ρ).isSemisimple T (j - 2 * ρ.1.re) hP
  have hnil : IsNilpotent T := isNilpotent_thetaBlock F q ρ
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss)

/-- Under a positive infinitesimal polarization of weight `j`, every `ρ` in the index set has
`Re ρ = j/2`: `Θ = ρ` on the nonzero summand `V̂_ρ`, so `(ρ + ρ̄) ĥ(x, x) = j ĥ(x, x)`. -/
theorem re_eq_of_infPol (hinf : IsInfPol hh (theta F q) j) (ρ : Idx F q) : ρ.1.re = j / 2 := by
  obtain ⟨x, hx⟩ := exists_ne_zero_summand ρ
  set a := DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ x
  have ha : a ≠ 0 := fun h0 => hx (lof_injective ρ (h0.trans (map_zero _).symm))
  have h := hinf a a
  have hθ : theta F q a = ρ.1 • a := by
    rw [theta_lof, thetaBlock_eq_of_infPol hinf ρ, LinearMap.smul_apply, Module.End.one_apply,
      map_smul]
  rw [hθ, hh.smul_left, hh.smul_right, ← add_mul, Complex.add_conj] at h
  have hpos := hh.re_pos a ha
  have hne : hh.toFun a a ≠ 0 := fun h0 => by rw [h0] at hpos; simp at hpos
  have h' := congrArg Complex.re (mul_right_cancel₀ hne h)
  simp at h'
  linarith

/-- `N_α = 0` forces `F = α` on `V_{(α)}`, by `eq_zero_of_logSeries_eq_zero`. -/
theorem restrictF_eq_of_logNil {α : ℂ} (hα : α ≠ 0) (h : logNil F α = 0) :
    restrictF F α = α • 1 := by
  by_cases h0 : finrank ℂ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.1 h0
    ext x
    exact Subsingleton.elim _ _
  have hU := eq_zero_of_logSeries_eq_zero (isNilpotent_unip F hα) (n := finrank ℂ V)
    (by omega) h
  rw [sub_eq_zero] at hU
  rw [← one_smul ℂ (restrictF F α), ← mul_inv_cancel₀ hα, ← smul_smul, hU]

/-- **`prop:susp-converse`.** Let `q > 1` and `j` be real, `F` an endomorphism of a
finite-dimensional complex space `V`, `(V̂, Θ)` its logarithmic suspension and `ĥ` a positive
infinitesimal polarization of weight `j` on `(V̂, Θ)`. For every choice `(ρ_α)`, `ρ_α ∈ Σ_q(α)`
(a sheet `σ`), the restricted form `h` of `ĥ` (`def:log-susp` (b)) is a positive Frobenius
polarization of weight `j` on `(V, F)`. (The existence of `σ` forces `F` to be invertible.) -/
theorem isFrobPol_restrictedForm (hq : 1 < q) (hinf : IsInfPol hh (theta F q) j)
    {σ : Eig F → ℂ} (hσ : IsSheet F q σ) : IsFrobPol (restrictedForm hh hσ) F q j := by
  have hF : ∀ β, ∀ x ∈ F.maxGenEigenspace β, F x = β • x := by
    intro β x hx
    by_cases hβ : F.HasEigenvalue β
    · set ρ := sheetIdx hσ ⟨β, hβ⟩
      have hqρ : qpow q ρ.1 = β := hσ ⟨β, hβ⟩
      have hlog : logNil F (qpow q ρ.1) = 0 := by
        have h1 := thetaBlock_eq_of_infPol hinf ρ
        rw [thetaBlock, add_eq_left] at h1
        exact (smul_eq_zero.1 h1).resolve_left
          (inv_ne_zero (Complex.ofReal_ne_zero.2 (Real.log_pos hq).ne'))
      have hR := restrictF_eq_of_logNil (qpow_ne_zero q ρ.1) hlog
      rw [hqρ] at hR
      have := congrArg Subtype.val (LinearMap.congr_fun hR ⟨x, hx⟩)
      simp only [restrictF, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_smul] at this
      exact this
    · rw [maxGenEigenspace_eq_bot hβ, Submodule.mem_bot] at hx
      simp [hx]
  intro u v
  change ∑ α : Eig F, hh.toFun (sheetCopy hσ α (F u)) (sheetCopy hσ α (F v)) =
    _ * ∑ α : Eig F, hh.toFun (sheetCopy hσ α u) (sheetCopy hσ α v)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hc : ∀ w, sheetCopy hσ α (F w) = α.1 • sheetCopy hσ α w := by
    intro w
    have h' : genProj F α.1 (F w) = α.1 • genProj F α.1 w :=
      Subtype.ext (by rw [genProj_apply_of_smul hF α.1 w]; rfl)
    simp only [sheetCopy, LinearMap.comp_apply, h', map_smul]
  rw [hc, hc, hh.smul_left, hh.smul_right, ← mul_assoc, Complex.mul_conj]
  congr 2
  have hre : (σ α).re = j / 2 := re_eq_of_infPol hinf (sheetIdx hσ α)
  rw [Complex.normSq_eq_norm_sq, ← hσ α, norm_qpow (by linarith), ← Real.rpow_natCast,
    ← Real.rpow_mul (by linarith), hre]
  norm_num

end Converse

end WeilRH.Suspension
