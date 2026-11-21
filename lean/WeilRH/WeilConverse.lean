/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Hermitian

/-!
# The converse of the Weil–Serre lemma (`prop:weil-converse`)

Source: `latex/notes.tex`, `def:frob-pol`, `prop:weil-linear`, `prop:weil-converse`.

A *positive Frobenius polarization of weight `j`* on `(V, F)` (`def:frob-pol`) is a positive
definite Hermitian form `h` on `V` with `h(Fu, Fv) = q^j h(u, v)`. Positive definite Hermitian forms
are `WeilRH.PosHermForm` (linear in the first argument), and the polarization identity is
`WeilRH.IsFrobPol`. "Diagonalizable" is encoded as `⨆ α, F.eigenspace α = ⊤`.

## Main results

* `WeilRH.exists_frobPol_iff` (**`prop:weil-converse` (i)**): `(V, F)` admits a positive Frobenius
  polarization of weight `j` iff `F` is diagonalizable with all eigenvalues of modulus `q^{j/2}`.
* `WeilRH.isFrobPol_iff_orthogonal` (**`prop:weil-converse` (ii)**): in that case a positive
  definite Hermitian form is a positive Frobenius polarization iff distinct eigenspaces of `F` are
  `h`-orthogonal, i.e. iff `h` is the orthogonal sum of its restrictions to the eigenspaces.
* `WeilRH.isFrobPol_iff_exists_assemble` (**`prop:weil-converse` (ii)**, as stated): the
  polarizations are exactly the orthogonal sums `WeilRH.assemble hdiag (h_α)` = `⊕_α h_α` of
  arbitrary positive definite Hermitian forms `h_α` on the eigenspaces; `WeilRH.restrict_assemble`
  recovers `h_α`, and `WeilRH.isFrobPol_assemble` is the direction used in the proof of (i).
-/

open scoped ComplexConjugate DirectSum

namespace WeilRH

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The polarization identity of `def:frob-pol`: `h(Fu, Fv) = q^j h(u, v)`. -/
def IsFrobPol (h : PosHermForm V) (F : Module.End ℂ V) (q j : ℝ) : Prop :=
  ∀ u v, h.toFun (F u) (F v) = ((q ^ j : ℝ) : ℂ) * h.toFun u v

/-- A polarization makes distinct eigenspaces orthogonal (part of `prop:weil-linear`). -/
theorem IsFrobPol.eq_zero_of_ne {h : PosHermForm V} {F : Module.End ℂ V} {q j : ℝ} (hq : 0 < q)
    (hF : IsFrobPol h F q j) {α β : ℂ} (hαβ : α ≠ β) {u v : V} (hu : u ∈ F.eigenspace α)
    (hv : v ∈ F.eigenspace β) : h.toFun u v = 0 := by
  by_cases hv0 : v = 0
  · rw [hv0, h.zero_right]
  have hβ : F.HasEigenvalue β := Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩
  have hnβ := h.norm_eq_rpow F q j hq hF hβ
  have key := hF u v
  rw [Module.End.mem_eigenspace_iff.1 hu, Module.End.mem_eigenspace_iff.1 hv, h.smul_left,
    h.smul_right] at key
  have hβsq : ((q ^ j : ℝ) : ℂ) = β * conj β := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnβ, ← Real.rpow_natCast,
      ← Real.rpow_mul hq.le]
    norm_num
  rw [hβsq] at key
  have hβ0 : conj β ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    rw [h0, norm_zero] at hnβ
    exact (Real.rpow_pos_of_pos hq _).ne' hnβ.symm
  have : (α - β) * conj β * h.toFun u v = 0 := by linear_combination key
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd (sub_eq_zero.1 h2) hαβ
    · exact absurd h2 hβ0
  · exact h1

/-- **`prop:weil-converse` (ii).** If every eigenvalue of `F` has modulus `q^{j/2}` and `F` is
diagonalizable, a positive definite Hermitian form `h` is a positive Frobenius polarization of
weight `j` iff distinct eigenspaces of `F` are `h`-orthogonal; that is, the polarizations are
exactly the orthogonal sums of positive definite Hermitian forms on the eigenspaces. -/
theorem isFrobPol_iff_orthogonal (h : PosHermForm V) (F : Module.End ℂ V) {q : ℝ} (hq : 0 < q)
    (j : ℝ) (hdiag : ⨆ α, F.eigenspace α = ⊤)
    (hnorm : ∀ α, F.HasEigenvalue α → ‖α‖ = q ^ (j / 2)) :
    IsFrobPol h F q j ↔ ∀ α β, α ≠ β → ∀ u ∈ F.eigenspace α, ∀ v ∈ F.eigenspace β,
      h.toFun u v = 0 := by
  refine ⟨fun hF α β hαβ u hu v hv => hF.eq_zero_of_ne hq hαβ hu hv, fun horth => ?_⟩
  -- the identity on pairs of eigenvectors
  have hpair : ∀ α β (u : V), u ∈ F.eigenspace α → ∀ v ∈ F.eigenspace β,
      h.toFun (F u) (F v) = ((q ^ j : ℝ) : ℂ) * h.toFun u v := by
    intro α β u hu v hv
    rw [Module.End.mem_eigenspace_iff.1 hu, Module.End.mem_eigenspace_iff.1 hv, h.smul_left,
      h.smul_right]
    by_cases hαβ : α = β
    · subst hαβ
      by_cases hv0 : v = 0
      · simp [hv0, h.zero_right]
      have hα : F.HasEigenvalue α := Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩
      have hsq : α * conj α = ((q ^ j : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm α hα, ← Real.rpow_natCast,
          ← Real.rpow_mul hq.le]
        norm_num
      rw [← mul_assoc, hsq]
    · rw [horth α β hαβ u hu v hv]; ring
  intro u v
  have hu : u ∈ ⨆ α, F.eigenspace α := hdiag ▸ Submodule.mem_top
  have hv : v ∈ ⨆ α, F.eigenspace α := hdiag ▸ Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem α u hu =>
    induction hv using Submodule.iSup_induction' with
    | mem β v hv => exact hpair α β u hu v hv
    | zero => simp [h.zero_right]
    | add v v' _ _ ih ih' => rw [map_add, h.add_right, h.add_right, ih, ih', mul_add]
  | zero => simp [h.zero_left]
  | add u u' _ _ ih ih' => rw [map_add, h.add_left, h.add_left, ih, ih', mul_add]

/-- The standard form attached to a finite basis: `h(u, v) = Σ_i u_i conj(v_i)`. -/
noncomputable def basisForm {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ V) : PosHermForm V where
  toFun u v := ∑ i, b.repr u i * conj (b.repr v i)
  add_left u u' v := by simp [add_mul, Finset.sum_add_distrib]
  smul_left c u v := by simp [Finset.mul_sum, mul_assoc]
  conj_symm u v := by simp [map_sum, mul_comm]
  re_pos u hu := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr u i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (b.ext_elem fun i => by simp [hcon i])
    simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

/-- **`prop:weil-converse` (i).** `(V, F)` admits a positive Frobenius polarization of weight `j`
iff `F` is diagonalizable and every eigenvalue has modulus `q^{j/2}`. -/
theorem exists_frobPol_iff [FiniteDimensional ℂ V] (F : Module.End ℂ V) {q : ℝ} (hq : 1 < q)
    (j : ℝ) :
    (∃ h : PosHermForm V, IsFrobPol h F q j) ↔
      (⨆ α, F.eigenspace α = ⊤) ∧ ∀ α, F.HasEigenvalue α → ‖α‖ = q ^ (j / 2) := by
  have hq0 : 0 < q := by linarith
  constructor
  · rintro ⟨h, hF⟩
    refine ⟨?_, fun α hα => h.norm_eq_rpow F q j hq0 hF hα⟩
    have hss := (h.isSemisimple_of_weil F q j hq0 hF).isFinitelySemisimple
    rw [← Module.End.iSup_maxGenEigenspace_eq_top F]
    exact iSup_congr fun α => (hss.maxGenEigenspace_eq_eigenspace α).symm
  · rintro ⟨hdiag, hnorm⟩
    have hint : DirectSum.IsInternal fun α => F.eigenspace α :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
        ⟨Module.End.eigenspaces_iSupIndep F, hdiag⟩
    let b := hint.collectedBasis fun α => Module.finBasis ℂ (F.eigenspace α)
    have : Finite _ := Module.Finite.finite_basis b
    let _ := Fintype.ofFinite (Σ α, Fin (Module.finrank ℂ (F.eigenspace α)))
    refine ⟨basisForm b, ?_⟩
    refine (isFrobPol_iff_orthogonal _ F hq0 j hdiag hnorm).2 ?_
    intro α β hαβ u hu v hv
    -- coordinates of `u` are supported on the `α`-block, those of `v` on the `β`-block
    have hsupp : ∀ (γ : ℂ) (w : V), w ∈ F.eigenspace γ → ∀ i : Σ α, Fin _, i.1 ≠ γ →
        b.repr w i = 0 := by
      intro γ w hw i hi
      obtain ⟨w', rfl⟩ : ∃ w' : F.eigenspace γ, (w' : V) = w := ⟨⟨w, hw⟩, rfl⟩
      rw [← (Module.finBasis ℂ (F.eigenspace γ)).sum_repr w']
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finsupp.coe_finsetSum,
        Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : (Module.finBasis ℂ (F.eigenspace γ) k : V) = b ⟨γ, k⟩ :=
        (congrFun (hint.collectedBasis_coe fun α => Module.finBasis ℂ (F.eigenspace α))
          ⟨γ, k⟩).symm
      rw [hk, b.repr_self, Finsupp.single_eq_of_ne (fun he => hi (congrArg Sigma.fst he)),
        mul_zero]
    show ∑ i, b.repr u i * conj (b.repr v i) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i.1 = α
    · rw [hsupp β v hv i (hi ▸ hαβ), map_zero, mul_zero]
    · rw [hsupp α u hu i hi, zero_mul]

/-- Two positive definite Hermitian forms with the same values are equal. -/
theorem PosHermForm.ext {h h' : PosHermForm V} (H : h.toFun = h'.toFun) : h = h' := by
  cases h; cases h'; cases H; rfl

/-- The restriction of a positive definite Hermitian form to a submodule. -/
def PosHermForm.restrict (h : PosHermForm V) (W : Submodule ℂ V) : PosHermForm W where
  toFun u v := h.toFun u v
  add_left u u' v := h.add_left u u' v
  smul_left c u v := h.smul_left c u v
  conj_symm u v := h.conj_symm u v
  re_pos u hu := h.re_pos u fun h0 => hu (Subtype.ext h0)

/-- Additivity over finite sums in the first argument. -/
theorem PosHermForm.sum_left (h : PosHermForm V) {ι : Type*} (s : Finset ι) (x : ι → V) (v : V) :
    h.toFun (∑ i ∈ s, x i) v = ∑ i ∈ s, h.toFun (x i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add_left, ih]

/-- Additivity over finite sums in the second argument. -/
theorem PosHermForm.sum_right (h : PosHermForm V) {ι : Type*} (s : Finset ι) (u : V) (x : ι → V) :
    h.toFun u (∑ i ∈ s, x i) = ∑ i ∈ s, h.toFun u (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add_right, ih]

section Assemble

variable (F : Module.End ℂ V)

/-- A diagonalizable `F` gives the internal direct sum `V = ⊕_α V_α`. -/
theorem isInternal_eigenspace (hdiag : ⨆ α, F.eigenspace α = ⊤) : DirectSum.IsInternal fun α => F.eigenspace α :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨Module.End.eigenspaces_iSupIndep F, hdiag⟩

/-- The decomposition `V ≃ ⨁_α V_α` of a diagonalizable `F`. -/
noncomputable abbrev eigenEquiv (hdiag : ⨆ α, F.eigenspace α = ⊤) :
    (⨁ α, F.eigenspace α) ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap fun α => F.eigenspace α)
    (isInternal_eigenspace F hdiag)

/-- The projection `V → V_α` along the other eigenspaces. -/
noncomputable def eigenProj (hdiag : ⨆ α, F.eigenspace α = ⊤) (α : ℂ) : V →ₗ[ℂ] F.eigenspace α :=
  DirectSum.component ℂ ℂ (fun α => F.eigenspace α) α ∘ₗ (eigenEquiv F hdiag).symm.toLinearMap

theorem eigenProj_apply (hdiag : ⨆ α, F.eigenspace α = ⊤) (α : ℂ) (u : V) :
    eigenProj F hdiag α u = (eigenEquiv F hdiag).symm u α := rfl

variable {F} {hdiag : ⨆ α, F.eigenspace α = ⊤}

/-- `eigenProj α` is the identity on `V_α`. -/
theorem eigenProj_of_mem {α : ℂ} {u : V} (hu : u ∈ F.eigenspace α) :
    eigenProj F hdiag α u = ⟨u, hu⟩ := by
  rw [eigenProj_apply]; exact (isInternal_eigenspace F hdiag).ofBijective_coeLinearMap_of_mem hu

/-- `eigenProj β` kills `V_α` for `α ≠ β`. -/
theorem eigenProj_of_mem_ne {α β : ℂ} (hαβ : α ≠ β) {u : V} (hu : u ∈ F.eigenspace α) :
    eigenProj F hdiag β u = 0 := by
  rw [eigenProj_apply]; exact (isInternal_eigenspace F hdiag).ofBijective_coeLinearMap_of_mem_ne hαβ hu

/-- `eigenProj α = 0` when `α` is not an eigenvalue. -/
theorem eigenProj_eq_zero_of_not {α : ℂ} (hα : ¬ F.HasEigenvalue α) (u : V) :
    eigenProj F hdiag α u = 0 := by
  have : F.eigenspace α = ⊥ := not_not.1 hα
  exact Subtype.ext ((Submodule.mem_bot ℂ).1 (this ▸ (eigenProj F hdiag α u).2))

variable [FiniteDimensional ℂ V]

variable (F) in
/-- The (finite) set of eigenvalues of `F`. -/
noncomputable def eigenFinset : Finset ℂ := (Module.End.finite_hasEigenvalue F).toFinset

/-- `u = Σ_α u_α`. -/
theorem sum_eigenProj (u : V) : ∑ α ∈ eigenFinset F, (eigenProj F hdiag α u : V) = u := by
  classical
  have hu : DirectSum.coeLinearMap (fun α => F.eigenspace α) ((eigenEquiv F hdiag).symm u) = u :=
    (eigenEquiv F hdiag).apply_symm_apply u
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum] at hu
  conv_rhs => rw [← hu]
  simp only [eigenProj_apply]
  have hsub : ((eigenEquiv F hdiag).symm u).support ⊆ eigenFinset F := by
    intro α hα
    rw [eigenFinset, Set.Finite.mem_toFinset]
    by_contra hne
    exact (DFinsupp.mem_support_iff.1 hα) (eigenProj_eq_zero_of_not (hdiag := hdiag) hne u)
  refine (Finset.sum_subset hsub fun α _ hα => ?_).symm
  rw [DFinsupp.notMem_support_iff.1 hα, ZeroMemClass.coe_zero]

variable (hdiag) in
/-- **The orthogonal sum `⊕_α h_α`** of forms `h_α` on the eigenspaces `V_α` of a diagonalizable
`F` (`prop:weil-converse` (ii)): `h(u, v) = Σ_α h_α(u_α, v_α)`. -/
noncomputable def assemble (hα : ∀ α, PosHermForm (F.eigenspace α)) : PosHermForm V where
  toFun u v := ∑ α ∈ eigenFinset F, (hα α).toFun (eigenProj F hdiag α u) (eigenProj F hdiag α v)
  add_left u u' v := by simp [(hα _).add_left, Finset.sum_add_distrib]
  smul_left c u v := by simp [(hα _).smul_left, Finset.mul_sum]
  conj_symm u v := by simp [map_sum, (hα _).conj_symm]
  re_pos u hu := by
    obtain ⟨α, hα0⟩ : ∃ α ∈ eigenFinset F, eigenProj F hdiag α u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hu
      rw [← sum_eigenProj (hdiag := hdiag) u]
      exact Finset.sum_eq_zero fun α hα => by rw [hcon α hα, ZeroMemClass.coe_zero]
    rw [Complex.re_sum]
    refine Finset.sum_pos' (fun β _ => ?_) ⟨α, hα0.1, (hα α).re_pos _ hα0.2⟩
    by_cases hβ : eigenProj F hdiag β u = 0
    · rw [hβ, (hα β).zero_left]; simp
    · exact ((hα β).re_pos _ hβ).le

variable {hα : ∀ α, PosHermForm (F.eigenspace α)}

/-- On `V_α × V_α`, `⊕_β h_β` is `h_α`. -/
theorem assemble_apply_of_mem {α : ℂ} {u v : V} (hu : u ∈ F.eigenspace α)
    (hv : v ∈ F.eigenspace α) : (assemble hdiag hα).toFun u v = (hα α).toFun ⟨u, hu⟩ ⟨v, hv⟩ := by
  show ∑ β ∈ eigenFinset F, _ = _
  by_cases hs : α ∈ eigenFinset F
  · rw [Finset.sum_eq_single α (fun β _ hβ => by
      rw [eigenProj_of_mem_ne (Ne.symm hβ) hu, (hα β).zero_left]) (fun h => absurd hs h),
      eigenProj_of_mem hu, eigenProj_of_mem hv]
  · have hα0 : F.eigenspace α = ⊥ := by
      rw [eigenFinset, Set.Finite.mem_toFinset] at hs; exact not_not.1 hs
    have hu0 : (⟨u, hu⟩ : F.eigenspace α) = 0 :=
      Subtype.ext ((Submodule.mem_bot ℂ).1 (hα0 ▸ hu))
    rw [hu0, (hα α).zero_left]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [eigenProj_of_mem_ne (fun h : α = β => hs (h ▸ hβ)) hu, (hα β).zero_left]

/-- Distinct eigenspaces are `⊕_β h_β`-orthogonal. -/
theorem assemble_eq_zero_of_ne {α β : ℂ} (hαβ : α ≠ β) {u v : V} (hu : u ∈ F.eigenspace α)
    (hv : v ∈ F.eigenspace β) : (assemble hdiag hα).toFun u v = 0 := by
  refine Finset.sum_eq_zero fun γ _ => ?_
  by_cases hγ : γ = α
  · subst hγ; rw [eigenProj_of_mem_ne (Ne.symm hαβ) hv, (hα γ).zero_right]
  · rw [eigenProj_of_mem_ne (Ne.symm hγ) hu, (hα γ).zero_left]

/-- The orthogonal sum `⊕_α h_α` restricts to `h_α` on `V_α`. -/
theorem restrict_assemble (α : ℂ) : (assemble hdiag hα).restrict (F.eigenspace α) = hα α :=
  PosHermForm.ext <| funext fun u => funext fun v => assemble_apply_of_mem u.2 v.2

variable (hdiag) in
/-- A form with pairwise orthogonal eigenspaces is the orthogonal sum of its restrictions. -/
theorem eq_assemble_restrict (h : PosHermForm V)
    (horth : ∀ α β, α ≠ β → ∀ u ∈ F.eigenspace α, ∀ v ∈ F.eigenspace β, h.toFun u v = 0) :
    h = assemble hdiag fun α => h.restrict (F.eigenspace α) := by
  refine PosHermForm.ext (funext fun u => funext fun v => ?_)
  show h.toFun u v = ∑ α ∈ eigenFinset F, h.toFun (eigenProj F hdiag α u) (eigenProj F hdiag α v)
  conv_lhs => rw [← sum_eigenProj (hdiag := hdiag) u, ← sum_eigenProj (hdiag := hdiag) v]
  rw [h.sum_left]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [h.sum_right, Finset.sum_eq_single α (fun β _ hβ => horth α β (Ne.symm hβ) _
    (eigenProj F hdiag α u).2 _ (eigenProj F hdiag β v).2) (fun h => absurd hα h)]

variable (hdiag) in
/-- **`prop:weil-converse` (ii), full form.** If `F` is diagonalizable and every eigenvalue has
modulus `q^{j/2}`, the positive Frobenius polarizations of weight `j` are exactly the orthogonal
sums `⊕_α h_α` of arbitrary positive definite Hermitian forms `h_α` on the eigenspaces `V_α`
(and `h_α` is recovered as the restriction, `restrict_assemble`). -/
theorem isFrobPol_iff_exists_assemble (h : PosHermForm V) {q : ℝ} (hq : 0 < q) (j : ℝ)
    (hnorm : ∀ α, F.HasEigenvalue α → ‖α‖ = q ^ (j / 2)) :
    IsFrobPol h F q j ↔ ∃ hα : ∀ α, PosHermForm (F.eigenspace α), h = assemble hdiag hα := by
  rw [isFrobPol_iff_orthogonal h F hq j hdiag hnorm]
  refine ⟨fun horth => ⟨_, eq_assemble_restrict hdiag h horth⟩, ?_⟩
  rintro ⟨hα, rfl⟩
  exact fun α β hαβ u hu v hv => assemble_eq_zero_of_ne hαβ hu hv

variable (hdiag) in
/-- Every orthogonal sum `⊕_α h_α` is a positive Frobenius polarization (`prop:weil-converse`,
proof of (i) and (ii)). -/
theorem isFrobPol_assemble (hα : ∀ α, PosHermForm (F.eigenspace α)) {q : ℝ} (hq : 0 < q) (j : ℝ)
    (hnorm : ∀ α, F.HasEigenvalue α → ‖α‖ = q ^ (j / 2)) : IsFrobPol (assemble hdiag hα) F q j :=
  (isFrobPol_iff_exists_assemble hdiag _ hq j hnorm).2 ⟨hα, rfl⟩

end Assemble

end WeilRH
