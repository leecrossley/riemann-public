/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.SuspConverse
import WeilRH.MultiplicativeForm

/-!
# Statements about the suspension `V̂` itself (`notes.tex`, obligation 7)

Round 5 stated `prop:aw4-EF` (ii) and `prop:ff-phantom` (ii) without the logarithmic suspension as
an object: `θ_σ` was shown to act by `σ(α)` on `ker(F − α)`, and the phantom spectrum was the union
of the progressions `Σ_q(α)`. Here they are restated on `Suspension.theta`.

## Main results

* `WeilRH.AW4EFDatum.theta_sheetMap` (`prop:aw4-EF` (ii)): `Θ ι_σ = ι_σ θ_σ` for the sheet map
  `ι_σ : V → V̂` (`Suspension.sheetMap`); with `AW4EFDatum.star_sheetElem` (`θ_σ^† = j − θ_σ`) this
  is all of (ii).
* `WeilRH.AW4EFDatum.exists_aw4EAdd_suspension` (`prop:aw4-EF` (iii)): every vector of `V̂` lies in
  a finite-dimensional `Θ`-stable `V̂' = ⨁_m V̂_{σ_m}` on which `Θ|V̂'` satisfies the additive
  algebra form AW4-E of weight `j`; built from `Suspension.sheetSum` (injective for distinct
  sheets, `sheetSum_injective`) and the round 5 truncation `AW4EFDatum.truncation`.
* `WeilRH.Suspension.sheetMap_injective`, `range_sheetMap`, `sheetEquiv` (`def:aw4-EF` (c) and the
  remark after (d)): `ι_σ` is an isomorphism of `V` onto the sheet space
  `V̂_σ = ⨁_α V̂_{σ(α)}` (`sheetSpace`).
* `WeilRH.Suspension.isInternal_sheetSpace` (remark after `def:aw4-EF` (d)): for `q > 1`,
  `V̂ = ⨁_{m ∈ ℤ} V̂_{σ + 2πim/log q}` as an internal direct sum; `existsUnique_shift` is the step
  "every `ρ` with `q^ρ = α` equals `σ(α) + 2πim/log q` for exactly one `m`".
* `WeilRH.Suspension.spec_theta_phantom` (`prop:ff-phantom` (ii)): the suspension of
  `(ℂ^{S_N}, diag(S_N))` has spectrum `C_{N log q}`.
-/

open Module
open scoped DirectSum

universe u

namespace WeilRH.Suspension

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q : ℝ}

/-- If `T` acts by `c β` on every `V_{(β)}`, the projections intertwine `T` with `c α`. -/
theorem genProj_apply_of_act (T : Module.End ℂ V) (c : ℂ → ℂ)
    (hT : ∀ β, ∀ x ∈ F.maxGenEigenspace β, T x = c β • x) (α : ℂ) (u : V) :
    (genProj F α (T u) : V) = c α • (genProj F α u : V) := by
  classical
  conv_lhs => rw [← sum_genProj (F := F) u]
  rw [map_sum, map_sum, Submodule.coe_sum]
  simp_rw [hT _ _ (genProj F _ u).2, map_smul, Submodule.coe_smul]
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

/-- The sheet map `ι_σ : V → V̂`, `u ↦ Σ_α (u_α in the summand V̂_{σ α})` (`def:aw4-EF` (b)). -/
noncomputable def sheetMap {σ : Eig F → ℂ} (hσ : IsSheet F q σ) : V →ₗ[ℂ] SuspSpace F q :=
  ∑ α : Eig F, sheetCopy hσ α

omit [FiniteDimensional ℂ V] in
/-- A sheet in the sense of `MultiplicativeForm.lean` (`σ α ∈ Σ_q(α)` on eigenvalues) gives a
sheet `Eig F → ℂ` here. -/
lemma isSheet_of {σ : ℂ → ℂ} (hσ : WeilRH.IsSheet F q σ) : IsSheet F q (fun α : Eig F => σ α.1) :=
  fun α => by
    have := hσ α.1 α.2
    simp only [WeilRH.progression, Set.mem_ofPred_eq] at this
    rw [qpow, mul_comm]; exact this

/-- If `F` is semisimple, `Θ = ρ` on every summand `V̂_ρ`. -/
lemma thetaBlock_eq_of_semisimple (hF : F.IsSemisimple) (ρ : Idx F q) :
    thetaBlock F q ρ = ρ.1 • 1 := by
  have hss := (Module.End.isFinitelySemisimple_iff_isSemisimple.2 hF).maxGenEigenspace_eq_eigenspace
  rw [thetaBlock, logNil_eq_zero (F := F) (qpow_ne_zero q _) (restrictF_eq_smul (F := F) (hss _)),
    smul_zero, add_zero]

lemma theta_lof_of_semisimple (hF : F.IsSemisimple) (ρ : Idx F q) (x : Summand F q ρ) :
    theta F q (DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ x) =
      ρ.1 • DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ x := by
  rw [theta_lof, thetaBlock_eq_of_semisimple hF, LinearMap.smul_apply, Module.End.one_apply,
    map_smul]

lemma theta_sheetCopy (hF : F.IsSemisimple) {σ : Eig F → ℂ} (hσ : IsSheet F q σ) (α : Eig F)
    (u : V) : theta F q (sheetCopy hσ α u) = σ α • sheetCopy hσ α u := by
  simp only [sheetCopy, LinearMap.comp_apply]
  exact theta_lof_of_semisimple hF (sheetIdx hσ α) _

/-- The diagonal operator `diag(S_N)` on `ℂ^{S_N}`. -/
noncomputable def phantomF (q : ℝ) (N : ℕ) : Module.End ℂ (phantomSet q N → ℂ) :=
  Matrix.toLin' (Matrix.diagonal fun α => (α : ℂ))

/-- **`prop:ff-phantom` (ii), on `V̂`.** The logarithmic suspension `(V̂, Θ)` of
`(ℂ^{S_N}, diag(S_N))` has spectrum `C_{N log q}`. -/
theorem spec_theta_phantom {q : ℝ} (hq : 1 < q) {N : ℕ} (hN : 2 ≤ N) :
    Spectral.spec (theta (phantomF q N) q) = halfCoset (N * Real.log q) := by
  rw [spec_theta, ← spectrum_suspension_phantom hq hN]
  ext ρ
  simp only [Set.mem_ofPred_eq, phantomF, progression]
  rw [_root_.hasEigenvalue_toLin'_diagonal_iff, qpow, mul_comm (ρ : ℂ)]
  constructor
  · rintro ⟨α, hα⟩; exact ⟨α, α.2, hα.symm⟩
  · rintro ⟨α, hα, h⟩; exact ⟨⟨α, hα⟩, h.symm⟩

end WeilRH.Suspension

namespace WeilRH.AW4EFDatum

open WeilRH.Suspension

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q : ℝ}

variable {j : ℝ} (D : AW4EFDatum V F q j)

/-- **`prop:aw4-EF` (ii), on `V̂`.** For every sheet `σ`, `θ_σ = p_σ(F) ∈ A` satisfies
`Θ ι_σ = ι_σ θ_σ`, where `ι_σ : V → V̂` is the sheet map and `Θ` the logarithmic suspension
(`def:log-susp`). The relation `θ_σ^† = j - θ_σ` is `AW4EFDatum.star_sheetElem`. -/
theorem theta_sheetMap (hq : 0 < q) {σ : ℂ → ℂ} (hσ : WeilRH.IsSheet F q σ) (u : V) :
    WeilRH.Suspension.theta F q (sheetMap (isSheet_of hσ) u) =
      sheetMap (isSheet_of hσ) (D.ι (D.sheetElem σ) u) := by
  have hF := D.isSemisimple hq
  have hss := (Module.End.isFinitelySemisimple_iff_isSemisimple.2 hF).maxGenEigenspace_eq_eigenspace
  have hT : ∀ β, ∀ x ∈ F.maxGenEigenspace β, D.ι (D.sheetElem σ) x = σ β • x := fun β x hx =>
    D.ι_sheetElem_apply σ (Module.End.mem_eigenspace_iff.1 (hss β ▸ hx))
  simp only [sheetMap, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [theta_sheetCopy hF]
  have : genProj F α.1 (D.ι (D.sheetElem σ) u) = σ α.1 • genProj F α.1 u :=
    Subtype.ext (by rw [genProj_apply_of_act _ σ hT]; rfl)
  simp only [sheetCopy, LinearMap.comp_apply, this, map_smul]

end WeilRH.AW4EFDatum

/-! ### `prop:aw4-EF` (iii) on `V̂`: finite sums of sheet spaces -/

namespace WeilRH.Suspension

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q : ℝ}

/-- The eigenvalue `q^ρ` of `F` indexing the summand `V̂_ρ`. -/
noncomputable def eigOf (ρ : Idx F q) : Eig F := ⟨qpow q ρ.1, ρ.2⟩

lemma sheetCopy_apply {σ : Eig F → ℂ} (hσ : IsSheet F q σ) (α : Eig F) (u : V) (ρ : Idx F q) :
    ((sheetCopy hσ α u) ρ : V) = if sheetIdx hσ α = ρ then (genProj F α.1 u : V) else 0 := by
  split_ifs with h
  · subst h; exact sheetCopy_apply_self hσ α u
  · rw [sheetCopy, LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ZeroMemClass.coe_zero]

omit [FiniteDimensional ℂ V] in
lemma sheetIdx_eq_iff {σ : Eig F → ℂ} (hσ : IsSheet F q σ) (α : Eig F) (ρ : Idx F q) :
    sheetIdx hσ α = ρ ↔ α = eigOf ρ ∧ σ (eigOf ρ) = ρ.1 := by
  constructor
  · rintro rfl
    have : eigOf (sheetIdx hσ α) = α := Subtype.ext (hσ α)
    exact ⟨this.symm, by rw [this]; rfl⟩
  · rintro ⟨rfl, h⟩; exact Subtype.ext h

/-- The `ρ`-component of `ι_σ u`: `u_{q^ρ}` if `ρ = σ(q^ρ)`, else `0`. -/
lemma sheetMap_apply {σ : Eig F → ℂ} (hσ : IsSheet F q σ) (u : V) (ρ : Idx F q) :
    ((sheetMap hσ u) ρ : V) =
      if σ (eigOf ρ) = ρ.1 then (genProj F (qpow q ρ.1) u : V) else 0 := by
  classical
  simp only [sheetMap, LinearMap.coe_sum, Finset.sum_apply]
  rw [DFinsupp.finsetSum_apply, Submodule.coe_sum]
  simp_rw [sheetCopy_apply, sheetIdx_eq_iff]
  rw [Finset.sum_eq_single (eigOf ρ) (fun β _ hβ => by simp [hβ]) (by simp)]
  simp only [true_and]; congr

/-- The sheet map `ι_σ : V → V̂` is injective (`def:aw4-EF`, remark after (d)). -/
theorem sheetMap_injective {σ : Eig F → ℂ} (hσ : IsSheet F q σ) :
    Function.Injective (sheetMap hσ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  rw [← sum_genProj (F := F) u]
  refine Finset.sum_eq_zero fun α _ => ?_
  have h := congrArg (fun x : SuspSpace F q => ((x (sheetIdx hσ α)) : V)) hu
  have he : eigOf (sheetIdx hσ α) = α := Subtype.ext (hσ α)
  simp_rw [sheetMap_apply, he] at h
  change (if σ α = σ α then (genProj F (qpow q (σ α)) u : V) else 0) = 0 at h
  rw [hσ α] at h
  simpa using h

section SheetSum

variable {n : ℕ} {σs : Fin n → Eig F → ℂ} (hs : ∀ i, IsSheet F q (σs i))

/-- `Fin n → V ≅ ⨁_{i<n} V̂_{σ_i} ⊂ V̂`, `w ↦ Σ_i ι_{σ_i}(w_i)`. -/
noncomputable def sheetSum : (Fin n → V) →ₗ[ℂ] SuspSpace F q :=
  ∑ i, sheetMap (hs i) ∘ₗ LinearMap.proj i

lemma sheetSum_apply (w : Fin n → V) : sheetSum hs w = ∑ i, sheetMap (hs i) (w i) := by
  simp [sheetSum]

/-- If the sheets `σ_i` are pairwise distinct at every eigenvalue, the sheet spaces are
independent and `w ↦ Σ_i ι_{σ_i}(w_i)` is injective. -/
theorem sheetSum_injective (hinj : ∀ α i k, σs i α = σs k α → i = k) :
    Function.Injective (sheetSum hs) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext i
  rw [← sum_genProj (F := F) (w i)]
  refine Finset.sum_eq_zero fun α _ => ?_
  have h := congrArg (fun x : SuspSpace F q => ((x (sheetIdx (hs i) α)) : V)) hw
  have he : eigOf (sheetIdx (hs i) α) = α := Subtype.ext (hs i α)
  rw [sheetSum_apply, DFinsupp.finsetSum_apply, Submodule.coe_sum] at h
  simp_rw [sheetMap_apply, he] at h
  change (∑ k, if σs k α = σs i α then (genProj F (qpow q (σs i α)) (w k) : V) else 0) = 0 at h
  rw [hs i α, Finset.sum_eq_single i
    (fun k _ hk => ite_eq_right_iff.2 fun h' => absurd (hinj α k i h') hk) (by simp)] at h
  simpa using h

/-- A summand `V̂_ρ` lies in the image as soon as some `σ_i` passes through `ρ`. -/
lemma lof_mem_range (ρ : Idx F q) {i : Fin n} (hi : σs i (eigOf ρ) = ρ.1) (y : Summand F q ρ) :
    DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ y ∈ LinearMap.range (sheetSum hs) := by
  classical
  refine ⟨Pi.single i (y : V), ?_⟩
  rw [sheetSum_apply, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero])
    (by simp), Pi.single_eq_same]
  ext ρ'
  rw [sheetMap_apply, DirectSum.lof_eq_of]
  by_cases hρ : ρ' = ρ
  · subst hρ; rw [ite_eq_left_iff.2 (fun h => absurd hi h), DirectSum.of_eq_same, genProj_of_mem y.2]
  · rw [DirectSum.of_eq_of_ne _ _ _ hρ, ZeroMemClass.coe_zero]
    split_ifs with h'
    · have hq : qpow q ρ'.1 ≠ qpow q ρ.1 := by
        intro hq
        have : eigOf ρ' = eigOf ρ := Subtype.ext hq
        exact hρ (Subtype.ext (by rw [← h', ← hi, this]))
      rw [genProj_of_mem_ne (Ne.symm hq) y.2, ZeroMemClass.coe_zero]
    · rfl

end SheetSum

/-! ### Sheet spaces and the decomposition of `V̂` -/

/-- The vectors of `V̂` vanishing at every index satisfying `P`. -/
def vanishOn (P : Idx F q → Prop) : Submodule ℂ (SuspSpace F q) where
  carrier := {x | ∀ ρ, P ρ → x ρ = 0}
  add_mem' hx hy ρ hρ := by rw [DirectSum.add_apply, hx ρ hρ, hy ρ hρ, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c x hx ρ hρ := by rw [DirectSum.smul_apply, hx ρ hρ, smul_zero]

section SheetSpace

variable {σ : Eig F → ℂ} (hσ : IsSheet F q σ)

/-- **`def:aw4-EF` (c)**: the sheet space `V̂_σ = ⨁_α V̂_{σ(α)} ⊂ V̂`. -/
noncomputable def sheetSpace : Submodule ℂ (SuspSpace F q) :=
  ⨆ α : Eig F, LinearMap.range (DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) (sheetIdx hσ α))

omit [FiniteDimensional ℂ V] in
/-- `V̂_σ` is the set of vectors supported on the indices `ρ` with `ρ = σ(q^ρ)`. -/
theorem mem_sheetSpace_iff (x : SuspSpace F q) :
    x ∈ sheetSpace hσ ↔ ∀ ρ : Idx F q, σ (eigOf ρ) ≠ ρ.1 → x ρ = 0 := by
  classical
  constructor
  · intro hx
    refine (show sheetSpace hσ ≤ vanishOn (fun ρ : Idx F q => σ (eigOf ρ) ≠ ρ.1) from
      iSup_le fun α => ?_) hx
    rintro _ ⟨y, rfl⟩ ρ hρ
    have hne : ρ ≠ sheetIdx hσ α := fun h => hρ ((sheetIdx_eq_iff hσ α ρ).1 h.symm).2
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hne]
  · intro hx
    rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun ρ hρ => ?_
    have h : σ (eigOf ρ) = ρ.1 := by
      by_contra h
      exact (DFinsupp.mem_support_iff.1 hρ) (hx ρ h)
    have he : sheetIdx hσ (eigOf ρ) = ρ := (sheetIdx_eq_iff hσ _ ρ).2 ⟨rfl, h⟩
    refine Submodule.mem_iSup_of_mem (eigOf ρ) ?_
    rw [he, ← DirectSum.lof_eq_of ℂ]
    exact ⟨x ρ, rfl⟩

/-- `ι_σ u` on a summand `V̂_ρ` through which `σ` passes is the copy of `u`. -/
lemma sheetMap_coe (ρ : Idx F q) (hρ : σ (eigOf ρ) = ρ.1) (y : Summand F q ρ) :
    sheetMap hσ (y : V) = DirectSum.lof ℂ _ (fun ρ => Summand F q ρ) ρ y := by
  classical
  ext ρ'
  rw [sheetMap_apply, DirectSum.lof_eq_of]
  by_cases hρ' : ρ' = ρ
  · subst hρ'; rw [ite_eq_left_iff.2 (fun h => absurd hρ h), DirectSum.of_eq_same, genProj_of_mem y.2]
  · rw [DirectSum.of_eq_of_ne _ _ _ hρ', ZeroMemClass.coe_zero]
    split_ifs with h'
    · have hq : qpow q ρ'.1 ≠ qpow q ρ.1 := by
        intro hq
        have : eigOf ρ' = eigOf ρ := Subtype.ext hq
        exact hρ' (Subtype.ext (by rw [← h', ← hρ, this]))
      rw [genProj_of_mem_ne (Ne.symm hq) y.2, ZeroMemClass.coe_zero]
    · rfl

/-- **`def:aw4-EF`, remark after (d)**: the sheet map lands in, and maps onto, the sheet space. -/
theorem range_sheetMap : LinearMap.range (sheetMap hσ) = sheetSpace hσ := by
  classical
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    rw [mem_sheetSpace_iff]
    intro ρ hρ
    ext
    rw [sheetMap_apply, ite_eq_right_of_eq_false _ _ (eq_false hρ)]; rfl
  · intro x hx
    rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun ρ hρ => ?_
    have h : σ (eigOf ρ) = ρ.1 := by
      by_contra h
      exact (DFinsupp.mem_support_iff.1 hρ) ((mem_sheetSpace_iff hσ x).1 hx ρ h)
    rw [← DirectSum.lof_eq_of ℂ]
    exact ⟨_, sheetMap_coe hσ ρ h (x ρ)⟩

/-- **`def:aw4-EF`, remark after (d)**: `ι_σ : V → V̂_σ` is an isomorphism. -/
noncomputable def sheetEquiv : V ≃ₗ[ℂ] sheetSpace hσ :=
  (LinearEquiv.ofInjective _ (sheetMap_injective hσ)).trans
    (LinearEquiv.ofEq _ _ (range_sheetMap hσ))

@[simp] lemma sheetEquiv_apply (u : V) : (sheetEquiv hσ u : SuspSpace F q) = sheetMap hσ u := rfl

end SheetSpace

section Decomposition

variable {σ : Eig F → ℂ}

/-- The shifted sheet `σ + 2πim/log q`. -/
noncomputable def shiftSheet (σ : Eig F → ℂ) (q : ℝ) (m : ℤ) : Eig F → ℂ :=
  fun α => σ α + 2 * Real.pi * Complex.I * m / Real.log q

omit [FiniteDimensional ℂ V] in
lemma isSheet_shiftSheet (hq : 1 < q) (hσ : IsSheet F q σ) (m : ℤ) :
    IsSheet F q (shiftSheet σ q m) := by
  intro α
  have hL : (Real.log q : ℂ) ≠ 0 := WeilRH.log_ne_zero_of_one_lt hq
  have h := hσ α
  simp only [qpow, shiftSheet] at h ⊢
  rw [mul_add, mul_div_cancel₀ _ hL, Complex.exp_add, h,
    show 2 * Real.pi * Complex.I * (m : ℂ) = m * (2 * Real.pi * Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [FiniteDimensional ℂ V] in
/-- Every index `ρ` lies on exactly one shifted sheet. -/
lemma existsUnique_shift (hq : 1 < q) (hσ : IsSheet F q σ) (ρ : Idx F q) :
    ∃! m : ℤ, shiftSheet σ q m (eigOf ρ) = ρ.1 := by
  have hL : (Real.log q : ℂ) ≠ 0 := WeilRH.log_ne_zero_of_one_lt hq
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  have h1 : qpow q ρ.1 = qpow q (σ (eigOf ρ)) := (hσ (eigOf ρ)).symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hρ : (ρ.1 : ℂ) = σ (eigOf ρ) + 2 * Real.pi * Complex.I * n / Real.log q := by
    field_simp
    linear_combination hn
  refine ⟨n, hρ.symm, fun m hm => ?_⟩
  simp only [shiftSheet] at hm
  have h2 : 2 * Real.pi * Complex.I * (m : ℂ) = 2 * Real.pi * Complex.I * (n : ℂ) := by
    rw [← div_left_inj' hL]
    linear_combination hm + hρ
  exact_mod_cast mul_left_cancel₀ hc h2

omit [FiniteDimensional ℂ V] in
/-- **`def:aw4-EF`, remark after (d)**: `V̂ = ⨁_{m ∈ ℤ} V̂_{σ + 2πim/log q}`. -/
theorem isInternal_sheetSpace (hq : 1 < q) (hσ : IsSheet F q σ) :
    DirectSum.IsInternal fun m : ℤ => sheetSpace (isSheet_shiftSheet hq hσ m) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro m
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ k, ⨆ (_ : k ≠ m), sheetSpace (isSheet_shiftSheet hq hσ k)) ≤ vanishOn (fun ρ : Idx F q => shiftSheet σ q m (eigOf ρ) = ρ.1) := by
      refine iSup₂_le fun k hk y hy ρ hρ => ?_
      refine (mem_sheetSpace_iff _ y).1 hy ρ fun hk' => hk ?_
      exact (existsUnique_shift hq hσ ρ).unique hk' hρ
    have h0 := hle hx'
    ext ρ
    by_cases hρ : shiftSheet σ q m (eigOf ρ) = ρ.1
    · rw [h0 ρ hρ]; rfl
    · rw [(mem_sheetSpace_iff _ x).1 hx ρ hρ]; rfl
  · rw [eq_top_iff]
    intro x _
    rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun ρ _ => ?_
    obtain ⟨m, hm, -⟩ := existsUnique_shift hq hσ ρ
    refine Submodule.mem_iSup_of_mem m ?_
    rw [mem_sheetSpace_iff]
    intro ρ' hρ'
    have hne : ρ' ≠ ρ := by rintro rfl; exact hρ' hm
    rw [DirectSum.of_eq_of_ne _ _ _ hne]

end Decomposition

end WeilRH.Suspension

namespace WeilRH.AW4EAddDatum

variable {W W' : Type u} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {Θ : Module.End ℂ W} {j : ℝ}

/-- Transport of the additive algebra form AW4-E along a linear isomorphism `e : W ≃ W'`:
`(W', e Θ e⁻¹)` carries the same algebra, acting by conjugation. -/
noncomputable def congr (T : AW4EAddDatum W Θ j) (e : W ≃ₗ[ℂ] W') :
    AW4EAddDatum W' (e.conjAlgEquiv ℂ Θ) j where
  A := T.A
  P := T.P
  ι := (e.conjAlgEquiv ℂ).toAlgHom.comp T.ι
  ι_injective := (e.conjAlgEquiv ℂ).injective.comp T.ι_injective
  θ := T.θ
  ι_θ := by simp [T.ι_θ]
  add_star := T.add_star

/-- AW4-E transported to the image of an injective map intertwining `Θ` with `Θ''`. -/
theorem nonempty_range {W'' : Type u} [AddCommGroup W''] [Module ℂ W'']
    (T : AW4EAddDatum W Θ j) (J : W →ₗ[ℂ] W'') (hJ : Function.Injective J)
    (Θ'' : Module.End ℂ W'') (hΘ : ∀ w, Θ'' (J w) = J (Θ w))
    (hW : ∀ y ∈ LinearMap.range J, Θ'' y ∈ LinearMap.range J) :
    Nonempty (AW4EAddDatum (LinearMap.range J) (Θ''.restrict hW) j) := by
  set E := LinearEquiv.ofInjective J hJ
  have hE : E.conjAlgEquiv ℂ Θ = Θ''.restrict hW := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨w, rfl⟩ := E.surjective y
    apply Subtype.ext
    rw [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.coe_restrict_apply, LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply,
      hΘ]
  rw [← hE]
  exact ⟨T.congr E⟩

end WeilRH.AW4EAddDatum

namespace WeilRH.AW4EFDatum

open WeilRH.Suspension

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {F : Module.End ℂ V} {q : ℝ} {j : ℝ} (D : AW4EFDatum V F q j)

/-- `Θ` restricted to `⨁_{i<n} V̂_{σ_i}` is the truncation operator `Θ'` of `prop:aw4-EF` (iii):
`Θ (Σ_i ι_{σ_i} w_i) = Σ_i ι_{σ_i} (θ_{σ_i} w_i)`. -/
theorem theta_sheetSum (hq : 0 < q) {n : ℕ} (σ : Fin n → ℂ → ℂ) (hσ : ∀ i, WeilRH.IsSheet F q (σ i))
    (w : Fin n → V) :
    theta F q (sheetSum (fun i => isSheet_of (hσ i)) w) =
      sheetSum (fun i => isSheet_of (hσ i)) (D.truncTheta σ w) := by
  rw [sheetSum_apply, sheetSum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => D.theta_sheetMap hq (hσ i) (w i)

include D in
/-- **`prop:aw4-EF` (iii), on `V̂`.** Under AW4-E_F of weight `j`, every vector of the logarithmic
suspension `V̂` lies in a finite-dimensional `Θ`-stable subspace `V̂'` such that `(V̂', Θ|V̂')`
satisfies the additive algebra form AW4-E of weight `j`: a finite-dimensional complex `*`-algebra
`A'` with a positive trace involution acts faithfully and unitally on `V̂'` (so its image is a
subalgebra of `End_ℂ(V̂')` containing `id`) and contains `θ'` with `ι θ' = Θ|V̂'` and
`θ'^† = j − θ'`. As in the notes, `V̂' = ⨁_m V̂_{σ_m}` over finitely many shifted sheets
`σ_m = σ_0 + 2πim/log q` and `A' = ∏_m A`. -/
theorem exists_aw4EAdd_suspension (hq : 1 < q) (x : SuspSpace F q) :
    ∃ W : Submodule ℂ (SuspSpace F q), x ∈ W ∧ FiniteDimensional ℂ W ∧
      ∃ hW : ∀ y ∈ W, theta F q y ∈ W, Nonempty (AW4EAddDatum W ((theta F q).restrict hW) j) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hF0 : ∀ α, F.HasEigenvalue α → α ≠ 0 := by
    rintro α hα rfl
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    exact hv.2 (((Module.End.isUnit_iff F).1 (D.isUnit hq0)).injective (by rw [hv.apply_eq_smul, zero_smul, map_zero]))
  set σ0 := suspEigen q 0
  have hσ0 : WeilRH.IsSheet F q σ0 := isSheet_suspEigen hq hF0 0
  have hL : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.log_pos hq).ne'
  -- every index is on some shifted sheet
  have hshift : ∀ ρ : Idx F q, ∃ m : ℤ,
      ρ.1 = σ0 (qpow q ρ.1) + 2 * Real.pi * Complex.I * m / Real.log q := by
    intro ρ
    have h1 : qpow q (σ0 (qpow q ρ.1)) = qpow q ρ.1 := isSheet_of hσ0 (eigOf ρ)
    have h2 : Complex.exp ((Real.log q : ℂ) * ρ.1 - (Real.log q : ℂ) * σ0 (qpow q ρ.1)) = 1 := by
      rw [Complex.exp_sub, ← qpow, ← qpow, h1, div_self (qpow_ne_zero q _)]
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨m, ?_⟩
    field_simp
    linear_combination hm
  choose mf hmf using hshift
  set M : Finset ℤ := x.support.image mf
  set e : Fin M.card → ℤ := fun i => (M.equivFin.symm i).1
  have he : Function.Injective e := fun i k h => M.equivFin.symm.injective (Subtype.ext h)
  set σ : Fin M.card → ℂ → ℂ := fun i α => σ0 α + 2 * Real.pi * Complex.I * e i / Real.log q
  have hσ : ∀ i, WeilRH.IsSheet F q (σ i) := fun i => isSheet_add_int hq hσ0 (e i)
  set J := sheetSum (fun i => isSheet_of (hσ i))
  have hinj : ∀ (α : Eig F) (i k : Fin M.card), σ i α.1 = σ k α.1 → i = k := by
    intro α i k h
    apply he
    have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
    have h1 : 2 * Real.pi * Complex.I * (e i : ℂ) / Real.log q =
        2 * Real.pi * Complex.I * (e k : ℂ) / Real.log q := add_left_cancel h
    rw [div_left_inj' hL] at h1
    exact_mod_cast mul_left_cancel₀ hc h1
  have hJ : Function.Injective J := sheetSum_injective _ hinj
  have hW : ∀ y ∈ LinearMap.range J, theta F q y ∈ LinearMap.range J := by
    rintro y ⟨w, rfl⟩
    exact ⟨D.truncTheta σ w, (D.theta_sheetSum hq0 σ hσ w).symm⟩
  refine ⟨LinearMap.range J, ?_, LinearMap.finiteDimensional_range J, hW, ?_⟩
  · rw [← DirectSum.sum_support_of x]
    refine Submodule.sum_mem _ fun ρ hρ => ?_
    have hmem : mf ρ ∈ M := Finset.mem_image_of_mem mf hρ
    rw [← DirectSum.lof_eq_of ℂ]
    refine lof_mem_range _ ρ (i := M.equivFin ⟨mf ρ, hmem⟩) ?_ (x ρ)
    simp only [σ, e, Equiv.symm_apply_apply, eigOf]
    exact (hmf ρ).symm
  · exact (D.truncation hq σ hσ).nonempty_range J hJ (theta F q)
      (fun w => D.theta_sheetSum hq0 σ hσ w) hW

end WeilRH.AW4EFDatum
