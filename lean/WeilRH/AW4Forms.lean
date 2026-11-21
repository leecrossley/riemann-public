/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.MultiplicativeForm
import WeilRH.Suspension

/-!
# The vector and algebra forms of AW4 (`def:aw4-forms`, `prop:aw4-forms` (i)–(ii))

`def:aw4-forms` is stated for a Weil datum of type `(d, 0)` in degree `j`, but both forms only
involve the degree-`j` piece `(V^j, Θ_j)`. We therefore state them for a single endomorphism
`Θ : End_ℂ V` and a real weight `j`:

* `AW4V Θ j` (`def:aw4-forms` (a)): `(V, Θ)` admits a positive infinitesimal polarization of weight
  `j` (`def:inf-pol`, `Suspension.IsInfPol`).
* `AW4E Θ j` (`def:aw4-forms` (b)): every vector lies in a finite-dimensional `Θ`-stable subspace
  `V'` carrying an algebra form of AW4-E with `θ_{V'}^† = j - θ_{V'}` (`AW4EAddDatum`, as in
  round 5: an abstract `*`-algebra acting faithfully and unitally on `V'`, which is the same as a
  subalgebra of `End_ℂ(V')` containing `id` and `θ`).

## Main results

* `AW4Forms.maxGenEigenspace_eq_eigenspace`, `AW4Forms.re_eq_half`, `AW4Forms.aw4V_of_aw4E`:
  **`prop:aw4-forms` (i)**. Under AW4-E in degree `j`, `Θ` is diagonalizable on every generalized
  eigenspace, every eigenvalue has real part `j / 2`, and AW4-V holds in degree `j`.
* `AW4Forms.nonempty_aw4EAddDatum`, `AW4Forms.aw4E_of_aw4V`: **`prop:aw4-forms` (ii)**. On a
  spectral core, AW4-V in degree `j` implies AW4-E in degree `j`, with `A_{V'} = End_ℂ(V')` (as
  matrices in an `h`-orthonormal basis), `τ` the trace and `†` the `h`-adjoint. `AW4Forms.HSpace`
  is `V'` with the inner product `⟪u, v⟫ = h(v, u)`.
* `PosHermForm.ofBasis`: the form `Σ_i u_i conj(v_i)` of an arbitrary (possibly infinite) basis.
-/

open Module Complex ComplexConjugate

namespace WeilRH

namespace PosHermForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} (b : Module.Basis ι ℂ V)

/-- The coordinate form `Σ_{i ∈ s} u_i conj(v_i)` over a finset `s`. -/
noncomputable def coordSum (s : Finset ι) (u v : V) : ℂ := ∑ i ∈ s, b.repr u i * conj (b.repr v i)

lemma coordSum_eq_of_subset {s t : Finset ι} (u v : V) (hs : (b.repr u).support ⊆ s)
    (ht : s ⊆ t) : coordSum b s u v = coordSum b t u v := by
  unfold coordSum
  refine Finset.sum_subset ht fun i _ hi => ?_
  have : b.repr u i = 0 := Finsupp.notMem_support_iff.1 (fun h => hi (hs h))
  simp [this]

/-- The form `Σ_i u_i conj(v_i)` attached to a basis of `V`. -/
noncomputable def ofBasis : PosHermForm V where
  toFun u v := coordSum b (b.repr u).support u v
  add_left u u' v := by
    classical
    set s := (b.repr u).support ∪ (b.repr u').support
    have hs : (b.repr (u + u')).support ⊆ s := by
      rw [map_add]; exact Finsupp.support_add
    rw [coordSum_eq_of_subset b _ _ (subset_refl _) hs,
      coordSum_eq_of_subset b u v (subset_refl _) (Finset.subset_union_left : _ ⊆ s),
      coordSum_eq_of_subset b u' v (subset_refl _) (Finset.subset_union_right : _ ⊆ s)]
    simp [coordSum, s, add_mul, Finset.sum_add_distrib]
  smul_left c u v := by
    classical
    have hs : (b.repr (c • u)).support ⊆ (b.repr u).support := by
      rw [map_smul]; exact Finsupp.support_smul
    rw [coordSum_eq_of_subset b _ _ (subset_refl _) hs]
    simp [coordSum, Finset.mul_sum, mul_assoc]
  conj_symm u v := by
    classical
    set s := (b.repr u).support ∪ (b.repr v).support
    rw [coordSum_eq_of_subset b u v (subset_refl _) (Finset.subset_union_left : _ ⊆ s),
      coordSum_eq_of_subset b v u (subset_refl _) (Finset.subset_union_right : _ ⊆ s)]
    simp [coordSum, map_sum, mul_comm]
  re_pos u hu := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr u i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (b.ext_elem fun i => by simp [hcon i])
    simp only [coordSum, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨i, Finsupp.mem_support_iff.2 hi, Complex.normSq_pos.2 hi⟩

lemma ofBasis_apply_basis [DecidableEq ι] (i k : ι) :
    (ofBasis b).toFun (b i) (b k) = if i = k then 1 else 0 := by
  show coordSum b (b.repr (b i)).support (b i) (b k) = _
  rw [coordSum_eq_of_subset b _ _ (subset_refl _) (Finset.subset_union_left (s₂ := {k}))]
  simp only [coordSum, Module.Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = k <;> simp [h]
  · intro x _ hx; simp [Finsupp.single_apply, Ne.symm hx]
  · intro h; simp at h

end PosHermForm

namespace AW4Forms

open WeilRH.Suspension

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **`def:aw4-forms` (a)**, AW4-V in degree `j`: `(V^j, Θ_j)` admits a positive infinitesimal
polarization of weight `j`. -/
def AW4V (Θ : Module.End ℂ V) (j : ℝ) : Prop := ∃ h : PosHermForm V, IsInfPol h Θ j

/-- **`def:aw4-forms` (b)**, AW4-E in degree `j`: every vector of `V^j` lies in a
finite-dimensional `Θ_j`-stable subspace `V'` carrying a positive trace involution on an algebra
`A_{V'} ⊂ End(V')` containing `id` and `θ_{V'} = Θ_j|_{V'}` with `θ_{V'}^† = j - θ_{V'}`. -/
def AW4E (Θ : Module.End ℂ V) (j : ℝ) : Prop :=
  ∀ x : V, ∃ W : Submodule ℂ V, x ∈ W ∧ FiniteDimensional ℂ W ∧
    ∃ hW : ∀ y ∈ W, Θ y ∈ W, Nonempty (AW4EAddDatum W (Θ.restrict hW) j)

variable {Θ : Module.End ℂ V} {j : ℝ}

/-- `prop:aw4-forms` (i), first clause: under AW4-E, `Θ` is diagonalizable on every generalized
eigenspace. -/
theorem maxGenEigenspace_eq_eigenspace (hE : AW4E Θ j) (ρ : ℂ) :
    Θ.maxGenEigenspace ρ = Θ.eigenspace ρ := by
  refine le_antisymm (fun x hx => ?_) Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨W, hxW, hfd, hW, ⟨D⟩⟩ := hE x
  have hss := D.isSemisimple
  have hx' : (⟨x, hxW⟩ : W) ∈ Module.End.maxGenEigenspace (Θ.restrict hW) ρ := by
    rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
    exact hx
  rw [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hx'
  exact Module.End.eigenspace_restrict_le_eigenspace Θ hW ρ ⟨_, hx', rfl⟩

/-- `prop:aw4-forms` (i), second clause: under AW4-E, every eigenvalue of `Θ` has real part
`j / 2`. -/
theorem re_eq_half (hE : AW4E Θ j) {ρ : ℂ} (hρ : Θ.HasEigenvalue ρ) : ρ.re = j / 2 := by
  obtain ⟨v, hv⟩ := hρ.exists_hasEigenvector
  obtain ⟨W, hvW, hfd, hW, ⟨D⟩⟩ := hE v
  refine D.re_eq_half (Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩)
  · rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (by simpa using hv.apply_eq_smul)
  · exact fun h => hv.2 (congrArg Subtype.val h)

/-- Under AW4-E, `V` is the sum of the eigenspaces of `Θ`. -/
theorem iSup_eigenspace_eq_top (hE : AW4E Θ j) : ⨆ ρ, Θ.eigenspace ρ = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨W, hxW, hfd, hW, ⟨D⟩⟩ := hE x
  have hss := D.isSemisimple
  have htop : ⨆ ρ, Module.End.eigenspace (Θ.restrict hW) ρ = ⊤ := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top (Θ.restrict hW)]
    exact iSup_congr fun ρ => (hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace ρ).symm
  have hmem : (⟨x, hxW⟩ : W) ∈ ⨆ ρ, Module.End.eigenspace (Θ.restrict hW) ρ := htop ▸ Submodule.mem_top
  have hmap : x ∈ (⨆ ρ, Module.End.eigenspace (Θ.restrict hW) ρ).map W.subtype := ⟨_, hmem, rfl⟩
  rw [Submodule.map_iSup] at hmap
  exact (iSup_mono fun ρ => Module.End.eigenspace_restrict_le_eigenspace Θ hW ρ) hmap

/-- **`prop:aw4-forms` (i)**, third clause: AW4-E in degree `j` implies AW4-V in degree `j`. The
polarization is the coordinate form of a basis of eigenvectors, an orthogonal sum of positive
definite forms on the eigenspaces. -/
theorem aw4V_of_aw4E (hE : AW4E Θ j) : AW4V Θ j := by
  classical
  have hint : DirectSum.IsInternal fun ρ => Θ.eigenspace ρ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨Module.End.eigenspaces_iSupIndep Θ, iSup_eigenspace_eq_top hE⟩
  let b := hint.collectedBasis fun ρ => Module.Basis.ofVectorSpace ℂ (Θ.eigenspace ρ)
  have hb : ∀ i, Θ (b i) = i.1 • b i := fun i =>
    Module.End.mem_eigenspace_iff.1 (hint.collectedBasis_mem _ i)
  let h := PosHermForm.ofBasis b
  refine ⟨h, ?_⟩
  -- `L(u, v) = h(Θu, v) + h(u, Θv) - j h(u, v)` vanishes on basis pairs and is sesquilinear
  let L : V → V → ℂ := fun u v => h.toFun (Θ u) v + h.toFun u (Θ v) - (j : ℂ) * h.toFun u v
  have hLb : ∀ i k, L (b i) (b k) = 0 := by
    intro i k
    have hh : ∀ i k, h.toFun (b i) (b k) = if i = k then 1 else 0 :=
      PosHermForm.ofBasis_apply_basis b
    simp only [L, hb, h.smul_left, h.smul_right, hh]
    by_cases hik : i = k
    · subst hik
      have hre : i.1.re = j / 2 := by
        refine re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector (x := b i) ⟨?_, b.ne_zero i⟩)
        exact hint.collectedBasis_mem _ i
      simp only [ite_true, mul_one]
      apply Complex.ext <;> simp [hre]
    · simp [hik]
  have hLadd_left : ∀ u u' v, L (u + u') v = L u v + L u' v := by
    intro u u' v; simp only [L, map_add, h.add_left]; ring
  have hLsmul_left : ∀ (c : ℂ) u v, L (c • u) v = c * L u v := by
    intro c u v; simp only [L, map_smul, h.smul_left]; ring
  have hLadd_right : ∀ u v v', L u (v + v') = L u v + L u v' := by
    intro u v v'; simp only [L, map_add, h.add_right]; ring
  have hLsmul_right : ∀ (c : ℂ) u v, L u (c • v) = conj c * L u v := by
    intro c u v; simp only [L, map_smul, h.smul_right]; ring
  have hL0 : ∀ u v, L u v = 0 := by
    intro u v
    have hu : u ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hv : v ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hLb i k
      | zero => simpa using hLsmul_right 0 (b i) 0
      | add y y' _ _ hy hy' => rw [hLadd_right, hy, hy', add_zero]
      | smul c y _ hy => rw [hLsmul_right, hy, mul_zero]
    | zero => simpa using hLsmul_left 0 0 v
    | add x x' _ _ hx hx' => rw [hLadd_left, hx, hx', add_zero]
    | smul c x _ hx => rw [hLsmul_left, hx, mul_zero]
  intro u v
  have := hL0 u v
  simp only [L] at this
  linear_combination this

/-! ### `prop:aw4-forms` (ii): AW4-V ⇒ AW4-E on a spectral core -/

universe u

/-- `W` with the inner product `⟪u, v⟫ = h(v, u)` of a positive definite Hermitian form `h`. -/
def HSpace {W : Type u} [AddCommGroup W] [Module ℂ W] (_h : PosHermForm W) : Type u := W

namespace HSpace

variable {W : Type u} [AddCommGroup W] [Module ℂ W] (h : PosHermForm W)

instance : AddCommGroup (HSpace h) := inferInstanceAs (AddCommGroup W)
instance : Module ℂ (HSpace h) := inferInstanceAs (Module ℂ W)

omit [Module ℂ W] in
lemma _root_.WeilRH.PosHermForm.re_nonneg {W : Type*} [AddCommGroup W] [Module ℂ W]
    (h : PosHermForm W) (x : W) : 0 ≤ (h.toFun x x).re := by
  by_cases hx : x = 0
  · have h0 : h.toFun 0 0 = 0 := by simpa using h.smul_left 0 (0 : W) 0
    simp [hx, h0]
  · exact (h.re_pos x hx).le

/-- The inner product core `⟪u, v⟫ = h(v, u)`. -/
@[instance_reducible]
def core : InnerProductSpace.Core ℂ (HSpace h) where
  inner u v := h.toFun v u
  conj_inner_symm x y := h.conj_symm x y
  re_inner_nonneg x := PosHermForm.re_nonneg h (x : W)
  add_left x y z := h.add_right z x y
  smul_left x y r := h.smul_right r y x
  definite x hx := by
    by_contra hne
    have := h.re_pos x hne
    simp [hx] at this

noncomputable instance normedAddCommGroup : NormedAddCommGroup (HSpace h) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core h)

noncomputable instance innerProductSpace : InnerProductSpace ℂ (HSpace h) :=
  InnerProductSpace.ofCore (core h).toCore

instance [FiniteDimensional ℂ W] : FiniteDimensional ℂ (HSpace h) :=
  inferInstanceAs (FiniteDimensional ℂ W)

lemma inner_eq (u v : HSpace h) : inner ℂ u v = h.toFun v u := rfl

end HSpace

/-- **`prop:aw4-forms` (ii), finite-dimensional step.** A positive infinitesimal polarization of
weight `j` on a finite-dimensional `(W, Θ)` gives the algebra form AW4-E: `A = End_ℂ(W)` (as
matrices in an `h`-orthonormal basis), `τ` the trace and `†` the `h`-adjoint. -/
theorem nonempty_aw4EAddDatum {W : Type u} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {Θ : Module.End ℂ W} {j : ℝ} {h : PosHermForm W} (hh : IsInfPol h Θ j) :
    Nonempty (AW4EAddDatum W Θ j) := by
  let n := ULift.{u} (Fin (finrank ℂ (HSpace h)))
  let v : OrthonormalBasis n ℂ (HSpace h) := (stdOrthonormalBasis ℂ (HSpace h)).reindex Equiv.ulift.symm
  let Θ' : Module.End ℂ (HSpace h) := Θ
  let e := LinearMap.toMatrixOrthonormal v
  have key : ∀ x y : W, h.toFun y ((j : ℂ) • x - Θ x) = h.toFun (Θ y) x := by
    intro x y
    have hs : ∀ a b : W, h.toFun y (a - b) = h.toFun y a - h.toFun y b := by
      intro a b
      rw [sub_eq_add_neg, h.add_right, ← neg_one_smul ℂ b, h.smul_right]
      simp
      ring
    rw [hs, h.smul_right, Complex.conj_ofReal]
    linear_combination -(hh y x)
  have hadj : LinearMap.adjoint Θ' = (j : ℂ) • 1 - Θ' := by
    symm
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    exact key x y
  exact ⟨{
    A := Matrix n n ℂ
    P := matrixTrace
    ι := AlgHom.ofClass e.symm
    ι_injective := e.symm.injective
    θ := e Θ'
    ι_θ := e.symm_apply_apply Θ'
    add_star := by
      rw [← map_star e, LinearMap.star_eq_adjoint, hadj, map_sub, map_smul, map_one] }⟩

/-- **`prop:aw4-forms` (ii).** If `(V, Θ)` is a spectral core (`def:spectral-core`), AW4-V in degree
`j` implies AW4-E in degree `j`: each vector lies in a finite sum `V'` of generalized eigenspaces,
which is finite-dimensional and `Θ`-stable, and `End_ℂ(V')` with the trace and the `h|_{V'}`-adjoint
is a positive trace involution with `θ_{V'}^† = j - θ_{V'}`. -/
theorem aw4E_of_aw4V {V : Type*} [AddCommGroup V] [Module ℂ V] {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hV : AW4V Θ j) : AW4E Θ j := by
  obtain ⟨h, hh⟩ := hV
  intro x
  have hx : x ∈ ⨆ ρ, Θ.maxGenEigenspace ρ := hS.iSup_eq_top ▸ Submodule.mem_top
  obtain ⟨s, hxs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  rw [iSup_subtype'] at hxs
  set W : Submodule ℂ V := ⨆ ρ : s, Θ.maxGenEigenspace ρ with hWdef
  have : ∀ ρ : s, FiniteDimensional ℂ (Θ.maxGenEigenspace ρ) := fun ρ => hS.finiteDimensional ρ
  have hfd : FiniteDimensional ℂ W := Submodule.finiteDimensional_iSup _
  have hW : ∀ y ∈ W, Θ y ∈ W := by
    intro y hy
    have hmap : W.map Θ ≤ W := by
      rw [hWdef, Submodule.map_iSup]
      refine iSup_mono fun ρ => ?_
      rintro _ ⟨z, hz, rfl⟩
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl Θ) ρ hz
    exact hmap ⟨y, hy, rfl⟩
  refine ⟨W, hxs, hfd, hW, nonempty_aw4EAddDatum (h := h.restrict W) ?_⟩
  intro u v
  exact hh u v

end AW4Forms

end WeilRH
