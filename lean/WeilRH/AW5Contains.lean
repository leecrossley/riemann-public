/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.AW4Forms

/-!
# AW5 contains AW4-V (`prop:aw5-contains` (i)–(ii))

`prop:aw5-contains` concerns a Weil datum of type `(d, 0)` whose star form `h_j` is positive
definite in degree `j` and which satisfies AW5 (`def:aw-analytic`) in that degree. Only the
degree-`j` piece `(V^j, Θ_j, h_j)` enters, so we state it for `Θ : End_ℂ V`, `h : PosHermForm V`
and a real weight `j`.

## Main results

* `AW5Contains.AW5Local`: the AW5 condition restricted to `V^j`, namely that the normalized flow
  `e^{-jt/2} e^{tΘ}` is `h`-isometric on finite-dimensional `Θ`-stable subspaces.
* `AW5Contains.isInfPol_of_aw5`: **`prop:aw5-contains` (i)**. `h` is a positive infinitesimal
  polarization of weight `j`, so AW4-V holds in degree `j`.
* `AW5Contains.aw5_pure`: **`prop:aw5-contains` (ii)**. On a spectral core, `Θ_j` is
  diagonalizable, its eigenvalues have real part `j / 2`, and distinct eigenspaces are
  `h`-orthogonal.

Parts (iii)–(iv) need the Hilbert completion `𝓗^j` and `prop:hilbert`, which are not formalized.
-/

open Module Complex WeilRH.Suspension WeilRH.AW4Forms
open scoped ComplexConjugate

namespace WeilRH.AW5Contains

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The flow generator `Θ|_W - j/2` on `W` with the inner product of `h|_W`. -/
noncomputable def gen (h : PosHermForm V) (Θ : Module.End ℂ V) (j : ℝ) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, Θ w ∈ W) :
    HSpace (h.restrict W) →L[ℂ] HSpace (h.restrict W) :=
  LinearMap.toContinuousLinearMap
    ((Θ.restrict hW - ((j / 2 : ℝ) : ℂ) • 1 : Module.End ℂ W) : Module.End ℂ (HSpace (h.restrict W)))


/-- If `t ↦ exp(tA)` is isometric on a complete inner product space, then
`⟪v, Av⟫ + ⟪Av, v⟫ = 0`. -/
lemma inner_gen_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (hU : ∀ (t : ℝ) (v : E), ‖NormedSpace.exp ((t : ℂ) • A) v‖ = ‖v‖) (v : E) :
    inner ℂ v (A v) + inner ℂ (A v) v = 0 := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • A) v) (A v) 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℂ) A ((0 : ℝ) : ℂ)).scomp (0 : ℝ)
      Complex.ofRealCLM.hasDerivAt
    have h2 := (((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
      (0 : ℝ) h1
    simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.apply_apply, ofRealCLM_apply, ofReal_zero, zero_smul,
      NormedSpace.exp_zero, one_mul, ofReal_one, one_smul] at h2
    exact h2
  have hi := hd.inner ℂ hd
  have hc : (fun t : ℝ => inner ℂ (NormedSpace.exp ((t : ℂ) • A) v)
      (NormedSpace.exp ((t : ℂ) • A) v)) = fun _ => ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [inner_self_eq_norm_sq_to_K, hU]; push_cast; rfl
  rw [hc] at hi
  have := hi.unique (hasDerivAt_const (0 : ℝ) _)
  simpa using this

/-- A sesquilinear defect `D(a, b) = h(Θa, b) + h(a, Θb) - j h(a, b)` vanishing on the diagonal of a
submodule vanishes there identically (complex polarization). -/
lemma defect_eq_zero (h : PosHermForm V) (Θ : Module.End ℂ V) (j : ℝ) (W : Submodule ℂ V)
    (hD : ∀ x ∈ W, h.toFun (Θ x) x + h.toFun x (Θ x) - (j : ℂ) * h.toFun x x = 0)
    {u v : V} (hu : u ∈ W) (hv : v ∈ W) :
    h.toFun (Θ u) v + h.toFun u (Θ v) = (j : ℂ) * h.toFun u v := by
  have e := fun (c : ℂ) => hD (u + c • v) (W.add_mem hu (W.smul_mem c hv))
  have e1 := e 1
  have e2 := e (-1)
  have e3 := e I
  have e4 := e (-I)
  simp only [map_add, map_smul, h.add_left, h.add_right, h.smul_left, h.smul_right] at e1 e2 e3 e4
  simp only [map_one, map_neg, conj_I, one_mul, neg_mul, neg_neg] at e1 e2 e3 e4
  linear_combination (norm := skip) (e1 - e2 + I * e3 - I * e4) / 4
  ring_nf
  simp only [I_sq]
  ring

/-- **AW5 on the core `V^j`** (`def:aw-analytic`, AW5, as used in `prop:aw5-contains`). The
normalized flow `U_j(t) = e^{-jt/2} e^{tΘ}` is isometric for `h`: on every finite-dimensional
`Θ`-stable `W ⊆ V`, `‖exp(t(Θ|_W - j/2)) v‖_h = ‖v‖_h` for all real `t`. This is the restriction
to `V^j` of the unitarity in AW5; the completion, strong continuity and core clauses are not
encoded, since the proof of (i) does not use them. -/
def AW5Local (h : PosHermForm V) (Θ : Module.End ℂ V) (j : ℝ) : Prop :=
  ∀ (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, Θ w ∈ W) (t : ℝ)
    (v : HSpace (h.restrict W)), ‖NormedSpace.exp ((t : ℂ) • gen h Θ j W hW) v‖ = ‖v‖

/-- Every vector lies in a finite-dimensional `Θ`-stable subspace. -/
def LocFin (Θ : Module.End ℂ V) : Prop :=
  ∀ x : V, ∃ W : Submodule ℂ V, x ∈ W ∧ FiniteDimensional ℂ W ∧ ∀ w ∈ W, Θ w ∈ W

/-- **`prop:aw5-contains` (i).** If every vector lies in a finite-dimensional `Θ`-stable subspace
and the normalized flow is `h`-isometric there (AW5 on `V^j`), then `h` is a positive infinitesimal
polarization of weight `j` on `(V^j, Θ_j)`. The proof is the source's: differentiate
`h(U(t)v, U(t)v) = h(v, v)` at `t = 0`, then polarize. -/
theorem isInfPol_of_aw5 {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hloc : LocFin Θ) (hU : AW5Local h Θ j) : IsInfPol h Θ j := by
  intro u v
  obtain ⟨Wu, hu, hfu, hsu⟩ := hloc u
  obtain ⟨Wv, hv, hfv, hsv⟩ := hloc v
  let W := Wu ⊔ Wv
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_sup _ _
  have hW : ∀ w ∈ W, Θ w ∈ W := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact W.add_mem (Submodule.mem_sup_left (hsu a ha)) (Submodule.mem_sup_right (hsv b hb))
  refine defect_eq_zero h Θ j W ?_ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hv)
  intro x hx
  let x' : HSpace (h.restrict W) := ⟨x, hx⟩
  have key := inner_gen_add (gen h Θ j W hW) (hU W hW) x'
  change (h.restrict W).toFun (gen h Θ j W hW x') x' + (h.restrict W).toFun x' (gen h Θ j W hW x')
    = 0 at key
  have hc : ((show W from gen h Θ j W hW x') : V) = Θ x + (-((j / 2 : ℝ) : ℂ)) • x := by
    change Θ x - ((j / 2 : ℝ) : ℂ) • x = _
    rw [sub_eq_add_neg, neg_smul]
  change h.toFun ((show W from gen h Θ j W hW x') : V) x + h.toFun x ((show W from gen h Θ j W hW x') : V) = 0 at key
  rw [hc] at key
  simp only [h.add_left, h.add_right, h.smul_left, h.smul_right, map_neg, conj_ofReal] at key
  push_cast at key
  linear_combination key

/-- A spectral core is locally finite. -/
lemma locFin_of_spectralCore {Θ : Module.End ℂ V} (hS : WeilRH.Spectral.SpectralCore Θ) :
    LocFin Θ := by
  intro x
  have hx : x ∈ ⨆ ρ, Θ.maxGenEigenspace ρ := hS.iSup_eq_top ▸ Submodule.mem_top
  obtain ⟨s, hxs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  rw [iSup_subtype'] at hxs
  set W : Submodule ℂ V := ⨆ ρ : s, Θ.maxGenEigenspace ρ with hWdef
  have : ∀ ρ : s, FiniteDimensional ℂ (Θ.maxGenEigenspace ρ) := fun ρ => hS.finiteDimensional ρ
  refine ⟨W, hxs, Submodule.finiteDimensional_iSup _, ?_⟩
  intro y hy
  have hmap : W.map Θ ≤ W := by
    rw [hWdef, Submodule.map_iSup]
    refine iSup_mono fun ρ => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl Θ) ρ hz
  exact hmap ⟨y, hy, rfl⟩

/-- **`prop:aw5-contains` (ii).** On a spectral core with AW5 in degree `j`, `Θ_j` is
diagonalizable, every eigenvalue has real part `j / 2`, and distinct eigenspaces are
`h`-orthogonal. -/
theorem aw5_pure {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : WeilRH.Spectral.SpectralCore Θ) (hU : AW5Local h Θ j) :
    (⨆ ρ, Θ.eigenspace ρ = ⊤) ∧ (∀ ρ, Θ.HasEigenvalue ρ → ρ.re = j / 2) ∧
    ∀ ρ σ, ρ ≠ σ → ∀ u ∈ Θ.eigenspace ρ, ∀ v ∈ Θ.eigenspace σ, h.toFun u v = 0 := by
  have hpol := isInfPol_of_aw5 (locFin_of_spectralCore hS) hU
  have hE := AW4Forms.aw4E_of_aw4V hS ⟨h, hpol⟩
  refine ⟨AW4Forms.iSup_eigenspace_eq_top hE, fun ρ hρ => AW4Forms.re_eq_half hE hρ, ?_⟩
  intro ρ σ hne u hu v hv
  have hu' := Module.End.mem_eigenspace_iff.1 hu
  have hv' := Module.End.mem_eigenspace_iff.1 hv
  have e := hpol u v
  rw [hu', hv', h.smul_left, h.smul_right] at e
  by_cases hu0 : u = 0
  · subst hu0; simpa using h.smul_left 0 0 v
  by_cases hv0 : v = 0
  · subst hv0; simpa using h.smul_right 0 u 0
  have hρ : ρ.re = j / 2 := AW4Forms.re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hu, hu0⟩)
  have hσ : σ.re = j / 2 := AW4Forms.re_eq_half hE (Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
  have hc : ρ + (starRingEnd ℂ) σ - (j : ℂ) ≠ 0 := by
    intro h0
    apply hne
    have him := congrArg Complex.im h0
    simp at him
    apply Complex.ext
    · rw [hρ, hσ]
    · linarith
  have : (ρ + (starRingEnd ℂ) σ - (j : ℂ)) * h.toFun u v = 0 := by linear_combination e
  exact (mul_eq_zero.1 this).resolve_left hc

end WeilRH.AW5Contains
