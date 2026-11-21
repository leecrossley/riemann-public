/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Zeta-regularized determinants (`def:regdet`, round 73)

Source: `latex/notes.tex`, `def:regdet` (a)–(d).

Let `S ⊆ ℂ` be the spectrum of a spectral core and `m : ℂ → ℕ` its multiplicity function (the
definition only uses this pair, so we state it for an arbitrary set with multiplicities; for a
spectral core take `S = spec Θ`, `m = WeilRH.Spectral.mult Θ`).

* (a) `SpectralCut S`: a nonempty open `U` disjoint from `S` and, for each `ρ ∈ S`, a holomorphic
  branch `L ρ` of `log((s - ρ)/2π)` on `U`; `((s - ρ)/2π)^{-w} := exp(-w L_ρ(s))`.
* (b) `specZeta c m w s = ∑_{ρ ∈ S} m(ρ) ((s - ρ)/2π)^{-w}` (a `tsum`; `ConvergesAt` records absolute
  convergence).
* (c) `Regularization c m`: zeta-regularizability, carried as data — for each `s ∈ U` a half-plane
  `Re w > σ(s)` of absolute convergence, a meromorphic continuation `Z s` on a preconnected open
  domain containing that half-plane and `0`, regular at `0`; `s ↦ ∂_w Z(0; s)` holomorphic on `U`;
  and an entire function `D` with `D = exp(-∂_w Z(0; ·))` on `U`.
* (d) `detreg r := r.D`.

**Representation choice.** The manuscript fixes and records the cut as part of the data; here the
continuation and the entire extension are recorded too. The entire extension is unique
(`Regularization.D_unique`), and when `S` is finite the determinant is
`∏_ρ ((s - ρ)/2π)^{m(ρ)}` for *every* cut and *every* regularization (`detreg_finite`), which is the
manuscript's remark after `def:regdet`; `Regularization.ofFinite` shows that such a regularization
exists, so the notion is not vacuous.
-/

open Complex Set Filter Topology
open scoped Real

namespace WeilRH

namespace RegDet

/-- `def:regdet` (a): a spectral cut for the spectrum `S`. -/
structure SpectralCut (S : Set ℂ) where
  /-- The open set on which the branches live. -/
  U : Set ℂ
  isOpen : IsOpen U
  nonempty : U.Nonempty
  disjoint : Disjoint U S
  /-- The branch `L ρ` of `log((s - ρ)/2π)`. -/
  L : ℂ → ℂ → ℂ
  holo : ∀ ρ ∈ S, DifferentiableOn ℂ (L ρ) U
  exp_L : ∀ ρ ∈ S, ∀ s ∈ U, exp (L ρ s) = (s - ρ) / (2 * π)

variable {S : Set ℂ}

/-- `((s - ρ)/2π)^{-w} = exp(-w L_ρ(s))` for the cut. -/
noncomputable def SpectralCut.pow (c : SpectralCut S) (ρ s w : ℂ) : ℂ := exp (-w * c.L ρ s)

/-- The terms `m(ρ) ((s - ρ)/2π)^{-w}` of the spectral zeta function. -/
noncomputable def zetaTerm (c : SpectralCut S) (m : ℂ → ℕ) (w s : ℂ) (ρ : S) : ℂ :=
  (m ρ : ℂ) * c.pow ρ s w

/-- `def:regdet` (b): the spectral zeta function `Z(w; s)`. -/
noncomputable def specZeta (c : SpectralCut S) (m : ℂ → ℕ) (w s : ℂ) : ℂ :=
  ∑' ρ : S, zetaTerm c m w s ρ

/-- Absolute convergence of the series defining `Z(w; s)`. -/
def ConvergesAt (c : SpectralCut S) (m : ℂ → ℕ) (w s : ℂ) : Prop :=
  Summable fun ρ : S => ‖zetaTerm c m w s ρ‖

/-- `def:regdet` (c): zeta-regularizability for the cut `c`, with its witnesses. -/
structure Regularization (c : SpectralCut S) (m : ℂ → ℕ) where
  /-- Abscissa of absolute convergence (for each `s`). -/
  σ : ℂ → ℝ
  converges : ∀ s ∈ c.U, ∀ w : ℂ, σ s < w.re → ConvergesAt c m w s
  /-- The continuation `w ↦ Z(w; s)`. -/
  Z : ℂ → ℂ → ℂ
  /-- Its (preconnected, open) domain. -/
  dom : ℂ → Set ℂ
  dom_open : ∀ s ∈ c.U, IsOpen (dom s)
  dom_preconnected : ∀ s ∈ c.U, IsPreconnected (dom s)
  halfPlane_subset : ∀ s ∈ c.U, {w : ℂ | σ s < w.re} ⊆ dom s
  zero_mem : ∀ s ∈ c.U, (0 : ℂ) ∈ dom s
  merom : ∀ s ∈ c.U, MeromorphicOn (Z s) (dom s)
  eq_series : ∀ s ∈ c.U, ∀ w : ℂ, σ s < w.re → Z s w = specZeta c m w s
  regular : ∀ s ∈ c.U, AnalyticAt ℂ (Z s) 0
  holo_deriv : DifferentiableOn ℂ (fun s => deriv (Z s) 0) c.U
  /-- The entire continuation of `s ↦ exp(-∂_w Z(0; s))`. -/
  D : ℂ → ℂ
  entire : Differentiable ℂ D
  D_eq : ∀ s ∈ c.U, D s = exp (-deriv (Z s) 0)

/-- `def:regdet` (d): the regularized determinant `det_reg((s - Θ)/2π)` for the cut. -/
noncomputable def detreg {c : SpectralCut S} {m : ℂ → ℕ} (r : Regularization c m) : ℂ → ℂ := r.D

/-- Two entire functions that agree on a nonempty open set agree everywhere. -/
lemma entire_eq_of_eqOn {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) (h : EqOn f g U) : f = g := by
  obtain ⟨z, hz⟩ := hne
  have := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ z)
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h)
  exact funext fun s => this (mem_univ s)

/-- The entire extension in `def:regdet` (c) is unique. -/
theorem Regularization.D_unique {c : SpectralCut S} {m : ℂ → ℕ} (r : Regularization c m)
    {D' : ℂ → ℂ} (hD' : Differentiable ℂ D') (h : ∀ s ∈ c.U, D' s = exp (-deriv (r.Z s) 0)) :
    D' = detreg r :=
  entire_eq_of_eqOn hD' r.entire c.isOpen c.nonempty (fun s hs => (h s hs).trans (r.D_eq s hs).symm)

section Finite

variable (F : Finset ℂ) (c : SpectralCut (F : Set ℂ)) (m : ℂ → ℕ)

/-- For finite spectrum, `Z(w; s)` is the finite sum `∑_{ρ ∈ F} m(ρ) exp(-w L_ρ(s))`. -/
noncomputable def finZeta (s w : ℂ) : ℂ := ∑ ρ ∈ F, (m ρ : ℂ) * exp (-w * c.L ρ s)

lemma specZeta_finite (w s : ℂ) : specZeta c m w s = finZeta F c m s w := by
  unfold specZeta finZeta zetaTerm SpectralCut.pow
  rw [tsum_fintype]
  exact Finset.sum_coe_sort F (fun ρ => (m ρ : ℂ) * exp (-w * c.L ρ s))

lemma hasDerivAt_finZeta (s w : ℂ) :
    HasDerivAt (finZeta F c m s)
      (∑ ρ ∈ F, (m ρ : ℂ) * (exp (-w * c.L ρ s) * (-c.L ρ s))) w := by
  unfold finZeta
  refine HasDerivAt.fun_sum (fun ρ _ => ?_)
  have h1 : HasDerivAt (fun w : ℂ => -w * c.L ρ s) (-c.L ρ s) w := by
    simpa using ((hasDerivAt_id w).neg.mul_const (c.L ρ s))
  exact h1.cexp.const_mul _

lemma differentiable_finZeta (s : ℂ) : Differentiable ℂ (finZeta F c m s) :=
  fun w => (hasDerivAt_finZeta F c m s w).differentiableAt

lemma deriv_finZeta_zero (s : ℂ) :
    deriv (finZeta F c m s) 0 = -∑ ρ ∈ F, (m ρ : ℂ) * c.L ρ s := by
  rw [(hasDerivAt_finZeta F c m s 0).deriv, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  simp

/-- `exp(-∂_w Z(0; s)) = ∏_ρ ((s - ρ)/2π)^{m(ρ)}` on the cut's domain. -/
lemma exp_neg_deriv_finZeta {s : ℂ} (hs : s ∈ c.U) :
    exp (-deriv (finZeta F c m s) 0) = ∏ ρ ∈ F, ((s - ρ) / (2 * π)) ^ m ρ := by
  rw [deriv_finZeta_zero, neg_neg, exp_sum]
  refine Finset.prod_congr rfl (fun ρ hρ => ?_)
  rw [exp_nat_mul, c.exp_L ρ (by simpa using hρ) s hs]

/-- The finite product `∏_ρ ((s - ρ)/2π)^{m(ρ)}`. -/
noncomputable def finDet (s : ℂ) : ℂ := ∏ ρ ∈ F, ((s - ρ) / (2 * π)) ^ m ρ

lemma differentiable_finDet : Differentiable ℂ (finDet F m) := by
  unfold finDet; fun_prop

/-- Every cut of a finite spectrum is zeta-regularizable (the notion is not vacuous). -/
noncomputable def Regularization.ofFinite : Regularization c m where
  σ := fun _ => 0
  converges := fun _ _ _ _ => Summable.of_finite
  Z := finZeta F c m
  dom := fun _ => univ
  dom_open := fun _ _ => isOpen_univ
  dom_preconnected := fun _ _ => isPreconnected_univ
  halfPlane_subset := fun _ _ => subset_univ _
  zero_mem := fun _ _ => mem_univ _
  merom := fun s _ w _ => ((differentiable_finZeta F c m s).analyticAt w).meromorphicAt
  eq_series := fun s _ w _ => (specZeta_finite F c m w s).symm
  regular := fun s _ => (differentiable_finZeta F c m s).analyticAt 0
  holo_deriv := by
    have : EqOn (fun s => deriv (finZeta F c m s) 0) (fun s => -∑ ρ ∈ F, (m ρ : ℂ) * c.L ρ s)
        c.U := fun s _ => deriv_finZeta_zero F c m s
    refine DifferentiableOn.congr ?_ this
    refine (DifferentiableOn.fun_sum (fun ρ hρ => ?_)).neg
    exact (c.holo ρ (by simpa using hρ)).const_mul _
  D := finDet F m
  entire := differentiable_finDet F m
  D_eq := fun s hs => (exp_neg_deriv_finZeta F c m hs).symm

/-- **Finite spectrum (the remark after `def:regdet`).** For every cut and every regularization,
`det_reg((s - Θ)/2π) = ∏_ρ ((s - ρ)/2π)^{m(ρ)}`; in particular it does not depend on the cut. -/
theorem detreg_finite (r : Regularization c m) : detreg r = finDet F m := by
  refine (entire_eq_of_eqOn r.entire (differentiable_finDet F m) c.isOpen c.nonempty
    (fun s hs => ?_))
  rw [show detreg r s = r.D s from rfl, r.D_eq s hs]
  unfold finDet
  rw [← exp_neg_deriv_finZeta F c m hs]
  congr 2
  -- the continuation agrees with the finite sum near `0`
  set g : ℂ → ℂ := fun w => r.Z s w - finZeta F c m s w
  have hgm : MeromorphicOn g (r.dom s) := fun w hw =>
    (r.merom s hs w hw).sub (((differentiable_finZeta F c m s).analyticAt w).meromorphicAt)
  set w₁ : ℂ := ((r.σ s + 1 : ℝ) : ℂ)
  have hw₁ : w₁ ∈ {w : ℂ | r.σ s < w.re} := by simp [w₁]
  have hopen : IsOpen {w : ℂ | r.σ s < w.re} := isOpen_lt continuous_const continuous_re
  have hg₁ : g =ᶠ[𝓝 w₁] 0 := by
    filter_upwards [hopen.mem_nhds hw₁] with w hw
    simp [g, r.eq_series s hs w hw, specZeta_finite]
  have htop₁ : meromorphicOrderAt g w₁ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (hg₁.filter_mono nhdsWithin_le_nhds)
  have htop₀ : meromorphicOrderAt g 0 = ⊤ :=
    hgm.meromorphicOrderAt_eq_top_of_isPreconnected (r.dom_preconnected s hs)
      (r.halfPlane_subset s hs hw₁) (r.zero_mem s hs) htop₁
  have hga : AnalyticAt ℂ g 0 :=
    (r.regular s hs).sub ((differentiable_finZeta F c m s).analyticAt 0)
  have hg0 : g =ᶠ[𝓝 0] 0 :=
    hga.frequently_zero_iff_eventually_zero.1
      (meromorphicOrderAt_eq_top_iff.1 htop₀).frequently
  have : r.Z s =ᶠ[𝓝 0] finZeta F c m s := by
    filter_upwards [hg0] with w hw
    simpa [g, sub_eq_zero] using hw
  exact this.deriv_eq

end Finite

section Independence

variable {S : Set ℂ} {c : SpectralCut S} {m : ℂ → ℕ}

/-- **Independence of the regularization (round 74).** Two regularizations of the same cut give
the same `det_reg`, provided that for each `s ∈ U` their continuation domains share a preconnected
open set `W` containing `0` and a point to the right of both convergence abscissae. Without such a
condition the continuations to `w = 0` along different domains need not agree; `def:regdet` in
`notes.tex` leaves the continuation domain unspecified. -/
theorem detreg_eq_of_common_domain (r r' : Regularization c m)
    (hW : ∀ s ∈ c.U, ∃ W : Set ℂ, IsOpen W ∧ IsPreconnected W ∧ W ⊆ r.dom s ∩ r'.dom s ∧
      (0 : ℂ) ∈ W ∧ ∃ w₁ ∈ W, r.σ s < w₁.re ∧ r'.σ s < w₁.re) :
    detreg r = detreg r' := by
  refine entire_eq_of_eqOn r.entire r'.entire c.isOpen c.nonempty (fun s hs => ?_)
  show r.D s = r'.D s
  rw [r.D_eq s hs, r'.D_eq s hs]
  obtain ⟨W, hWo, hWp, hWsub, h0, w₁, hw₁, hσ, hσ'⟩ := hW s hs
  set g : ℂ → ℂ := fun w => r.Z s w - r'.Z s w
  have hgm : MeromorphicOn g W := fun w hw =>
    (r.merom s hs w (hWsub hw).1).sub (r'.merom s hs w (hWsub hw).2)
  have hopen : IsOpen {w : ℂ | r.σ s < w.re ∧ r'.σ s < w.re} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_re)
  have hg₁ : g =ᶠ[𝓝 w₁] 0 := by
    filter_upwards [hopen.mem_nhds ⟨hσ, hσ'⟩] with w hw
    simp [g, r.eq_series s hs w hw.1, r'.eq_series s hs w hw.2]
  have htop₁ : meromorphicOrderAt g w₁ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (hg₁.filter_mono nhdsWithin_le_nhds)
  have htop₀ : meromorphicOrderAt g 0 = ⊤ :=
    hgm.meromorphicOrderAt_eq_top_of_isPreconnected hWp hw₁ h0 htop₁
  have hga : AnalyticAt ℂ g 0 := (r.regular s hs).sub (r'.regular s hs)
  have hg0 : g =ᶠ[𝓝 0] 0 :=
    hga.frequently_zero_iff_eventually_zero.1
      (meromorphicOrderAt_eq_top_iff.1 htop₀).frequently
  have : r.Z s =ᶠ[𝓝 0] r'.Z s := by
    filter_upwards [hg0] with w hw
    simpa [g, sub_eq_zero] using hw
  rw [this.deriv_eq]

/-- In particular two regularizations with the same continuation domains give the same
`det_reg`. -/
theorem detreg_eq_of_dom_eq (r r' : Regularization c m) (h : ∀ s ∈ c.U, r.dom s = r'.dom s) :
    detreg r = detreg r' := by
  refine detreg_eq_of_common_domain r r' (fun s hs => ⟨r.dom s, r.dom_open s hs,
    r.dom_preconnected s hs, fun w hw => ⟨hw, h s hs ▸ hw⟩, r.zero_mem s hs, ?_⟩)
  refine ⟨((max (r.σ s) (r'.σ s) + 1 : ℝ) : ℂ), r.halfPlane_subset s hs ?_, ?_, ?_⟩ <;>
    simp <;> linarith [le_max_left (r.σ s) (r'.σ s), le_max_right (r.σ s) (r'.σ s)]

end Independence

section HalfPlane

/-! ### `def:regdet` (c) as revised (`regdet-canonical`, 2026-11-20; round 77)

`notes.tex` now asks that `Z(w; s)` continue to a meromorphic function on a half-plane
`Re w > -ε(s)`, `ε(s) > 0`, regular at `w = 0`. A `Regularization` records a continuation on a
preconnected domain containing the convergence half-plane and `0`; `OnHalfPlane` adds that the domain
contains such a half-plane, so `Z s` is meromorphic there. With it `det_reg` depends only on the cut
(`detreg_eq_of_onHalfPlane`), which is the paragraph after the definition. -/

variable {S : Set ℂ} {c : SpectralCut S} {m : ℂ → ℕ}

/-- The continuation domain of `r` contains a half-plane `Re w > -ε(s)` with `ε(s) > 0`, for every
`s ∈ U` (revised `def:regdet` (c)). -/
def Regularization.OnHalfPlane (r : Regularization c m) : Prop :=
  ∀ s ∈ c.U, ∃ ε : ℝ, 0 < ε ∧ {w : ℂ | -ε < w.re} ⊆ r.dom s

/-- Revised `def:regdet` (c): the cut is zeta-regularizable. -/
def IsZetaRegularizable (c : SpectralCut S) (m : ℂ → ℕ) : Prop :=
  ∃ r : Regularization c m, r.OnHalfPlane

/-- **Uniqueness (the paragraph after `def:regdet`).** Two half-plane regularizations of the same
cut give the same `det_reg`. -/
theorem detreg_eq_of_onHalfPlane (r r' : Regularization c m) (hr : r.OnHalfPlane)
    (hr' : r'.OnHalfPlane) : detreg r = detreg r' := by
  refine detreg_eq_of_common_domain r r' (fun s hs => ?_)
  obtain ⟨ε, hε, hεs⟩ := hr s hs
  obtain ⟨ε', hε', hεs'⟩ := hr' s hs
  set δ := min ε ε'
  have hδ : 0 < δ := lt_min hε hε'
  refine ⟨{w : ℂ | -δ < w.re}, isOpen_lt continuous_const continuous_re,
    (convex_halfSpace_re_gt (-δ)).isPreconnected, fun w hw => ⟨hεs ?_, hεs' ?_⟩, ?_, ?_⟩
  · simp only [mem_ofPred_eq] at hw ⊢; linarith [min_le_left ε ε']
  · simp only [mem_ofPred_eq] at hw ⊢; linarith [min_le_right ε ε']
  · simp [hδ]
  · refine ⟨((max (max (r.σ s) (r'.σ s)) 0 + 1 : ℝ) : ℂ), ?_, ?_, ?_⟩ <;> simp only [mem_ofPred_eq,
      ofReal_re] <;>
      linarith [le_max_left (max (r.σ s) (r'.σ s)) 0, le_max_right (max (r.σ s) (r'.σ s)) 0,
        le_max_left (r.σ s) (r'.σ s), le_max_right (r.σ s) (r'.σ s)]

/-- The regularized determinant of a zeta-regularizable cut (revised `def:regdet` (d)). -/
noncomputable def canonicalDetreg (h : IsZetaRegularizable c m) : ℂ → ℂ := detreg h.choose

/-- Every half-plane regularization computes `canonicalDetreg`, so `det_reg` depends only on the
cut. -/
theorem detreg_eq_canonical (r : Regularization c m) (hr : r.OnHalfPlane) :
    detreg r = canonicalDetreg ⟨r, hr⟩ :=
  detreg_eq_of_onHalfPlane r _ hr (⟨r, hr⟩ : IsZetaRegularizable c m).choose_spec

/-- The finite-spectrum regularization is a half-plane one; finite spectra are zeta-regularizable
in the revised sense, so the revised notion is not vacuous. -/
theorem Regularization.ofFinite_onHalfPlane (F : Finset ℂ) (c : SpectralCut (F : Set ℂ))
    (m : ℂ → ℕ) : (Regularization.ofFinite F c m).OnHalfPlane :=
  fun _ _ => ⟨1, one_pos, subset_univ _⟩

theorem isZetaRegularizable_finite (F : Finset ℂ) (c : SpectralCut (F : Set ℂ)) (m : ℂ → ℕ) :
    IsZetaRegularizable c m :=
  ⟨_, Regularization.ofFinite_onHalfPlane F c m⟩

end HalfPlane

end RegDet

end WeilRH
