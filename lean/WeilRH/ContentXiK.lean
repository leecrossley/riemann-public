import WeilRH.XiK
import WeilRH.TrivialModel

/-!
# `Σ_K = div ξ_K` and `prop:content` (i), (iv) (roadmap D5)

Round 51 of `lean/ROADMAP-arakelov.md`. Source: `latex/notes.tex`, `prop:content`
(`Σ_K = div ξ_K`): (i) the trivial model with spectrum `Σ_K` satisfies AW1, AW2, AW3 for
`(Λ_K, 𝟙)` unconditionally; (iv) some Weil datum satisfies AW1–AW4 iff every zero of `ξ_K` has
real part `1/2`. Hecke's simple poles are the hypothesis `DedekindContinuation.SimplePoles`
(round 50, `XiK.lean`).

## Generic part: divisors of symmetric entire functions

For an entire `f : ℂ → ℂ` with `f (1 - s) = f s` that is not identically zero, write
`m σ = analyticOrderNatAt f σ`.

* `SymEntire.mult_one_sub`: `m (1 - σ) = m σ` (Mathlib `analyticOrderAt_comp_of_deriv_ne_zero`).
* `SymEntire.even_mult_half`: `m (1/2)` is even (the notes' "`t ↦ ξ_K(1/2 + t)` is even").
* `SymEntire.mult_pos_iff`: `0 < m σ ↔ f σ = 0` (identity theorem: the order is never `⊤`).
* `SymEntire.family`: a family `ρ : ι → ℂ` of designated zeros (`Re > 1/2`, or `Re = 1/2` and
  `Im > 0`, plus `m(1/2)/2` copies of `1/2`) such that the trivial model's
  `λ = (ρ_p, 1 - ρ_p)` lists `div f` with multiplicity:
  `SymEntire.card_fiber : #{i // lam ρ i = σ} = m σ`.
* `SymEntire.spectralCore`: the trivial model `Θ_1` for this family is a spectral core (finite
  multiplicities; no finite accumulation point, by Mathlib `preimage_zero_mem_codiscrete`).

## `prop:content`

* `content_free` (i): for every `K` with simple poles, the trivial model `TrivialModel.model ρ_K`
  is a degree-one Weil datum (AW1 derivation law `B_theta`, AW3 nondegeneracy `B_nondegenerate`),
  `(V^1, Θ_1)` is a spectral core, and `dim V^1_{Θ∼σ} = ord_σ ξ_K` for every `σ`
  (`Sp_1 = Σ_K`, the degree-one form of AW2).
* `content_iff` (iv): a positive degree-one Weil datum of type `(1, 0)` with `Sp_1 = Σ_K` exists
  iff every zero of `ξ_K` has real part `1/2` (GRH for `ζ_K`).

## Fidelity

Degree-one slice only (as `TrivialModel`): AW2 is encoded as `Sp_1 = div ξ_K` with multiplicities;
with the endpoints `Sp_0 = {0}`, `Sp_2 = {1}` this is the divisor of `Λ_K`
(`SimplePoles.xi_eq_zero_iff`). "Weil datum on `X̄_K`" in (iv) is a `WeightedStarDatum 1 0 1`
with that spectrum; degrees 0 and 2 are `TrivialModelFull`. The Euler-product nonvanishing of
`ξ_K` on `Re s > 1` is not needed here and remains blocked (Mathlib v4.34.1).
-/

open Complex Filter Topology

namespace WeilRH.SymEntire

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsym : ∀ s, f (1 - s) = f s)
  {z₀ : ℂ} (hz₀ : f z₀ ≠ 0)

include hf in
lemma analyticAt (σ : ℂ) : AnalyticAt ℂ f σ := hf.analyticAt σ

include hf hz₀ in
/-- The analytic order is finite everywhere (identity theorem). -/
lemma order_ne_top (σ : ℂ) : analyticOrderAt f σ ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ f Set.univ := fun s _ => hf.analyticAt s
  refine hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ z₀)
    (Set.mem_univ σ) ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr hz₀)]
  exact ENat.zero_ne_top

include hf hz₀ in
/-- `0 < ord_σ f ↔ f σ = 0`. -/
lemma mult_pos_iff (σ : ℂ) : 0 < analyticOrderNatAt f σ ↔ f σ = 0 := by
  rw [analyticOrderNatAt, Nat.pos_iff_ne_zero, Ne, ENat.toNat_eq_zero,
    or_iff_left (order_ne_top hf hz₀ σ), analyticOrderAt_eq_zero]
  simp [hf.analyticAt σ]

include hsym in
/-- `ord_{1 - σ} f = ord_σ f`. -/
lemma mult_one_sub (σ : ℂ) : analyticOrderNatAt f (1 - σ) = analyticOrderNatAt f σ := by
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) σ := by fun_prop
  have hd : deriv (fun s : ℂ => 1 - s) σ ≠ 0 := by
    rw [deriv_const_sub, deriv_id'']; norm_num
  have hcomp : f ∘ (fun s : ℂ => 1 - s) = f := funext hsym
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg hd
  rw [hcomp] at this
  simp only [analyticOrderNatAt, ← this]

include hf hsym hz₀ in
/-- `ord_{1/2} f` is even. -/
lemma even_mult_half : Even (analyticOrderNatAt f (1 / 2)) := by
  set n := analyticOrderNatAt f (1 / 2) with hn
  have hfin : analyticOrderAt f (1 / 2) = n := by
    rw [hn, analyticOrderNatAt, ENat.natCast_toNat (order_ne_top hf hz₀ _)]
  obtain ⟨g, hga, hg0, hfg⟩ := (hf.analyticAt (1 / 2)).analyticOrderAt_eq_natCast.1 hfin
  have ht : Tendsto (fun s : ℂ => 1 - s) (𝓝 (1 / 2)) (𝓝 (1 / 2)) := by
    have : Continuous (fun s : ℂ => 1 - s) := by fun_prop
    have h := this.tendsto (1 / 2)
    rwa [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at h
  have hfg' := ht.eventually hfg
  -- eventually `(s - 1/2)^n g s = (s - 1/2)^n ((-1)^n g (1 - s))`
  have heq : ∀ᶠ s in 𝓝 (1 / 2 : ℂ),
      (s - 1 / 2) ^ n * g s = (s - 1 / 2) ^ n * ((-1) ^ n * g (1 - s)) := by
    filter_upwards [hfg, hfg'] with s h1 h2
    simp only [smul_eq_mul] at h1 h2
    rw [hsym] at h2
    rw [← h1, h2, show (1 - s - 1 / 2 : ℂ) = -(s - 1 / 2) by ring, neg_pow]
    ring
  have hpunct : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), g s = (-1) ^ n * g (1 - s) := by
    filter_upwards [nhdsWithin_le_nhds heq, self_mem_nhdsWithin] with s h hs
    have hs' : (s - 1 / 2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hs)
    exact mul_left_cancel₀ hs' h
  have hc1 : Tendsto g (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (g (1 / 2))) :=
    hga.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun s => (-1) ^ n * g (1 - s)) (𝓝[≠] (1 / 2 : ℂ))
      (𝓝 ((-1) ^ n * g (1 / 2))) := by
    have hgc : ContinuousAt (fun s : ℂ => g (1 - s)) (1 / 2) := by
      have hg' : ContinuousAt g (1 - 1 / 2) := by
        rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]; exact hga.continuousAt
      exact hg'.comp (by fun_prop)
    have := (hgc.tendsto.const_mul ((-1 : ℂ) ^ n)).mono_left (nhdsWithin_le_nhds (s := {1 / 2}ᶜ))
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num] at this
    exact this
  have hlim : g (1 / 2) = (-1) ^ n * g (1 / 2) :=
    tendsto_nhds_unique hc1 (hc2.congr' (hpunct.mono fun s h => h.symm))
  have hpow : ((-1 : ℂ)) ^ n = 1 := by
    have := mul_right_cancel₀ hg0 (hlim.symm.trans (one_mul _).symm)
    exact this
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 hpow

/-! ### The designated family -/

/-- Designated half of the divisor: `Re σ > 1/2`, or `Re σ = 1/2 ∧ Im σ > 0`, or `σ = 1/2`. -/
def Desig (σ : ℂ) : Prop := 1 / 2 < σ.re ∨ (σ.re = 1 / 2 ∧ 0 < σ.im) ∨ σ = 1 / 2

variable (f) in
/-- Number of copies of a designated point: `m σ`, except `m (1/2) / 2` at the centre. -/
noncomputable def copies (σ : ℂ) : ℕ :=
  if σ = 1 / 2 then analyticOrderNatAt f σ / 2 else analyticOrderNatAt f σ

variable (f) in
/-- Index set: every designated point `σ`, repeated `copies σ` times. -/
abbrev Idx : Type := Σ σ : {σ : ℂ // Desig σ}, Fin (copies f σ.1)

variable (f) in
/-- The family `ρ`: an index `⟨σ, k⟩` maps to `σ`. -/
def family (i : Idx f) : ℂ := i.1.1

lemma desig_one_sub_of_not {σ : ℂ} (h : ¬ Desig σ) : Desig (1 - σ) ∧ 1 - σ ≠ 1 / 2 := by
  unfold Desig at *
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  have hre : (1 - σ).re = 1 - σ.re := by simp
  have him : (1 - σ).im = -σ.im := by simp
  refine ⟨?_, ?_⟩
  · rcases h1.lt_or_eq with hlt | heq
    · left; rw [hre]; linarith
    · right; left
      refine ⟨by rw [hre, heq]; norm_num, ?_⟩
      rw [him]
      have hne : σ.im ≠ 0 := by
        intro h0; apply h3; apply Complex.ext <;> simp [heq, h0]
      have := h2 heq
      exact neg_pos.2 (lt_of_le_of_ne this hne)
  · intro h; apply h3; linear_combination -h

lemma not_desig_one_sub {σ : ℂ} (h : Desig σ) (hne : σ ≠ 1 / 2) : ¬ Desig (1 - σ) := by
  unfold Desig at *
  have hre : (1 - σ).re = 1 - σ.re := by simp
  have him : (1 - σ).im = -σ.im := by simp
  rintro (h' | ⟨h'1, h'2⟩ | h')
  · rcases h with h | ⟨h1, _⟩ | h
    · rw [hre] at h'; linarith
    · rw [hre, h1] at h'; norm_num at h'
    · exact hne h
  · rcases h with h | ⟨h1, h2⟩ | h
    · rw [hre] at h'1; linarith
    · rw [him] at h'2; linarith
    · exact hne h
  · apply hne; linear_combination -h'

/-- Fibres of `family` over a designated point. -/
def fiberEquiv {σ : ℂ} (h : Desig σ) :
    {i : Idx f // family f i = σ} ≃ Fin (copies f σ) :=
  (Equiv.subtypeEquivRight fun i => by
    change i.1.1 = σ ↔ i.1 = ⟨σ, h⟩
    exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩).trans
    (Equiv.sigmaSubtype (⟨σ, h⟩ : {σ : ℂ // Desig σ}))

lemma fiber_isEmpty {σ : ℂ} (h : ¬ Desig σ) : IsEmpty {i : Idx f // family f i = σ} :=
  ⟨fun i => h (i.2 ▸ i.1.1.2)⟩

open Classical in
/-- `#{i // ρ_i = σ}`: `copies σ` on designated points, `0` elsewhere. -/
lemma card_family_fiber (σ : ℂ) :
    Cardinal.mk {i : Idx f // family f i = σ} = if Desig σ then (copies f σ : Cardinal) else 0 := by
  split_ifs with h
  · rw [Cardinal.mk_congr (fiberEquiv h), Cardinal.mk_fin]
  · have := fiber_isEmpty (f := f) h
    exact Cardinal.mk_eq_zero _

/-- The trivial model's fibre splits into the `true` and `false` copies. -/
def lamFiberEquiv (σ : ℂ) :
    {i : Idx f × Bool // TrivialModel.lam (family f) i = σ} ≃
      {i : Idx f // 1 - family f i = σ} ⊕ {i : Idx f // family f i = σ} :=
  (Equiv.subtypeEquiv (q := fun s : Idx f ⊕ Idx f =>
      Sum.elim (fun i => 1 - family f i = σ) (fun i => family f i = σ) s)
    ((Equiv.prodComm _ _).trans (Equiv.boolProdEquivSum _))
    (by rintro ⟨i, _ | _⟩ <;> simp [TrivialModel.lam])).trans Equiv.subtypeSum

include hf hsym hz₀ in
/-- **`Σ = div f` with multiplicity**: the trivial model built on `family f` lists every `σ`
exactly `ord_σ f` times. -/
theorem card_fiber (σ : ℂ) :
    Cardinal.mk {i : Idx f × Bool // TrivialModel.lam (family f) i = σ} =
      analyticOrderNatAt f σ := by
  rw [Cardinal.mk_congr (lamFiberEquiv σ), Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  have e1 : Cardinal.mk {i : Idx f // 1 - family f i = σ} =
      Cardinal.mk {i : Idx f // family f i = 1 - σ} :=
    Cardinal.mk_congr (Equiv.subtypeEquivRight fun i => by
      constructor <;> intro h <;> linear_combination -h)
  rw [e1, card_family_fiber, card_family_fiber]
  have hev := even_mult_half hf hsym hz₀
  by_cases hhalf : σ = 1 / 2
  · subst hhalf
    have hd : Desig (1 / 2 : ℂ) := Or.inr (Or.inr rfl)
    have h1 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h1]
    simp only [hd, ↓reduceIte, copies]
    obtain ⟨k, hk⟩ := hev
    rw [hk, show k + k = 2 * k by ring, Nat.mul_div_cancel_left _ two_pos]
    push_cast; ring
  by_cases hd : Desig σ
  · have h2 : σ ≠ 2⁻¹ := fun h => hhalf (by rw [h]; norm_num)
    simp [not_desig_one_sub hd hhalf, hd, copies, h2]
  · obtain ⟨hd', hne'⟩ := desig_one_sub_of_not hd
    have h2 : 1 - σ ≠ 2⁻¹ := fun h => hne' (by rw [h]; norm_num)
    simp [hd', hd, copies, h2, mult_one_sub hsym]

include hf hsym hz₀ in
/-- Every value of `λ` is a zero of `f`. -/
lemma lam_zero (i : Idx f × Bool) : f (TrivialModel.lam (family f) i) = 0 := by
  have h := card_fiber hf hsym hz₀ (TrivialModel.lam (family f) i)
  have hne : Cardinal.mk {j : Idx f × Bool // TrivialModel.lam (family f) j =
      TrivialModel.lam (family f) i} ≠ 0 := Cardinal.mk_ne_zero_iff.2 ⟨⟨i, rfl⟩⟩
  rw [h] at hne
  exact (mult_pos_iff hf hz₀ _).1 (Nat.pos_of_ne_zero (by exact_mod_cast hne))

include hf hsym hz₀ in
/-- **Spectral core**: finite multiplicities, and the zero set of `f ≢ 0` has no finite
accumulation point (Mathlib `preimage_zero_mem_codiscrete`). -/
theorem spectralCore : WeilRH.Spectral.SpectralCore (TrivialModel.theta (family f)) := by
  refine TrivialModel.spectralCore_theta (family f) (fun σ => ?_) (fun z => ?_)
  · have hlt : Cardinal.mk {i : Idx f × Bool // TrivialModel.lam (family f) i = σ} <
        Cardinal.aleph0 := by
      rw [card_fiber hf hsym hz₀]; exact Cardinal.natCast_lt_aleph0
    exact Cardinal.lt_aleph0_iff_set_finite.1 hlt
  · have hA : AnalyticOnNhd ℂ f Set.univ := fun s _ => hf.analyticAt s
    have hcod := hA.preimage_zero_mem_codiscrete hz₀
    rw [mem_codiscrete_accPt] at hcod
    intro hacc
    apply hcod z
    refine Filter.NeBot.mono hacc (inf_le_inf_left _ (Filter.principal_mono.2 ?_))
    rintro _ ⟨i, rfl⟩
    simpa using lam_zero hf hsym hz₀ i

end WeilRH.SymEntire

namespace WeilRH

open NumberField

variable {K : Type} [Field K] [NumberField K] {C : DedekindContinuation K}
  (P : C.SimplePoles)

/-- The designated zero family of `ξ_K`. -/
noncomputable def xiFamily : SymEntire.Idx P.ξ → ℂ := SymEntire.family P.ξ

/-- **`prop:content` (i)** (degree one): the trivial model with spectrum `Σ_K = div ξ_K` is a
Weil datum of type `(1, 0)` (AW1: `B_theta`; AW3: `B_nondegenerate`, built into
`TrivialModel.model`), `(V^1, Θ_1)` is a spectral core, and `Sp_1 = Σ_K` with multiplicities. -/
theorem content_free :
    WeilRH.Spectral.SpectralCore (TrivialModel.theta (xiFamily P)) ∧
      ∀ σ, Module.rank ℂ ((TrivialModel.theta (xiFamily P)).maxGenEigenspace σ) =
        analyticOrderNatAt P.ξ σ := by
  refine ⟨SymEntire.spectralCore P.differentiable P.one_sub P.xi_one_ne_zero, fun σ => ?_⟩
  rw [TrivialModel.rank_maxGenEigenspace_theta]
  exact SymEntire.card_fiber P.differentiable P.one_sub P.xi_one_ne_zero σ

/-- **`prop:content` (iv)** (degree one): a positive Weil datum of type `(1, 0)` in degree one with
`Sp_1 = Σ_K = div ξ_K` (with multiplicities) exists iff every zero of `ξ_K` has real part `1/2`,
i.e. GRH for `ζ_K` (zeros of `ξ_K` = nontrivial zeros, `SimplePoles.xi_eq_zero_iff`). -/
theorem content_iff :
    (∃ (V W T : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W)
      (_ : Module ℂ W) (_ : AddCommGroup T) (_ : Module ℂ T)
      (D : WeightedStarDatum 1 0 1 V W T), D.IsPositive ∧
        ∀ σ, Module.rank ℂ (D.ΘV.maxGenEigenspace σ) = analyticOrderNatAt P.ξ σ) ↔
      ∀ ρ, P.ξ ρ = 0 → ρ.re = 1 / 2 := by
  have hcard : ∀ σ, Cardinal.mk {i // TrivialModel.lam (xiFamily P) i = σ} =
      analyticOrderNatAt P.ξ σ :=
    SymEntire.card_fiber P.differentiable P.one_sub P.xi_one_ne_zero
  have key := TrivialModel.exists_datum_iff (xiFamily P)
  simp_rw [show ∀ σ, Cardinal.mk {i // TrivialModel.lam (xiFamily P) i = σ} =
    (analyticOrderNatAt P.ξ σ : Cardinal) from hcard] at key
  rw [key]
  constructor
  · intro hline ρ hρ
    have hpos := (SymEntire.mult_pos_iff P.differentiable P.xi_one_ne_zero ρ).2 hρ
    have hne : Cardinal.mk {i : SymEntire.Idx P.ξ × Bool //
        TrivialModel.lam (xiFamily P) i = ρ} ≠ 0 := by
      rw [hcard]; exact_mod_cast hpos.ne'
    obtain ⟨⟨⟨p, b⟩, hp⟩⟩ := Cardinal.mk_ne_zero_iff.1 hne
    subst hp
    cases b
    · simp only [TrivialModel.lam, Bool.false_eq_true, ↓reduceIte, sub_re, one_re]
      rw [hline p]; norm_num
    · simp only [TrivialModel.lam, ↓reduceIte]; exact hline p
  · intro hz p
    exact hz _ (SymEntire.lam_zero P.differentiable P.one_sub P.xi_one_ne_zero (p, true))

end WeilRH
