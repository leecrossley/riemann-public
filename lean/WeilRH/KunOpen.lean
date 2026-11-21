/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Spectral

/-!
# `prop:kun-open`: the alternating spectral divisor of an exact sequence

Round 67 formalization of `latex/notes.tex`, `prop:kun-open` (claim C11).

An exact sequence of spectral cores
`0 → E⁰ → F⁰ → G⁰ → E¹ → F¹ → G¹ → E² → F² → 0`
with linear maps commuting with the generators satisfies, coefficient by coefficient,
`Σⱼ (-1)ʲ Sp(Eʲ) = Σⱼ (-1)ʲ Sp(Fʲ) - Σ_{j ≤ 1} (-1)ʲ Sp(Gʲ)`.
The spectral divisor `Sp(V)` of a spectral core is `ρ ↦ mult Θ ρ = dim V_{Θ∼ρ}`
(`def:spectral-core` (c)), so equality of divisors is equality of these functions.

The proof is the manuscript's: an intertwining map sends `V_{Θ∼λ}` into `W_{Θ∼λ}`
(`map_maxGenEigenspace_le`), and the restriction of an exact sequence to the generalized
`λ`-eigenspaces is again exact (`range_restrict_eq_ker_restrict`), because a preimage can be
replaced by its `λ`-component (`exists_mem_maxGenEigenspace_of_map_eq`). The alternating sum of
the dimensions of an exact sequence of finite-dimensional spaces vanishes (`euler_eight`).

## Main results

* `WeilRH.KunOpen.KunSeq`: the data of the proposition.
* `WeilRH.KunOpen.KunSeq.altDiv_eq` (`prop:kun-open`, display).
* `WeilRH.KunOpen.KunSeq.altDiv_eq_of_same` (`prop:kun-open`, "same alternating divisor").
* `WeilRH.KunOpen.KunSeq.mult_E0_of_injective`, `KunSeq.mult_E0_of_zero`
  (`prop:kun-open`, `Sp(E⁰) = 0` in the first case and `[0]` in the second).
-/

open Module

namespace WeilRH.KunOpen

open WeilRH.Spectral

section Restrict

variable {U V W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- A linear map intertwining the generators sends `V_{Θ∼λ}` into `W_{Θ∼λ}`. -/
lemma mapsTo_maxGenEigenspace {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (lam : ℂ) :
    ∀ x ∈ ΘV.maxGenEigenspace lam, f x ∈ ΘW.maxGenEigenspace lam := fun x hx =>
  Module.End.map_genEigenspace_le f hf lam ⊤ ⟨x, hx, rfl⟩

/-- If `V` is spanned by its generalized eigenspaces and `f` intertwines the generators, every
`w ∈ W_{Θ∼λ} ∩ range f` has a preimage in `V_{Θ∼λ}`. -/
lemma exists_mem_maxGenEigenspace_of_map_eq {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}
    (f : V →ₗ[ℂ] W) (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (hV : ⨆ μ, ΘV.maxGenEigenspace μ = ⊤) {lam : ℂ}
    {w : W} (hw : w ∈ ΘW.maxGenEigenspace lam) (v : V) (hv : f v = w) :
    ∃ a ∈ ΘV.maxGenEigenspace lam, f a = w := by
  have htop : v ∈ ΘV.maxGenEigenspace lam ⊔ ⨆ (μ) (_ : μ ≠ lam), ΘV.maxGenEigenspace μ := by
    rw [← iSup_split_single (fun μ => ΘV.maxGenEigenspace μ) lam, hV]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 htop
  refine ⟨a, ha, ?_⟩
  have hfb : f b ∈ ⨆ (μ) (_ : μ ≠ lam), ΘW.maxGenEigenspace μ := by
    have hmap : (⨆ (μ) (_ : μ ≠ lam), ΘV.maxGenEigenspace μ).map f ≤
        ⨆ (μ) (_ : μ ≠ lam), ΘW.maxGenEigenspace μ := by
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun μ _ => Module.End.map_genEigenspace_le f hf μ ⊤
    exact hmap ⟨b, hb, rfl⟩
  have hfb' : f b ∈ ΘW.maxGenEigenspace lam := by
    have : f b = w - f a := by rw [← hv, map_add]; abel
    rw [this]
    exact sub_mem hw (mapsTo_maxGenEigenspace f hf lam a ha)
  have h0 : f b = 0 :=
    (Submodule.disjoint_def.1 (ΘW.independent_maxGenEigenspace lam)) _ hfb' hfb
  rw [← hv, map_add, h0, add_zero]

/-- The restriction of `f` to generalized `λ`-eigenspaces. -/
noncomputable def res {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (lam : ℂ) :
    ΘV.maxGenEigenspace lam →ₗ[ℂ] ΘW.maxGenEigenspace lam :=
  f.restrict (mapsTo_maxGenEigenspace f hf lam)

@[simp] lemma res_apply {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (lam : ℂ) (x : ΘV.maxGenEigenspace lam) :
    (res f hf lam x : W) = f x := rfl

lemma res_injective {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (lam : ℂ) (hinj : Function.Injective f) :
    Function.Injective (res f hf lam) := fun x y h =>
  Subtype.ext (hinj (by simpa using congrArg Subtype.val h))

lemma res_surjective {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : ΘW ∘ₗ f = f ∘ₗ ΘV) (hV : ⨆ μ, ΘV.maxGenEigenspace μ = ⊤) (lam : ℂ)
    (hsurj : Function.Surjective f) : Function.Surjective (res f hf lam) := by
  rintro ⟨w, hw⟩
  obtain ⟨v, hv⟩ := hsurj w
  obtain ⟨a, ha, hfa⟩ := exists_mem_maxGenEigenspace_of_map_eq f hf hV hw v hv
  exact ⟨⟨a, ha⟩, Subtype.ext hfa⟩

/-- Exactness is preserved by restriction to the generalized `λ`-eigenspaces. -/
lemma range_res_eq_ker_res {ΘU : Module.End ℂ U} {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}
    (f : U →ₗ[ℂ] V) (g : V →ₗ[ℂ] W) (hf : ΘV ∘ₗ f = f ∘ₗ ΘU) (hg : ΘW ∘ₗ g = g ∘ₗ ΘV)
    (hU : ⨆ μ, ΘU.maxGenEigenspace μ = ⊤) (hex : LinearMap.range f = LinearMap.ker g)
    (lam : ℂ) : LinearMap.range (res f hf lam) = LinearMap.ker (res g hg lam) := by
  ext ⟨v, hv⟩
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨u, hu⟩, h⟩
    have hv' : v ∈ LinearMap.range f := ⟨u, by simpa using congrArg Subtype.val h⟩
    rw [hex] at hv'
    exact Subtype.ext (by simpa using hv')
  · intro h
    have hv' : v ∈ LinearMap.ker g := by simpa using congrArg Subtype.val h
    rw [← hex] at hv'
    obtain ⟨u, hu⟩ := hv'
    obtain ⟨a, ha, hfa⟩ := exists_mem_maxGenEigenspace_of_map_eq f hf hU hv u hu
    exact ⟨⟨a, ha⟩, Subtype.ext hfa⟩

end Restrict

section Euler

variable {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : Type*}
  [AddCommGroup X₀] [Module ℂ X₀] [FiniteDimensional ℂ X₀]
  [AddCommGroup X₁] [Module ℂ X₁] [FiniteDimensional ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂] [FiniteDimensional ℂ X₂]
  [AddCommGroup X₃] [Module ℂ X₃] [FiniteDimensional ℂ X₃]
  [AddCommGroup X₄] [Module ℂ X₄] [FiniteDimensional ℂ X₄]
  [AddCommGroup X₅] [Module ℂ X₅] [FiniteDimensional ℂ X₅]
  [AddCommGroup X₆] [Module ℂ X₆] [FiniteDimensional ℂ X₆]
  [AddCommGroup X₇] [Module ℂ X₇] [FiniteDimensional ℂ X₇]

omit [FiniteDimensional ℂ X₇] in
/-- The alternating sum of the dimensions of an exact sequence
`0 → X₀ → X₁ → ⋯ → X₇ → 0` of finite-dimensional spaces vanishes. -/
theorem euler_eight (f₀ : X₀ →ₗ[ℂ] X₁) (f₁ : X₁ →ₗ[ℂ] X₂) (f₂ : X₂ →ₗ[ℂ] X₃)
    (f₃ : X₃ →ₗ[ℂ] X₄) (f₄ : X₄ →ₗ[ℂ] X₅) (f₅ : X₅ →ₗ[ℂ] X₆) (f₆ : X₆ →ₗ[ℂ] X₇)
    (h₀ : Function.Injective f₀) (h₁ : LinearMap.range f₀ = LinearMap.ker f₁)
    (h₂ : LinearMap.range f₁ = LinearMap.ker f₂) (h₃ : LinearMap.range f₂ = LinearMap.ker f₃)
    (h₄ : LinearMap.range f₃ = LinearMap.ker f₄) (h₅ : LinearMap.range f₄ = LinearMap.ker f₅)
    (h₆ : LinearMap.range f₅ = LinearMap.ker f₆) (h₇ : Function.Surjective f₆) :
    (finrank ℂ X₀ : ℤ) - finrank ℂ X₁ + finrank ℂ X₂ - finrank ℂ X₃ + finrank ℂ X₄
      - finrank ℂ X₅ + finrank ℂ X₆ - finrank ℂ X₇ = 0 := by
  have r₀ := f₀.finrank_range_add_finrank_ker
  have r₁ := f₁.finrank_range_add_finrank_ker
  have r₂ := f₂.finrank_range_add_finrank_ker
  have r₃ := f₃.finrank_range_add_finrank_ker
  have r₄ := f₄.finrank_range_add_finrank_ker
  have r₅ := f₅.finrank_range_add_finrank_ker
  have r₆ := f₆.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.2 h₀, finrank_bot] at r₀
  rw [← h₁] at r₁; rw [← h₂] at r₂; rw [← h₃] at r₃; rw [← h₄] at r₄; rw [← h₅] at r₅
  rw [← h₆] at r₆
  have r₇ : finrank ℂ (LinearMap.range f₆) = finrank ℂ X₇ := by
    rw [LinearMap.range_eq_top.2 h₇, finrank_top]
  omega

end Euler

/-- The data of `prop:kun-open`: an exact sequence
`0 → E⁰ → F⁰ → G⁰ → E¹ → F¹ → G¹ → E² → F² → 0` of spectral cores (generators `θ`) and linear
maps commuting with the generators. -/
structure KunSeq (E₀ F₀ G₀ E₁ F₁ G₁ E₂ F₂ : Type*)
    [AddCommGroup E₀] [Module ℂ E₀] [AddCommGroup F₀] [Module ℂ F₀]
    [AddCommGroup G₀] [Module ℂ G₀] [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup F₁] [Module ℂ F₁] [AddCommGroup G₁] [Module ℂ G₁]
    [AddCommGroup E₂] [Module ℂ E₂] [AddCommGroup F₂] [Module ℂ F₂] where
  θE₀ : Module.End ℂ E₀
  θF₀ : Module.End ℂ F₀
  θG₀ : Module.End ℂ G₀
  θE₁ : Module.End ℂ E₁
  θF₁ : Module.End ℂ F₁
  θG₁ : Module.End ℂ G₁
  θE₂ : Module.End ℂ E₂
  θF₂ : Module.End ℂ F₂
  a₀ : E₀ →ₗ[ℂ] F₀
  b₀ : F₀ →ₗ[ℂ] G₀
  c₀ : G₀ →ₗ[ℂ] E₁
  a₁ : E₁ →ₗ[ℂ] F₁
  b₁ : F₁ →ₗ[ℂ] G₁
  c₁ : G₁ →ₗ[ℂ] E₂
  a₂ : E₂ →ₗ[ℂ] F₂
  comm_a₀ : θF₀ ∘ₗ a₀ = a₀ ∘ₗ θE₀
  comm_b₀ : θG₀ ∘ₗ b₀ = b₀ ∘ₗ θF₀
  comm_c₀ : θE₁ ∘ₗ c₀ = c₀ ∘ₗ θG₀
  comm_a₁ : θF₁ ∘ₗ a₁ = a₁ ∘ₗ θE₁
  comm_b₁ : θG₁ ∘ₗ b₁ = b₁ ∘ₗ θF₁
  comm_c₁ : θE₂ ∘ₗ c₁ = c₁ ∘ₗ θG₁
  comm_a₂ : θF₂ ∘ₗ a₂ = a₂ ∘ₗ θE₂
  core_E₀ : SpectralCore θE₀
  core_F₀ : SpectralCore θF₀
  core_G₀ : SpectralCore θG₀
  core_E₁ : SpectralCore θE₁
  core_F₁ : SpectralCore θF₁
  core_G₁ : SpectralCore θG₁
  core_E₂ : SpectralCore θE₂
  core_F₂ : SpectralCore θF₂
  inj_a₀ : Function.Injective a₀
  exact_F₀ : LinearMap.range a₀ = LinearMap.ker b₀
  exact_G₀ : LinearMap.range b₀ = LinearMap.ker c₀
  exact_E₁ : LinearMap.range c₀ = LinearMap.ker a₁
  exact_F₁ : LinearMap.range a₁ = LinearMap.ker b₁
  exact_G₁ : LinearMap.range b₁ = LinearMap.ker c₁
  exact_E₂ : LinearMap.range c₁ = LinearMap.ker a₂
  surj_a₂ : Function.Surjective a₂

namespace KunSeq

variable {E₀ F₀ G₀ E₁ F₁ G₁ E₂ F₂ : Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [AddCommGroup F₀] [Module ℂ F₀]
  [AddCommGroup G₀] [Module ℂ G₀] [AddCommGroup E₁] [Module ℂ E₁]
  [AddCommGroup F₁] [Module ℂ F₁] [AddCommGroup G₁] [Module ℂ G₁]
  [AddCommGroup E₂] [Module ℂ E₂] [AddCommGroup F₂] [Module ℂ F₂]

/-- **`prop:kun-open`** (display). For every `λ ∈ ℂ`,
`Σⱼ (-1)ʲ m_{Eʲ}(λ) = Σⱼ (-1)ʲ m_{Fʲ}(λ) - Σ_{j ≤ 1} (-1)ʲ m_{Gʲ}(λ)`: the alternating spectral
divisors satisfy the identity coefficient by coefficient. -/
theorem altDiv_eq (S : KunSeq E₀ F₀ G₀ E₁ F₁ G₁ E₂ F₂) (lam : ℂ) :
    ((mult S.θE₀ lam : ℤ) - mult S.θE₁ lam + mult S.θE₂ lam) =
      ((mult S.θF₀ lam : ℤ) - mult S.θF₁ lam + mult S.θF₂ lam) -
        ((mult S.θG₀ lam : ℤ) - mult S.θG₁ lam) := by
  have := S.core_E₀.finiteDimensional lam
  have := S.core_F₀.finiteDimensional lam
  have := S.core_G₀.finiteDimensional lam
  have := S.core_E₁.finiteDimensional lam
  have := S.core_F₁.finiteDimensional lam
  have := S.core_G₁.finiteDimensional lam
  have := S.core_E₂.finiteDimensional lam
  have := S.core_F₂.finiteDimensional lam
  have h := euler_eight (res S.a₀ S.comm_a₀ lam) (res S.b₀ S.comm_b₀ lam)
    (res S.c₀ S.comm_c₀ lam) (res S.a₁ S.comm_a₁ lam) (res S.b₁ S.comm_b₁ lam)
    (res S.c₁ S.comm_c₁ lam) (res S.a₂ S.comm_a₂ lam)
    (res_injective _ _ lam S.inj_a₀)
    (range_res_eq_ker_res _ _ _ _ S.core_E₀.iSup_eq_top S.exact_F₀ lam)
    (range_res_eq_ker_res _ _ _ _ S.core_F₀.iSup_eq_top S.exact_G₀ lam)
    (range_res_eq_ker_res _ _ _ _ S.core_G₀.iSup_eq_top S.exact_E₁ lam)
    (range_res_eq_ker_res _ _ _ _ S.core_E₁.iSup_eq_top S.exact_F₁ lam)
    (range_res_eq_ker_res _ _ _ _ S.core_F₁.iSup_eq_top S.exact_G₁ lam)
    (range_res_eq_ker_res _ _ _ _ S.core_G₁.iSup_eq_top S.exact_E₂ lam)
    (res_surjective _ _ S.core_E₂.iSup_eq_top lam S.surj_a₂)
  simp only [mult]
  linarith

/-- **`prop:kun-open`** ("same alternating divisor"). Two such sequences with the same spaces
`Fʲ`, `Gʲ` and the same generators on them have the same alternating divisor
`Σⱼ (-1)ʲ Sp(Eʲ)`, whatever the maps. -/
theorem altDiv_eq_of_same {E₀' E₁' E₂' : Type*} [AddCommGroup E₀'] [Module ℂ E₀']
    [AddCommGroup E₁'] [Module ℂ E₁'] [AddCommGroup E₂'] [Module ℂ E₂']
    (S : KunSeq E₀ F₀ G₀ E₁ F₁ G₁ E₂ F₂) (T : KunSeq E₀' F₀ G₀ E₁' F₁ G₁ E₂' F₂)
    (hF₀ : S.θF₀ = T.θF₀) (hF₁ : S.θF₁ = T.θF₁) (hF₂ : S.θF₂ = T.θF₂)
    (hG₀ : S.θG₀ = T.θG₀) (hG₁ : S.θG₁ = T.θG₁) (lam : ℂ) :
    ((mult S.θE₀ lam : ℤ) - mult S.θE₁ lam + mult S.θE₂ lam) =
      ((mult T.θE₀ lam : ℤ) - mult T.θE₁ lam + mult T.θE₂ lam) := by
  rw [S.altDiv_eq, T.altDiv_eq, hF₀, hF₁, hF₂, hG₀, hG₁]

/-- **`prop:kun-open`** (first case). If `F⁰ → G⁰` is injective then `Sp(E⁰) = 0`. -/
theorem mult_E0_of_injective (S : KunSeq E₀ F₀ G₀ E₁ F₁ G₁ E₂ F₂)
    (hb : Function.Injective S.b₀) (lam : ℂ) : mult S.θE₀ lam = 0 := by
  have hE : ∀ x : E₀, x = 0 := by
    intro x
    have : S.a₀ x ∈ LinearMap.ker S.b₀ := S.exact_F₀ ▸ ⟨x, rfl⟩
    rw [LinearMap.ker_eq_bot.2 hb, Submodule.mem_bot] at this
    exact S.inj_a₀ (by rw [this, map_zero])
  have : Subsingleton E₀ := ⟨fun x y => by rw [hE x, hE y]⟩
  exact finrank_zero_of_subsingleton

/-- **`prop:kun-open`** (second case). If `F⁰ = ℂ` with generator `0` and `F⁰ → G⁰` is zero, then
`Sp(E⁰) = [0]`: `m_{E⁰}(0) = 1` and `m_{E⁰}(λ) = 0` for `λ ≠ 0`. -/
theorem mult_E0_of_zero {G₀ E₁ F₁ G₁ E₂ F₂ : Type*}
    [AddCommGroup G₀] [Module ℂ G₀] [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup F₁] [Module ℂ F₁] [AddCommGroup G₁] [Module ℂ G₁]
    [AddCommGroup E₂] [Module ℂ E₂] [AddCommGroup F₂] [Module ℂ F₂]
    (S : KunSeq E₀ ℂ G₀ E₁ F₁ G₁ E₂ F₂) (hθ : S.θF₀ = 0) (hb : S.b₀ = 0) (lam : ℂ) :
    mult S.θE₀ lam = if lam = 0 then 1 else 0 := by
  -- `a₀ : E⁰ → ℂ` is an isomorphism intertwining `θ_{E⁰}` with `0`
  have hsurj : Function.Surjective S.a₀ := by
    rw [← LinearMap.range_eq_top, S.exact_F₀, hb, LinearMap.ker_zero]
  let e : E₀ ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective S.a₀ ⟨S.inj_a₀, hsurj⟩
  have he : ∀ x, S.θF₀ (e x) = e (S.θE₀ x) := fun x =>
    (LinearMap.congr_fun S.comm_a₀ x : _)
  have hmap := map_maxGenEigenspace_of_equiv e he lam
  have hrk : mult S.θE₀ lam = finrank ℂ (S.θF₀.maxGenEigenspace lam) := by
    rw [mult, ← hmap]
    exact (e.submoduleMap _).finrank_eq
  rw [hrk, hθ]
  split_ifs with h
  · subst h
    have : (0 : Module.End ℂ ℂ).maxGenEigenspace 0 = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp⟩
    rw [this, finrank_top, finrank_self]
  · have : (0 : Module.End ℂ ℂ).maxGenEigenspace lam = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
      have : ((0 : Module.End ℂ ℂ) - lam • 1) ^ k = (-lam) ^ k • (1 : Module.End ℂ ℂ) := by
        rw [zero_sub, ← neg_smul, smul_pow, one_pow]
      rw [this, LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero] at hk
      rcases hk with hk | hk
      · exact absurd (pow_eq_zero_iff'.1 hk).1 (neg_ne_zero.2 h)
      · exact (Submodule.mem_bot ℂ).2 hk
    rw [this, finrank_bot]

end KunSeq

end WeilRH.KunOpen
