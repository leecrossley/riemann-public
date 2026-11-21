/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.KunFq
import WeilRH.KunOpen

/-!
# `thm:kun-square` (iii)–(iv): the surface `H²` is not a spectral core

Round 67 formalization of `latex/notes.tex`, `thm:kun-square` (claims K-N1, K-N2), for abstract
spectral cores.

The surface datum of `def:kun-notation` is not modelled. Its only inputs used here are those of
`thm:kun-square` (i): a space `H` (the manuscript's `H²`) with generator `Θ_S` and an injective
map `κ : V ⊗ W → H` with `Θ_S κ = κ (Θ ⊗ 1 + 1 ⊗ Θ)` (`Spectral.tensorSum`). The manuscript's
`V = V_K`, `W = V_L` have spectra `Z(K)`, `Z(L)` (the zeros of `ξ_K`, `ξ_L`, by `thm:rh`); here
they are arbitrary spectral cores.

## Main results

* `not_finite_of_pairs_infinite`: if infinitely many pairs `(ρ, ρ') ∈ spec Θ_V × spec Θ_W` have
  `ρ + ρ' = λ`, the generalized `λ`-eigenspace of `Θ ⊗ 1 + 1 ⊗ Θ` is infinite-dimensional
  (README obligation 9: failure of the spectral-core condition on `V ⊗ W` for infinite sums).
* `not_spectralCore_of_inter_infinite` (`thm:kun-square` (iv)): if
  `{ρ ∈ spec Θ_V : 1 - ρ ∈ spec Θ_W}` (the manuscript's `Z(K) ∩ Z(L)`, using `ρ ↦ 1 - ρ`
  symmetry of `Z(L)`) is infinite, then `H_{Θ_S∼1}` is infinite-dimensional and `(H, Θ_S)` is
  not a spectral core.
* `not_spectralCore_self` (`thm:kun-square` (iv), `K = L`): the same when `V = W` and `spec Θ_V`
  is infinite and stable under `ρ ↦ 1 - ρ`.
* `add_mem_spec` and `exists_accPt_of_infinite_bounded` (`thm:kun-square` (iii), last step):
  `ρ + ρ'` lies in `spec Θ_S` for `ρ ∈ spec Θ_V`, `ρ' ∈ spec Θ_W`, and an infinite bounded set of
  such sums gives a finite accumulation point of `spec Θ_S`. The selection of the sums
  `ρ_k + 1 - ρ'_k` from the hypothesis on imaginary parts of zeros is not formalized.
-/

open Module TensorProduct

universe u

namespace WeilRH.KunSquare

open WeilRH.Spectral WeilRH.KunFq WeilRH.KunOpen

variable {V W : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}

/-- Infinitely many contributing pairs force an infinite-dimensional generalized eigenspace of
`Θ ⊗ 1 + 1 ⊗ Θ` (the spectral-core condition fails on `V ⊗ W`). -/
theorem not_finite_of_pairs_infinite (hV : SpectralCore ΘV) (hW : SpectralCore ΘW) (lam : ℂ)
    (hinf : (pairs ΘV ΘW lam).Infinite) :
    ¬ Module.Finite ℂ ((tensorSum ΘV ΘW).maxGenEigenspace lam) := by
  classical
  intro hfin
  set E := (tensorSum ΘV ΘW).maxGenEigenspace lam
  have := hV.finiteDimensional
  have := hW.finiteDimensional
  let f : {p : ℂ × ℂ // p.1 + p.2 = lam} → Submodule ℂ E := fun p =>
    (block ΘV ΘW p.1.1 p.1.2).comap E.subtype
  have hind : iSupIndep f :=
    (isInternal_block_maxGenEigenspace ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top lam).submodule_iSupIndep
  have hs : ∀ p : pairs ΘV ΘW lam, f ⟨p.1, p.2.1⟩ ≠ ⊥ := by
    rintro ⟨p, hsum, h1, h2⟩
    have hb : block ΘV ΘW p.1 p.2 ≠ ⊥ := block_ne_bot ΘV ΘW h1 h2
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hb
    have hle : x ∈ E := by
      have := block_le ΘV ΘW p.1 p.2 hx
      rwa [hsum] at this
    exact (Submodule.ne_bot_iff _).2 ⟨⟨x, hle⟩, hx, fun h => hx0 (congrArg Subtype.val h)⟩
  let := hind.fintypeNeBotOfFiniteDimensional
  have := hinf.to_subtype
  refine not_injective_infinite_finite
    (fun p : pairs ΘV ΘW lam => (⟨⟨p.1, p.2.1⟩, hs p⟩ : {i // f i ≠ ⊥})) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun x : {i // f i ≠ ⊥} => x.1.1) hab)

variable {H : Type*} [AddCommGroup H] [Module ℂ H] {ΘS : Module.End ℂ H}

/-- Transport along an injective intertwining `κ : V ⊗ W → H`. -/
theorem not_finite_of_pairs_infinite_of_inj (hV : SpectralCore ΘV) (hW : SpectralCore ΘW)
    (κ : V ⊗[ℂ] W →ₗ[ℂ] H) (hκ : Function.Injective κ)
    (hcomm : ΘS ∘ₗ κ = κ ∘ₗ tensorSum ΘV ΘW) (lam : ℂ) (hinf : (pairs ΘV ΘW lam).Infinite) :
    ¬ Module.Finite ℂ (ΘS.maxGenEigenspace lam) := by
  intro hfin
  exact not_finite_of_pairs_infinite hV hW lam hinf
    (Module.Finite.of_injective (res κ hcomm lam) (res_injective κ hcomm lam hκ))

/-- **`thm:kun-square` (iv)**. If `{ρ ∈ spec Θ_V : 1 - ρ ∈ spec Θ_W}` is infinite, then the
generalized eigenspace of `Θ_S` at `1` is infinite-dimensional, so `(H, Θ_S)` is not a spectral
core. -/
theorem not_spectralCore_of_inter_infinite (hV : SpectralCore ΘV) (hW : SpectralCore ΘW)
    (κ : V ⊗[ℂ] W →ₗ[ℂ] H) (hκ : Function.Injective κ)
    (hcomm : ΘS ∘ₗ κ = κ ∘ₗ tensorSum ΘV ΘW)
    (hinf : {ρ | ρ ∈ spec ΘV ∧ 1 - ρ ∈ spec ΘW}.Infinite) :
    ¬ Module.Finite ℂ (ΘS.maxGenEigenspace 1) ∧ ¬ SpectralCore ΘS := by
  have hp : (pairs ΘV ΘW 1).Infinite := by
    refine Set.Infinite.mono ?_ (hinf.image (f := fun ρ : ℂ => (ρ, 1 - ρ))
      (fun a _ b _ h => congrArg Prod.fst h))
    rintro _ ⟨ρ, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simp, h1, h2⟩
  have h := not_finite_of_pairs_infinite_of_inj hV hW κ hκ hcomm 1 hp
  exact ⟨h, fun hS => h (hS.finiteDimensional 1)⟩

/-- **`thm:kun-square` (iv)**, `K = L`: if `spec Θ_V` is infinite and stable under `ρ ↦ 1 - ρ`
(the functional equation, `prop:xiK`), the surface space is not a spectral core. -/
theorem not_spectralCore_self (hV : SpectralCore ΘV) (κ : V ⊗[ℂ] V →ₗ[ℂ] H)
    (hκ : Function.Injective κ) (hcomm : ΘS ∘ₗ κ = κ ∘ₗ tensorSum ΘV ΘV)
    (hsymm : ∀ ρ ∈ spec ΘV, 1 - ρ ∈ spec ΘV) (hinf : (spec ΘV).Infinite) :
    ¬ Module.Finite ℂ (ΘS.maxGenEigenspace 1) ∧ ¬ SpectralCore ΘS := by
  refine not_spectralCore_of_inter_infinite hV hV κ hκ hcomm ?_
  have : {ρ | ρ ∈ spec ΘV ∧ 1 - ρ ∈ spec ΘV} = spec ΘV := by
    ext ρ; exact ⟨fun h => h.1, fun h => ⟨h, hsymm ρ h⟩⟩
  rw [this]; exact hinf

/-- `thm:kun-square` (iii), the eigenvalues: `ρ + ρ'` is an eigenvalue of `Θ_S` for
`ρ ∈ spec Θ_V`, `ρ' ∈ spec Θ_W`. -/
theorem add_mem_spec (hV : SpectralCore ΘV) (hW : SpectralCore ΘW)
    (κ : V ⊗[ℂ] W →ₗ[ℂ] H) (hκ : Function.Injective κ)
    (hcomm : ΘS ∘ₗ κ = κ ∘ₗ tensorSum ΘV ΘW) {ρ ρ' : ℂ} (h1 : ρ ∈ spec ΘV)
    (h2 : ρ' ∈ spec ΘW) : ρ + ρ' ∈ spec ΘS := by
  have := hV.finiteDimensional
  have := hW.finiteDimensional
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (block_ne_bot ΘV ΘW h1 h2)
  have hxE := block_le ΘV ΘW ρ ρ' hx
  intro hbot
  have : κ x ∈ ΘS.maxGenEigenspace (ρ + ρ') := mapsTo_maxGenEigenspace κ hcomm _ x hxE
  rw [hbot, Submodule.mem_bot] at this
  exact hx0 (hκ (by rw [this, map_zero]))

/-- `thm:kun-square` (iii), the last step: an infinite bounded set of sums `ρ + ρ'` gives a
finite accumulation point of `spec Θ_S`. -/
theorem exists_accPt_of_infinite_bounded (hV : SpectralCore ΘV) (hW : SpectralCore ΘW)
    (κ : V ⊗[ℂ] W →ₗ[ℂ] H) (hκ : Function.Injective κ)
    (hcomm : ΘS ∘ₗ κ = κ ∘ₗ tensorSum ΘV ΘW) {A : Set ℂ}
    (hA : A ⊆ {z | ∃ ρ ∈ spec ΘV, ∃ ρ' ∈ spec ΘW, z = ρ + ρ'})
    (hinf : A.Infinite) (hbdd : Bornology.IsBounded A) :
    ∃ z ∈ closure A, AccPt z (Filter.principal (spec ΘS)) := by
  have hsub : A ⊆ spec ΘS := by
    intro z hz
    obtain ⟨ρ, h1, ρ', h2, rfl⟩ := hA hz
    exact add_mem_spec hV hW κ hκ hcomm h1 h2
  obtain ⟨z, hz, hacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (hbdd.isCompact_closure) subset_closure
  exact ⟨z, hz, hacc.mono (Filter.principal_mono.2 hsub)⟩

end WeilRH.KunSquare
