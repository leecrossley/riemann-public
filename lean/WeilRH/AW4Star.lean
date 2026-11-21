/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.AW4Forms
import WeilRH.Duality
import WeilRH.WeilConverse

/-!
# Stars from polarizations (`prop:aw4-forms` (iii))

`prop:aw4-forms` (iii): for a Weil datum of type `(d, 0)` satisfying the derivation rule of AW1,
AW3, and AW4-V, there are antilinear maps `*'_j : V^j → V^{2d-j}` satisfying the star law of AW4
whose star forms are the given polarizations. The construction is degree by degree, and in degree
`j` it only involves the slice `V = V^j`, `W = V^{2d-j}`, `T = V^{2d}` of `WeightedStarDatum`
(with `w = 0`) together with AW3's perfectness of `B(u, x) = Tr(u ∪ x)` on
`V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d-ρ}` (`blockPairing`, `Remark rem:aw-comments`). We state it for that
slice.

## Main results

* `AW4Star.exists_star` (**`prop:aw4-forms` (iii)**, degree `j`): if `(V, Θ_j)` is a spectral core
  with a positive infinitesimal polarization `h` of weight `j`, then there is an antilinear
  `*' : V → W` with `Θ_{2d-j} ∘ *' = *' ∘ Θ_j + (d - j) *'` and `Tr(u ∪ *'v) = h(u, v)`.
* `AW4Star.exists_weightedStarDatum`: the same, packaged as a `WeightedStarDatum d 0 j` with the
  given flows, cup product and trace, whose star form is `h`.
-/

open Module Complex ComplexConjugate

namespace WeilRH.AW4Star

open WeilRH.Suspension WeilRH.Spectral WeilRH.AW4Forms

variable {V W T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup T] [Module ℂ T]

/-- The pairing `B(u, x) = Tr(u ∪ x)` restricted to `V_{Θ∼ρ} × W_{Θ∼σ}`, as the map
`W_{Θ∼σ} → (V_{Θ∼ρ})^*`. AW3's perfectness on `V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d-ρ}` is bijectivity
for `σ = d - ρ`. -/
noncomputable def blockPairing (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W)
    (cup : V →ₗ[ℂ] W →ₗ[ℂ] T) (tr : T →ₗ[ℂ] ℂ) (ρ σ : ℂ) :
    ΘW.maxGenEigenspace σ →ₗ[ℂ] Module.Dual ℂ (ΘV.maxGenEigenspace ρ) :=
  ((cup.compr₂ tr).flip ∘ₗ (ΘW.maxGenEigenspace σ).subtype).compl₂ (ΘV.maxGenEigenspace ρ).subtype

@[simp] lemma blockPairing_apply (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W)
    (cup : V →ₗ[ℂ] W →ₗ[ℂ] T) (tr : T →ₗ[ℂ] ℂ) (ρ σ : ℂ) (x : ΘW.maxGenEigenspace σ)
    (u : ΘV.maxGenEigenspace ρ) : blockPairing ΘV ΘW cup tr ρ σ x u = tr (cup u x) := rfl

/-- The functional `u ↦ h(u, x)` on `V_{Θ∼ρ}`. -/
noncomputable def hFun (h : PosHermForm V) (ΘV : Module.End ℂ V) (ρ : ℂ) (x : V) :
    Module.Dual ℂ (ΘV.maxGenEigenspace ρ) where
  toFun u := h.toFun u x
  map_add' u u' := h.add_left u u' x
  map_smul' c u := h.smul_left c u x

/-- Distinct eigenspaces are `h`-orthogonal for an infinitesimal polarization `h` of weight `j`
when every eigenvalue has real part `j / 2`. -/
lemma toFun_eq_zero_of_ne (h : PosHermForm V) {Θ : Module.End ℂ V} {j : ℝ} (hh : IsInfPol h Θ j)
    (hre : ∀ ρ, Θ.HasEigenvalue ρ → ρ.re = j / 2) {ρ ρ' : ℂ} (hne : ρ' ≠ ρ) {u v : V}
    (hu : u ∈ Θ.eigenspace ρ') (hv : v ∈ Θ.eigenspace ρ) : h.toFun u v = 0 := by
  by_cases hv0 : v = 0
  · rw [hv0, h.zero_right]
  have hρ : Θ.HasEigenvalue ρ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩
  have hc : conj ρ = (j : ℂ) - ρ := by
    apply Complex.ext <;> simp [hre ρ hρ]; ring
  have := hh u v
  rw [Module.End.mem_eigenspace_iff.1 hu, Module.End.mem_eigenspace_iff.1 hv, h.smul_left,
    h.smul_right, hc] at this
  have h2 : (ρ' - ρ) * h.toFun u v = 0 := by linear_combination this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

/-- **`prop:aw4-forms` (iii)**, degree `j`. Let `Θ_{2d}` be a derivation for `∪` (AW1), let
`Tr : V^{2d} → ℂ(-d)` be flow-equivariant (AW3, type `(d, 0)`), and let `B = Tr(· ∪ ·)` pair
`V^j_{Θ∼ρ}` perfectly with `V^{2d-j}_{Θ∼d-ρ}` (AW3). If `(V^j, Θ_j)` is a spectral core with a
positive infinitesimal polarization `h` of weight `j` (AW4-V), there is an antilinear
`*' : V^j → V^{2d-j}` satisfying the star law of AW4 whose star form `Tr(u ∪ *'v)` is `h`. -/
theorem exists_star (d j : ℕ) (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) (ΘT : Module.End ℂ T)
    (cup : V →ₗ[ℂ] W →ₗ[ℂ] T) (tr : T →ₗ[ℂ] ℂ)
    (hcup : ∀ u v, ΘT (cup u v) = cup (ΘV u) v + cup u (ΘW v))
    (htr : ∀ x, tr (ΘT x) = (d : ℂ) * tr x)
    (hperf : ∀ ρ, Function.Bijective (blockPairing ΘV ΘW cup tr ρ (d - ρ)))
    (hS : SpectralCore ΘV) (h : PosHermForm V) (hh : IsInfPol h ΘV j) :
    ∃ star : V →ₗ⋆[ℂ] W, (∀ v, ΘW (star v) = star (ΘV v) + ((d : ℂ) - j) • star v) ∧
      ∀ u v, tr (cup u (star v)) = h.toFun u v := by
  classical
  have hE : AW4E ΘV j := aw4E_of_aw4V hS ⟨h, hh⟩
  have hdiag : ⨆ ρ, ΘV.eigenspace ρ = ⊤ := AW4Forms.iSup_eigenspace_eq_top hE
  have hre : ∀ ρ, ΘV.HasEigenvalue ρ → ρ.re = (j : ℝ) / 2 := fun ρ hρ => AW4Forms.re_eq_half hE hρ
  have hmg : ∀ ρ, ΘV.maxGenEigenspace ρ = ΘV.eigenspace ρ := AW4Forms.maxGenEigenspace_eq_eigenspace hE
  let Ψ : ∀ ρ : ℂ, ΘW.maxGenEigenspace ((d : ℂ) - ρ) ≃ₗ[ℂ] Module.Dual ℂ (ΘV.maxGenEigenspace ρ) :=
    fun ρ => LinearEquiv.ofBijective _ (hperf ρ)
  -- the star on `V_ρ`
  let t : ∀ ρ : ℂ, ΘV.eigenspace ρ →ₗ⋆[ℂ] W := fun ρ =>
    { toFun := fun x => ((Ψ ρ).symm (hFun h ΘV ρ x) : W)
      map_add' := fun x y => by
        have : hFun h ΘV ρ ((x + y : ΘV.eigenspace ρ) : V) =
            hFun h ΘV ρ (x : V) + hFun h ΘV ρ (y : V) := by
          ext u; simp [hFun, h.add_right]
        rw [this, map_add, Submodule.coe_add]
      map_smul' := fun c x => by
        have : hFun h ΘV ρ ((c • x : ΘV.eigenspace ρ) : V) = conj c • hFun h ΘV ρ (x : V) := by
          ext u; simp [hFun, h.smul_right]
        rw [this, map_smul, Submodule.coe_smul] }
  have ht_mem : ∀ ρ x, t ρ x ∈ ΘW.maxGenEigenspace ((d : ℂ) - ρ) := fun ρ x =>
    ((Ψ ρ).symm (hFun h ΘV ρ (x : V))).2
  have ht_pair : ∀ ρ (x : ΘV.eigenspace ρ) (u : V) (hu : u ∈ ΘV.maxGenEigenspace ρ),
      tr (cup u (t ρ x)) = h.toFun u x := by
    intro ρ x u hu
    have := LinearMap.congr_fun ((Ψ ρ).apply_symm_apply (hFun h ΘV ρ (x : V))) ⟨u, hu⟩
    exact this
  -- `Θ_W` acts on the image of `V_ρ` by `d - ρ`
  have ht_eig : ∀ ρ x, ΘW (t ρ x) = ((d : ℂ) - ρ) • t ρ x := by
    intro ρ x
    set y := t ρ x
    have hy := ht_mem ρ x
    have hz : ΘW y - ((d : ℂ) - ρ) • y ∈ ΘW.maxGenEigenspace ((d : ℂ) - ρ) :=
      sub_mem (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl ΘW) _ hy)
        (Submodule.smul_mem _ _ hy)
    have h0 : Ψ ρ ⟨_, hz⟩ = 0 := by
      ext ⟨u, hu⟩
      have hu' : ΘV u = ρ • u := Module.End.mem_eigenspace_iff.1 (hmg ρ ▸ hu)
      have key := htr (cup u y)
      rw [hcup, map_add, hu', map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul] at key
      show tr (cup u (ΘW y - ((d : ℂ) - ρ) • y)) = 0
      rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul]
      linear_combination key
    have := congrArg Subtype.val ((Ψ ρ).injective (h0.trans (map_zero _).symm))
    exact sub_eq_zero.1 this
  -- assemble over the eigenspace decomposition
  let e := eigenEquiv ΘV hdiag
  let s0 : V →+ W := (DirectSum.toAddMonoid fun ρ => (t ρ).toAddMonoidHom).comp
    e.symm.toLinearMap.toAddMonoidHom
  have hs0 : ∀ ρ v (hv : v ∈ ΘV.eigenspace ρ), s0 v = t ρ ⟨v, hv⟩ := by
    intro ρ v hv
    have he : e.symm v = DirectSum.of (fun ρ => ΘV.eigenspace ρ) ρ ⟨v, hv⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact (DirectSum.coeLinearMap_of (fun ρ => ΘV.eigenspace ρ) ρ ⟨v, hv⟩).symm
    simp [s0, he, DirectSum.toAddMonoid_of]
  have hall : ∀ v : V, v ∈ ⨆ ρ, ΘV.eigenspace ρ := fun v => hdiag ▸ Submodule.mem_top
  have hsmul : ∀ (c : ℂ) v, s0 (c • v) = conj c • s0 v := by
    intro c v
    induction hall v using Submodule.iSup_induction' with
    | mem ρ v hv =>
      rw [hs0 ρ _ (Submodule.smul_mem _ c hv), hs0 ρ v hv]
      exact (t ρ).map_smulₛₗ c ⟨v, hv⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  let star : V →ₗ⋆[ℂ] W :=
    { toFun := s0
      map_add' := s0.map_add
      map_smul' := hsmul }
  refine ⟨star, fun v => ?_, fun u v => ?_⟩
  · -- the star law
    induction hall v using Submodule.iSup_induction' with
    | mem ρ v hv =>
      change ΘW (s0 v) = s0 (ΘV v) + ((d : ℂ) - j) • s0 v
      rw [Module.End.mem_eigenspace_iff.1 hv, hsmul, hs0 ρ v hv, ht_eig]
      by_cases hv0 : v = 0
      · have : (⟨v, hv⟩ : ΘV.eigenspace ρ) = 0 := Subtype.ext hv0
        rw [this, map_zero]; simp
      have hρ : ΘV.HasEigenvalue ρ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩
      have hc : conj ρ = (j : ℂ) - ρ := by
        apply Complex.ext <;> simp [hre ρ hρ]; ring
      rw [hc, ← add_smul]
      congr 1
      ring
    | zero => simp
    | add x y _ _ hx hy =>
      change ΘW (s0 (x + y)) = s0 (ΘV (x + y)) + ((d : ℂ) - j) • s0 (x + y)
      change ΘW (s0 x) = s0 (ΘV x) + ((d : ℂ) - j) • s0 x at hx
      change ΘW (s0 y) = s0 (ΘV y) + ((d : ℂ) - j) • s0 y at hy
      rw [map_add, map_add, map_add, hx, hy, map_add, smul_add]
      abel
  · -- the star form is `h`
    change tr (cup u (s0 v)) = h.toFun u v
    induction hall v using Submodule.iSup_induction' with
    | mem ρ v hv =>
      rw [hs0 ρ v hv]
      induction hall u using Submodule.iSup_induction' with
      | mem ρ' u hu =>
        by_cases hρ : ρ' = ρ
        · subst hρ
          exact ht_pair ρ' ⟨v, hv⟩ u (hmg ρ' ▸ hu)
        · rw [toFun_eq_zero_of_ne h hh hre hρ hu hv]
          refine cupTrace_eq_zero_of_mem_maxGenEigenspace ΘV ΘW ΘT cup tr hcup htr ?_
            (Module.End.eigenspace_le_maxGenEigenspace hu) (ht_mem ρ _)
          intro hsum
          exact hρ (by linear_combination hsum)
      | zero => simp [h.zero_left]
      | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, h.add_left]
    | zero => simp [h.zero_right]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy, h.add_right]

/-- **`prop:aw4-forms` (iii)**, packaged: under the hypotheses of `exists_star`, the given flows,
cup product and trace extend to a `WeightedStarDatum` of type `(d, 0)` in degree `j` whose star
form `h_j` is the given polarization `h`. -/
theorem exists_weightedStarDatum (d j : ℕ) (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W)
    (ΘT : Module.End ℂ T) (cup : V →ₗ[ℂ] W →ₗ[ℂ] T) (tr : T →ₗ[ℂ] ℂ)
    (hcup : ∀ u v, ΘT (cup u v) = cup (ΘV u) v + cup u (ΘW v))
    (htr : ∀ x, tr (ΘT x) = (d : ℂ) * tr x)
    (hperf : ∀ ρ, Function.Bijective (blockPairing ΘV ΘW cup tr ρ (d - ρ)))
    (hS : SpectralCore ΘV) (h : PosHermForm V) (hh : IsInfPol h ΘV j) :
    ∃ D : WeightedStarDatum d 0 j V W T, D.ΘV = ΘV ∧ D.ΘW = ΘW ∧ D.ΘT = ΘT ∧ D.cup = cup ∧
      D.tr = tr ∧ ∀ u v, D.h u v = h.toFun u v := by
  obtain ⟨star, hlaw, hform⟩ := exists_star d j ΘV ΘW ΘT cup tr hcup htr hperf hS h hh
  exact ⟨{ ΘV := ΘV, ΘW := ΘW, ΘT := ΘT, cup := cup, cup_derivation := hcup, tr := tr
           tr_equivariant := fun x => by rw [htr]; simp
           star := star, star_comm := hlaw }, rfl, rfl, rfl, rfl, rfl, hform⟩

end WeilRH.AW4Star
