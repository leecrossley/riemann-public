/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.TrivialModelFull

/-!
# The trivial model as one graded Weil datum (`def:trivial-model`, `def:aw`)

Source: the manuscript `latex/notes.tex`, `def:trivial-model`, `prop:trivial-model` (i)–(ii) and
the axioms AW1–AW4 of `def:aw` in type `(d, w) = (1, 0)`.

`TrivialModel.lean` and `TrivialModelFull.lean` build the degree slices and the product separately.
This file packages all three degrees into the single graded structure
`WeightedAlgebraDatum (Tot ι) 1 0` of `WeightedAlgebra.lean` (graded pieces, cup product, flow,
spectral cores, trace, stars and positive forms in every degree), and identifies the end degrees
with the unit object.

## Main results

* `TrivialModel.mulL`, `thetaL`, `G`, `st`, `trT`: the product, flow, grading
  (`V^0 = ℂ·1`, `V^1`, `V^2 = ℂη`), stars `*_0, *_1, *_2` and trace as linear data on `Tot ι`.
* `TrivialModel.gradedModel`: for a finite family `ρ` on `Re s = 1/2`, the trivial model is a
  `WeightedAlgebraDatum (Tot ι) 1 0`: AW1 (derivation), AW3 (trace weight `d + w = 1`), AW4
  (star laws, `h_j` Hermitian and positive definite) in all degrees at once.
* `TrivialModel.deg0Equiv`, `deg0Equiv_unit`: AW1's `V^0 ≅ 𝟙`, as a unital multiplicative
  isomorphism carrying `Θ_0` to the flow `0` of `𝟙`.
* `TrivialModel.deg2Equiv`, `deg2Equiv_twist`: AW1's `V^2 ≅ 𝟙(-1)`, carrying `Θ_2` to `1`, with the
  trace as the coefficient map.
* `TrivialModel.gradedModel_nontrivial`: the datum is nonzero, so `WeightedAlgebraDatum` with `w = 0`
  has a nonzero model with nonzero degree-one part (any nonempty `ι`).
* `TrivialModel.spectralCore_G1`, `gradedModelOf`, `gradedModelInf`, `gradedModelInf_nontrivial`:
  the degree-one summand `G 1` is a spectral core whenever `(V^1, Θ_1)` is (transport along
  `deg1Equiv`), so the package exists for every divisor with finite multiplicities and no finite
  accumulation point, without assuming `ι` finite.

## Fidelity

`gradedModel` is the finite case of `gradedModelOf`, where the spectral-core condition is automatic.
`gradedModelInf` takes the hypotheses of `prop:trivial-model` (i) and uses `spectralCore_theta`. The
positivity hypothesis `Re ρ = 1/2` is necessary: by `prop:trivial-model` (iii)
(`TrivialModel.exists_datum_iff`) no positive degree-one datum exists off the line.
-/

open Module Complex ComplexConjugate DirectSum WeilRH.Spectral
namespace WeilRH.TrivialModel

variable {ι : Type} (ρ : ι → ℂ) [DecidableEq ι]

/-- The product `mul` of `TrivialModelFull` as a bilinear map. -/
noncomputable def mulL : Tot ι →ₗ[ℂ] Tot ι →ₗ[ℂ] Tot ι :=
  LinearMap.mk₂ ℂ mul
    (fun x x' y => by
      obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := x'; obtain ⟨b, v, e⟩ := y
      simp only [mul, Prod.mk_add_mk, Prod.mk.injEq, map_add, LinearMap.add_apply]
      refine ⟨by ring, by module, by ring⟩)
    (fun s x y => by
      obtain ⟨a, u, c⟩ := x; obtain ⟨b, v, e⟩ := y
      simp only [mul, Prod.smul_mk, Prod.mk.injEq, map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine ⟨by ring, by module, by ring⟩)
    (fun x y y' => by
      obtain ⟨a, u, c⟩ := x; obtain ⟨b, v, e⟩ := y; obtain ⟨b', v', e'⟩ := y'
      simp only [mul, Prod.mk_add_mk, Prod.mk.injEq, map_add]
      refine ⟨by ring, by module, by ring⟩)
    (fun s x y => by
      obtain ⟨a, u, c⟩ := x; obtain ⟨b, v, e⟩ := y
      simp only [mul, Prod.smul_mk, Prod.mk.injEq, map_smul, smul_eq_mul]
      refine ⟨by ring, by module, by ring⟩)

@[simp] lemma mulL_apply (x y : Tot ι) : mulL x y = mul x y := rfl

/-- The flow `thetaTot` as a linear map. -/
noncomputable def thetaL : Module.End ℂ (Tot ι) where
  toFun := thetaTot ρ
  map_add' x y := by simp [thetaTot]
  map_smul' c x := by simp [thetaTot]

omit [DecidableEq ι] in
@[simp] lemma thetaL_apply (x : Tot ι) : thetaL ρ x = thetaTot ρ x := rfl

/-- The grading: `V^0 = ℂ·1`, `V^1`, `V^2 = ℂη`, and `0` above degree `2`. -/
def G : ℕ → Submodule ℂ (Tot ι)
  | 0 => LinearMap.ker (LinearMap.snd ℂ ℂ (V1 ι × ℂ))
  | 1 => LinearMap.ker (LinearMap.fst ℂ ℂ (V1 ι × ℂ)) ⊓
      LinearMap.ker ((LinearMap.snd ℂ (V1 ι) ℂ).comp (LinearMap.snd ℂ ℂ (V1 ι × ℂ)))
  | 2 => LinearMap.ker (LinearMap.fst ℂ ℂ (V1 ι × ℂ)) ⊓
      LinearMap.ker ((LinearMap.fst ℂ (V1 ι) ℂ).comp (LinearMap.snd ℂ ℂ (V1 ι × ℂ)))
  | _ + 3 => ⊥

omit [DecidableEq ι] in
lemma mem_G0 {x : Tot ι} : x ∈ G 0 ↔ x.2.1 = 0 ∧ x.2.2 = 0 := by
  simp [G, Prod.ext_iff]
omit [DecidableEq ι] in
lemma mem_G1 {x : Tot ι} : x ∈ G 1 ↔ x.1 = 0 ∧ x.2.2 = 0 := by simp [G]
omit [DecidableEq ι] in
lemma mem_G2 {x : Tot ι} : x ∈ G 2 ↔ x.1 = 0 ∧ x.2.1 = 0 := by simp [G]
omit [DecidableEq ι] in
lemma mem_G3 {n : ℕ} {x : Tot ι} : x ∈ G (n + 3) ↔ x = 0 := by simp [G]


/-- `*_0(a) = ā η`. -/
noncomputable def st0 : Tot ι →ₗ⋆[ℂ] Tot ι where
  toFun x := (0, 0, conj x.1)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- `*_1 = starLine` on `V^1`. -/
noncomputable def st1 : Tot ι →ₗ⋆[ℂ] Tot ι where
  toFun x := (0, starLine x.2.1, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- `*_2(c η) = c̄`. -/
noncomputable def st2 : Tot ι →ₗ⋆[ℂ] Tot ι where
  toFun x := (conj x.2.2, 0, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The stars `*_j`, with `*_j = 0` for `j > 2`. -/
noncomputable def st : ℕ → Tot ι →ₗ⋆[ℂ] Tot ι
  | 0 => st0
  | 1 => st1
  | 2 => st2
  | _ + 3 => 0

@[simp] lemma st_add_three (n : ℕ) : st (ι := ι) (n + 3) = 0 := rfl

/-- `Tr(a, u, c) = c`. -/
noncomputable def trT : Tot ι →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ (V1 ι) ℂ).comp (LinearMap.snd ℂ ℂ (V1 ι × ℂ))

/-- On the line, `B(u, *_1 v)` is the form `h_1` of the degree-one slice. -/
lemma B_starLine_eq_h (hline : ∀ p, (ρ p).re = 1 / 2) (u v : V1 ι) :
    B u (starLine v) = (model ρ).h u v := by
  simp [WeightedStarDatum.h, WeightedStarDatum.B, model, star1_of_line ρ hline]

/-- `V^0 ≅ 𝟙`: the coefficient map `V^0 → ℂ, a·1 ↦ a` is a linear isomorphism. -/
noncomputable def deg0Equiv : G (ι := ι) 0 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective ((LinearMap.fst ℂ ℂ (V1 ι × ℂ)).comp (G 0).subtype) <| by
    refine ⟨fun x y h => ?_, fun a => ⟨⟨(a, 0, 0), by simp [mem_G0]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G0] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

/-- `V^2 ≅ 𝟙(-1)`: the coefficient map `V^2 → ℂ, cη ↦ c` is a linear isomorphism. -/
noncomputable def deg2Equiv : G (ι := ι) 2 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective ((LinearMap.snd ℂ (V1 ι) ℂ).comp
      ((LinearMap.snd ℂ ℂ (V1 ι × ℂ)).comp (G 2).subtype)) <| by
    refine ⟨fun x y h => ?_, fun c => ⟨⟨(0, 0, c), by simp [mem_G2]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G2] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

/-- `V^1 ≅ V1 ι`: the middle component. -/
noncomputable def deg1Equiv : G (ι := ι) 1 ≃ₗ[ℂ] V1 ι :=
  LinearEquiv.ofBijective ((LinearMap.fst ℂ (V1 ι) ℂ).comp
      ((LinearMap.snd ℂ ℂ (V1 ι × ℂ)).comp (G 1).subtype)) <| by
    refine ⟨fun x y h => ?_, fun u => ⟨⟨(0, u, 0), by simp [mem_G1]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G1] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

omit [DecidableEq ι] in
lemma deg1Equiv_symm_apply (u : V1 ι) : ((deg1Equiv (ι := ι)).symm u : Tot ι) = (0, u, 0) := by
  have : (deg1Equiv (ι := ι)).symm u = ⟨(0, u, 0), by simp [mem_G1]⟩ :=
    (deg1Equiv (ι := ι)).symm_apply_eq.mpr rfl
  rw [this]

instance : FiniteDimensional ℂ (G (ι := ι) 0) := deg0Equiv.symm.finiteDimensional
instance : FiniteDimensional ℂ (G (ι := ι) 2) := deg2Equiv.symm.finiteDimensional
instance (n : ℕ) : FiniteDimensional ℂ (G (ι := ι) (n + 3)) := by
  rw [show G (ι := ι) (n + 3) = ⊥ from rfl]; infer_instance

omit [DecidableEq ι] in
/-- **`prop:trivial-model` (i) in the graded package**: if `(V^1, Θ_1)` is a spectral core, so is
the degree-one summand `G 1` of `Tot ι` with the restricted flow (transport along `deg1Equiv`). -/
theorem spectralCore_G1 (hsc : SpectralCore (theta ρ)) :
    SpectralCore ((thetaL ρ).restrict (p := G (ι := ι) 1) (q := G 1) fun x hx => by
      obtain ⟨a, u, c⟩ := x; rw [mem_G1] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]) :=
  hsc.of_equiv (deg1Equiv (ι := ι)).symm fun u => by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, deg1Equiv_symm_apply, deg1Equiv_symm_apply]
    simp [thetaTot]

/-- **The trivial model as one graded Weil datum** of type `(1, 0)` (`def:trivial-model`,
`def:aw` AW1, AW3, AW4 in every degree), for a family `ρ` on `Re s = 1/2` whose degree-one slice
`(V^1, Θ_1)` is a spectral core. Degrees `0` and `2` are one-dimensional. -/
noncomputable def gradedModelOf (hline : ∀ p, (ρ p).re = 1 / 2) (hsc : SpectralCore (theta ρ)) :
    WeightedAlgebraDatum (Tot ι) 1 0 where
  G := G
  vanish j hj := by
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 3 := ⟨j - 3, by omega⟩
    rfl
  mul := mulL
  mul_mem {i k x y} hx hy := by
    obtain ⟨a, u, c⟩ := x; obtain ⟨b, v, e⟩ := y
    match i, k, hx, hy with
    | 0, 0, hx, hy =>
      rw [mem_G0] at hx hy ⊢; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy; simp [mul]
    | 0, 1, hx, hy =>
      rw [mem_G0] at hx; rw [mem_G1] at hy ⊢; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
      simp [mul]
    | 0, 2, hx, hy =>
      rw [mem_G0] at hx; rw [mem_G2] at hy ⊢; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
      simp [mul]
    | 1, 0, hx, hy =>
      rw [mem_G1] at hx ⊢; rw [mem_G0] at hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
      simp [mul]
    | 1, 1, hx, hy =>
      rw [mem_G1] at hx hy; rw [mem_G2]; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
      simp [mul]
    | 2, 0, hx, hy =>
      rw [mem_G2] at hx ⊢; rw [mem_G0] at hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
      simp [mul]
    | 1, 2, hx, hy =>
      rw [mem_G1] at hx; rw [mem_G2] at hy; rw [show 1 + 2 = 0 + 3 from rfl, mem_G3]
      obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy; simp [mul]
    | 2, 1, hx, hy =>
      rw [mem_G2] at hx; rw [mem_G1] at hy; rw [show 2 + 1 = 0 + 3 from rfl, mem_G3]
      obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy; simp [mul]
    | 2, 2, hx, hy =>
      rw [mem_G2] at hx hy; rw [show 2 + 2 = 1 + 3 from rfl, mem_G3]
      obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy; simp [mul]
    | n + 3, k, hx, _ =>
      rw [mem_G3] at hx; rw [hx, map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | i, n + 3, _, hy =>
      rw [mem_G3] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _
  Θ := thetaL ρ
  Θ_mem {j x} hx := by
    obtain ⟨a, u, c⟩ := x
    match j, hx with
    | 0, hx => rw [mem_G0] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | 1, hx => rw [mem_G1] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | 2, hx => rw [mem_G2] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | n + 3, hx => rw [mem_G3] at hx ⊢; simp [hx, thetaTot]
  Θ_mul x y := by simpa using thetaTot_mul ρ x y
  spectralCore j := by
    match j with
    | 0 => exact Spectral.spectralCore_of_finiteDimensional _
    | 1 => exact spectralCore_G1 ρ hsc
    | 2 => exact Spectral.spectralCore_of_finiteDimensional _
    | n + 3 => exact Spectral.spectralCore_of_finiteDimensional _
  Tr := trT
  Tr_Θ x hx := by
    obtain ⟨a, u, c⟩ := x
    rw [show 2 * 1 = 2 from rfl, mem_G2] at hx; obtain ⟨rfl, rfl⟩ := hx
    simp [trT, thetaTot]
  st := st
  st_mem {j x} hx := by
    obtain ⟨a, u, c⟩ := x
    match j, hx with
    | 0, _ => rw [show 2 * 1 - 0 = 2 from rfl, mem_G2]; simp [st, st0]
    | 1, _ => rw [show 2 * 1 - 1 = 1 from rfl, mem_G1]; simp [st, st1]
    | 2, _ => rw [show 2 * 1 - 2 = 0 from rfl, mem_G0]; simp [st, st2]
    | n + 3, _ => rw [st_add_three, LinearMap.zero_apply]; exact Submodule.zero_mem _
  Θ_st {j x} hx := by
    obtain ⟨a, u, c⟩ := x
    match j, hx with
    | 0, hx =>
      rw [mem_G0] at hx; obtain ⟨rfl, rfl⟩ := hx
      simp [st, st0, thetaTot]
    | 1, hx =>
      rw [mem_G1] at hx; obtain ⟨rfl, rfl⟩ := hx
      simp [st, st1, thetaTot, theta_starLine ρ hline]
    | 2, hx =>
      rw [mem_G2] at hx; obtain ⟨rfl, rfl⟩ := hx
      simp only [st, st2, thetaL_apply, thetaTot, LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk,
        smul_eq_mul, Prod.mk_add_mk, map_zero, smul_zero, add_zero, Prod.mk.injEq]
      refine ⟨by push_cast; ring, by simp, by simp⟩
    | n + 3, hx => rw [mem_G3] at hx; rw [hx]; simp [thetaTot]
  h_conj {j u v} hu hv := by
    obtain ⟨a, u, c⟩ := u; obtain ⟨b, v, e⟩ := v
    match j, hu, hv with
    | 0, hu, hv =>
      rw [mem_G0] at hu hv; obtain ⟨rfl, rfl⟩ := hu; obtain ⟨rfl, rfl⟩ := hv
      simp [st, st0, trT, mul, mul_comm]
    | 1, hu, hv =>
      rw [mem_G1] at hu hv; obtain ⟨rfl, rfl⟩ := hu; obtain ⟨rfl, rfl⟩ := hv
      simp only [st, st1, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
        add_zero, zero_add]
      rw [B_starLine_eq_h ρ hline, B_starLine_eq_h ρ hline]
      exact (model_isPositive ρ hline).conj_symm u v
    | 2, hu, hv =>
      rw [mem_G2] at hu hv; obtain ⟨rfl, rfl⟩ := hu; obtain ⟨rfl, rfl⟩ := hv
      simp [st, st2, trT, mul, mul_comm]
    | n + 3, hu, hv => rw [mem_G3] at hu hv; rw [hu, hv]; simp
  h_pos {j u} hu hu0 := by
    obtain ⟨a, u, c⟩ := u
    match j, hu with
    | 0, hu =>
      rw [mem_G0] at hu; obtain ⟨rfl, rfl⟩ := hu
      have ha : a ≠ 0 := fun h => hu0 (by simp [h])
      simp only [st, st0, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
        add_zero, map_zero]
      rw [Complex.mul_conj]; exact_mod_cast Complex.normSq_pos.mpr ha
    | 1, hu =>
      rw [mem_G1] at hu; obtain ⟨rfl, rfl⟩ := hu
      have hu' : u ≠ 0 := fun h => hu0 (by simp [h])
      simp only [st, st1, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
        add_zero, zero_add]
      rw [B_starLine_eq_h ρ hline]
      exact (model_isPositive ρ hline).re_pos u hu'
    | 2, hu =>
      rw [mem_G2] at hu; obtain ⟨rfl, rfl⟩ := hu
      have hc : c ≠ 0 := fun h => hu0 (by simp [h])
      simp only [st, st2, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero, zero_mul,
        zero_add, add_zero, map_zero]
      rw [Complex.mul_conj]; exact_mod_cast Complex.normSq_pos.mpr hc
    | n + 3, hu => rw [mem_G3] at hu; exact absurd hu hu0

/-- **The trivial model for an infinite divisor**: if `Σ` has finite multiplicities and no finite
accumulation point (the hypotheses of `prop:trivial-model` (i)), the graded package is a
`WeilRH.WeightedAlgebraDatum` with no finiteness assumption on `ι`. -/
noncomputable def gradedModelInf (hline : ∀ p, (ρ p).re = 1 / 2)
    (hfin : ∀ σ, {i | lam ρ i = σ}.Finite)
    (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range (lam ρ)))) :
    WeightedAlgebraDatum (Tot ι) 1 0 :=
  gradedModelOf ρ hline (spectralCore_theta ρ hfin hdisc)

/-- The infinite-divisor package is nonzero: `1 ≠ 0` lies in `V^0`. -/
theorem gradedModelInf_nontrivial (hline : ∀ p, (ρ p).re = 1 / 2)
    (hfin : ∀ σ, {i | lam ρ i = σ}.Finite)
    (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range (lam ρ)))) :
    one ∈ (gradedModelInf ρ hline hfin hdisc).G 0 ∧ (one : Tot ι) ≠ 0 := by
  refine ⟨by simp [gradedModelInf, gradedModelOf, mem_G0, one], fun h => ?_⟩
  have := congrArg Prod.fst h
  simp [one] at this

variable [Fintype ι]

/-- **The trivial model as one graded Weil datum** for a finite family `ρ` on `Re s = 1/2`
(`gradedModelOf` with the automatic spectral-core condition in finite dimension). -/
noncomputable def gradedModel (hline : ∀ p, (ρ p).re = 1 / 2) :
    WeightedAlgebraDatum (Tot ι) 1 0 :=
  gradedModelOf ρ hline (Spectral.spectralCore_of_finiteDimensional _)

variable (hline : ∀ p, (ρ p).re = 1 / 2)

@[simp] lemma gradedModel_G : (gradedModel ρ hline).G = G := rfl
@[simp] lemma gradedModel_mul (x y : Tot ι) : (gradedModel ρ hline).mul x y = mul x y := rfl
@[simp] lemma gradedModel_Θ (x : Tot ι) : (gradedModel ρ hline).Θ x = thetaTot ρ x := rfl

/-- **AW1, `V^0 ≅ 𝟙` as a unital algebra with flow**: `1 ∈ V^0`, it maps to `1 ∈ ℂ`, the
isomorphism is multiplicative, and the flow `Θ_0` corresponds to `0` (the flow of `𝟙`). -/
theorem deg0Equiv_unit :
    one ∈ G (ι := ι) 0 ∧ deg0Equiv (ι := ι) ⟨one, by simp [mem_G0, one]⟩ = 1 ∧
    (∀ x y : G (ι := ι) 0, deg0Equiv ⟨mul x.1 y.1, (gradedModel ρ hline).mul_mem x.2 y.2⟩ =
      deg0Equiv x * deg0Equiv y) ∧
    (∀ x : G (ι := ι) 0, deg0Equiv ⟨thetaTot ρ x.1, (gradedModel ρ hline).Θ_mem x.2⟩ = 0) := by
  refine ⟨by simp [mem_G0, one], rfl, fun x y => rfl, fun x => rfl⟩

/-- **AW1, `V^2 ≅ 𝟙(-1)`**: the flow `Θ_2` corresponds to multiplication by `1`, the flow of the
Tate twist `𝟙(-1)` (`d + w = 1`), and the trace is the coefficient map. -/
theorem deg2Equiv_twist :
    (∀ x : G (ι := ι) 2, deg2Equiv ⟨thetaTot ρ x.1, (gradedModel ρ hline).Θ_mem x.2⟩ =
      deg2Equiv x) ∧
    ∀ x : G (ι := ι) 2, (gradedModel ρ hline).Tr x.1 = deg2Equiv x := by
  refine ⟨fun x => rfl, fun x => rfl⟩

/-- The graded trivial model is nonzero: `1 ≠ 0` lies in `V^0`. -/
theorem gradedModel_nontrivial : one ∈ (gradedModel ρ hline).G 0 ∧ (one : Tot ι) ≠ 0 := by
  refine ⟨by simp [mem_G0, one], fun h => ?_⟩
  have := congrArg Prod.fst h
  simp [one] at this

end WeilRH.TrivialModel
