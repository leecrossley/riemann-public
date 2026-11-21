/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.TrivialModel
import WeilRH.AW4Star
import WeilRH.WeightedAlgebra

/-!
# The trivial model in all degrees (`def:trivial-model`, `prop:trivial-model`)

Source: the manuscript `latex/notes.tex`, `def:trivial-model` and the proofs of
`prop:trivial-model` (i)–(ii).

`WeilRH.TrivialModel` builds the degree-one slice. This file adds degrees `0` and `2`
(`V^0 = ℂ·1`, `V^2 = ℂη`, `Θ_0 = 0`, `Θ_2 = 1`, `*_0(c) = c̄η`, `*_2(cη) = c̄`), the whole graded
algebra `V^0 ⊕ V^1 ⊕ V^2` with its product, and AW3's blockwise perfectness of `B`.

## Main results

* `TrivialModel.model0`, `TrivialModel.model2`: the degree-`0` and degree-`2` slices as
  `WeightedStarDatum 1 0 0` and `WeightedStarDatum 1 0 2`; `model0_isPositive`, `model2_isPositive`
  (**`prop:trivial-model` (ii)**, `h_0` and `h_2`), `spectralCore_zero`, `spectralCore_two`
  (`V^1` is `TrivialModel.spectralCore_theta`).
* `TrivialModel.Tot`, `TrivialModel.mul`: the graded algebra with `u ∪ v = B(u, v) η` on `V^1` and
  the unit products otherwise. **`prop:trivial-model` (i)**: `mul_assoc'` (associativity),
  `mul_comm_graded` and `mul_anticomm_one` (graded commutativity), `one_mul'`, `mul_one'` (unit `1 ∈ V^0`),
  `thetaTot_mul` (`Θ` is a derivation), `B_antisymm` (`B` is alternating).
* **`prop:trivial-model` (i)**, AW3 perfectness: `blockPairing_bijective` (degree one, finite
  multiplicities) and `blockPairing_zero_bijective` (degrees `0` and `2`).
-/

open Module Complex ComplexConjugate DirectSum WeilRH.Spectral

namespace WeilRH.TrivialModel

/-! ### Degrees `0` and `2` -/

/-- Complex conjugation on `ℂ` as an antilinear map: `*_0(c) = c̄ η` and `*_2(cη) = c̄`. -/
noncomputable def conjL : ℂ →ₗ⋆[ℂ] ℂ where
  toFun c := conj c
  map_add' := map_add conj
  map_smul' c x := by simp

@[simp] lemma conjL_apply (c : ℂ) : conjL c = conj c := rfl

/-- The degree-`0` slice of the trivial model: `V^0 = ℂ·1`, `V^2 = ℂη`, `Θ_0 = 0`, `Θ_2 = 1`, the
unit product `c ∪ c'η = cc'η`, `Tr(cη) = c` and `*_0(c) = c̄η`. -/
noncomputable def model0 : WeightedStarDatum 1 0 0 ℂ ℂ ℂ where
  ΘV := 0
  ΘW := LinearMap.id
  ΘT := LinearMap.id
  cup := LinearMap.mul ℂ ℂ
  cup_derivation u v := by simp
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := conjL
  star_comm v := by simp

/-- The degree-`2` slice of the trivial model: `V^2 = ℂη`, `V^0 = ℂ·1`, `Θ_2 = 1`, `Θ_0 = 0`, the
unit product `cη ∪ c' = cc'η`, `Tr(cη) = c` and `*_2(cη) = c̄`. -/
noncomputable def model2 : WeightedStarDatum 1 0 2 ℂ ℂ ℂ where
  ΘV := LinearMap.id
  ΘW := 0
  ΘT := LinearMap.id
  cup := LinearMap.mul ℂ ℂ
  cup_derivation u v := by simp
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := conjL
  star_comm v := by simp; norm_num

lemma model0_h (c c' : ℂ) : model0.h c c' = c * conj c' := rfl

lemma model2_h (c c' : ℂ) : model2.h c c' = c * conj c' := rfl

/-- **`prop:trivial-model` (ii)**, degree `0`: `h_0(c, c') = c c̄'` is positive definite. -/
theorem model0_isPositive : model0.IsPositive where
  conj_symm u v := by rw [model0_h, model0_h, map_mul, conj_conj, mul_comm]
  re_pos u hu := by
    rw [model0_h, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_pos.2 hu

/-- **`prop:trivial-model` (ii)**, degree `2`: `h_2(cη, c'η) = c c̄'` is positive definite. -/
theorem model2_isPositive : model2.IsPositive where
  conj_symm u v := by rw [model2_h, model2_h, map_mul, conj_conj, mul_comm]
  re_pos u hu := by
    rw [model2_h, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_pos.2 hu

/-- **`prop:trivial-model` (i)**: `(V^0, Θ_0)` is a spectral core. -/
theorem spectralCore_zero : SpectralCore (0 : Module.End ℂ ℂ) :=
  spectralCore_of_finiteDimensional _

/-- **`prop:trivial-model` (i)**: `(V^2, Θ_2)` is a spectral core. -/
theorem spectralCore_two : SpectralCore (LinearMap.id : Module.End ℂ ℂ) :=
  spectralCore_of_finiteDimensional _

/-- **`prop:trivial-model` (i)**, AW3 in degrees `0` and `2`: the pairing `V^0 × V^2 → ℂ`,
`(c, c'η) ↦ cc'`, restricts to a perfect pairing on every block `V^0_ρ × V^2_{1-ρ}`. -/
theorem blockPairing_zero_bijective (σ : ℂ) :
    Function.Bijective (AW4Star.blockPairing model0.ΘV model0.ΘW model0.cup model0.tr σ (1 - σ)) := by
  by_cases hσ : σ = 0
  · subst hσ
    have h0 : model0.ΘV.maxGenEigenspace 0 = ⊤ := by
      rw [eq_top_iff]; intro x _
      rw [Module.End.mem_maxGenEigenspace]; exact ⟨1, by simp [model0]⟩
    have h1 : model0.ΘW.maxGenEigenspace (1 - 0) = ⊤ := by
      rw [eq_top_iff]; intro x _
      rw [Module.End.mem_maxGenEigenspace]; exact ⟨1, by simp [model0]⟩
    have hfin : finrank ℂ (model0.ΘW.maxGenEigenspace (1 - 0)) =
        finrank ℂ (Module.Dual ℂ (model0.ΘV.maxGenEigenspace 0)) := by
      rw [Subspace.dual_finrank_eq, h0, h1]
    have hinj : Function.Injective
        (AW4Star.blockPairing model0.ΘV model0.ΘW model0.cup model0.tr 0 (1 - 0)) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 hx) ⟨1, by rw [h0]; exact Submodule.mem_top⟩
      simp only [AW4Star.blockPairing_apply, LinearMap.zero_apply] at this
      exact Subtype.ext (by simpa [model0] using this)
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj⟩
  · -- both blocks vanish: `Θ_0 = 0` has only the eigenvalue `0`
    have hbot : model0.ΘV.maxGenEigenspace σ = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro x hx
      rw [Module.End.mem_maxGenEigenspace] at hx; obtain ⟨k, hk⟩ := hx
      have : ((-σ) ^ k) * x = 0 := by
        have h' : ((model0.ΘV - σ • 1) ^ k) x = ((-σ) ^ k) * x := by
          have : model0.ΘV - σ • 1 = (-σ) • (1 : Module.End ℂ ℂ) := by
            ext; simp [model0]
          rw [this, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]
        rwa [h'] at hk
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (neg_ne_zero.2 hσ))
    have hbot' : model0.ΘW.maxGenEigenspace (1 - σ) = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro x hx
      rw [Module.End.mem_maxGenEigenspace] at hx; obtain ⟨k, hk⟩ := hx
      have : (σ ^ k) * x = 0 := by
        have h' : ((model0.ΘW - (1 - σ) • 1) ^ k) x = (σ ^ k) * x := by
          have : model0.ΘW - (1 - σ) • 1 = σ • (1 : Module.End ℂ ℂ) := by
            ext; simp [model0]
          rw [this, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]
        rwa [h'] at hk
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hσ)
    constructor
    · intro x y _
      have hx : (x : ℂ) = 0 := (Submodule.eq_bot_iff _).1 hbot' _ x.2
      have hy : (y : ℂ) = 0 := (Submodule.eq_bot_iff _).1 hbot' _ y.2
      exact Subtype.ext (by rw [hx, hy])
    · intro f
      refine ⟨0, ?_⟩
      ext u
      have : u = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hbot _ u.2)
      simp [this]

variable {ι : Type} (ρ : ι → ℂ) [DecidableEq ι]

/-! ### `B` is alternating -/

/-- `B` is alternating: `B(u, v) = -B(v, u)` on `V^1`. -/
theorem B_antisymm (u v : V1 ι) : B u v = -B v u := by
  have key : (B : V1 ι →ₗ[ℂ] V1 ι →ₗ[ℂ] ℂ) = -(B : V1 ι →ₗ[ℂ] V1 ι →ₗ[ℂ] ℂ).flip := by
    refine DirectSum.linearMap_ext ℂ fun i => ?_
    refine LinearMap.ext_ring ?_
    refine DirectSum.linearMap_ext ℂ fun j => ?_
    refine LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.flip_apply, B_lof_lof]
    by_cases h : j = swap i
    · subst h
      simp only [swap_swap, ite_true]
      linear_combination (-sgn (swap i)) * sgn_mul_self i + sgn i * sgn_swap_mul i
    · have h' : ¬ i = swap j := fun hij => h (by rw [hij, swap_swap])
      simp [h, h']
  simpa using LinearMap.congr_fun₂ key u v

/-! ### The graded algebra `V^0 ⊕ V^1 ⊕ V^2` -/

/-- The total space `V^0 ⊕ V^1 ⊕ V^2 = ℂ·1 ⊕ V^1 ⊕ ℂη`. -/
abbrev Tot (ι : Type) := ℂ × V1 ι × ℂ

/-- The product of `def:trivial-model`: `u ∪ v = B(u, v) η` on `V^1` and the unit products
otherwise. In components, `(a, u, c)(a', u', c') = (aa', au' + a'u, ac' + ca' + B(u, u'))`. -/
noncomputable def mul (x y : Tot ι) : Tot ι :=
  (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1, x.1 * y.2.2 + x.2.2 * y.1 + B x.2.1 y.2.1)

/-- The unit `1 ∈ V^0`. -/
def one : Tot ι := (1, 0, 0)

/-- **`prop:trivial-model` (i)**, AW1: the product is associative. -/
theorem mul_assoc' (x y z : Tot ι) : mul (mul x y) z = mul x (mul y z) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y; obtain ⟨a'', u'', c''⟩ := z
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by module, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`prop:trivial-model` (i)**, AW1: the product is graded-commutative. Degree-one elements
anticommute (`B` is alternating), everything else commutes. -/
theorem mul_comm_graded (x y : Tot ι) :
    mul y x = (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1, x.1 * y.2.2 + x.2.2 * y.1 - B x.2.1 y.2.1) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y
  simp only [mul, Prod.mk.injEq]
  refine ⟨mul_comm _ _, add_comm _ _, ?_⟩
  rw [B_antisymm u' u]
  ring

/-- **`prop:trivial-model` (i)**, AW1, graded commutativity in bidegree `(1, 1)`:
`u ∪ u' = -u' ∪ u` for `u, u' ∈ V^1`. -/
theorem mul_anticomm_one (u u' : V1 ι) :
    mul ((0 : ℂ), u, (0 : ℂ)) (0, u', 0) = -mul ((0 : ℂ), u', (0 : ℂ)) (0, u, 0) := by
  simp only [mul, zero_mul, zero_smul, add_zero, zero_add, Prod.neg_mk, neg_zero, Prod.mk.injEq,
    true_and]
  exact B_antisymm u u'

/-- **`prop:trivial-model` (i)**, AW1: `1 ∈ V^0` is a left unit. -/
@[simp] theorem one_mul' (x : Tot ι) : mul one x = x := by
  obtain ⟨a, u, c⟩ := x; simp [mul, one]

/-- **`prop:trivial-model` (i)**, AW1: `1 ∈ V^0` is a right unit. -/
@[simp] theorem mul_one' (x : Tot ι) : mul x one = x := by
  obtain ⟨a, u, c⟩ := x; simp [mul, one]

/-- The flow generator on `V^0 ⊕ V^1 ⊕ V^2`: `Θ_0 = 0`, `Θ_1`, `Θ_2 = 1`. -/
noncomputable def thetaTot (x : Tot ι) : Tot ι := (0, theta ρ x.2.1, x.2.2)

/-- **`prop:trivial-model` (i)**, AW1: `Θ` is a derivation of the product,
`Θ(x ∪ y) = Θx ∪ y + x ∪ Θy`. -/
theorem thetaTot_mul (x y : Tot ι) :
    thetaTot ρ (mul x y) = mul (thetaTot ρ x) y + mul x (thetaTot ρ y) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y
  simp only [thetaTot, mul, Prod.mk_add_mk, Prod.mk.injEq, map_add, map_smul]
  refine ⟨by ring, by module, ?_⟩
  rw [B_theta ρ u u']
  ring

/-! ### AW3 perfectness in degree one -/

omit [DecidableEq ι] in
lemma theta_sub_pow_apply (σ : ℂ) (n : ℕ) (x : V1 ι) (k : ι × Bool) :
    (((theta ρ - σ • 1) ^ n) x) k = (lam ρ k - σ) ^ n * x k := by
  rw [theta, Suspension.diag_sub_pow_apply]
  have : (lam ρ k • (1 : Module.End ℂ ℂ) - σ • 1) = (lam ρ k - σ) • 1 := by rw [sub_smul]
  rw [this, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul]

omit [DecidableEq ι] in
/-- A generalized `σ`-eigenvector of `Θ_1` is supported on `{k : λ_k = σ}`. -/
lemma lam_eq_of_mem {σ : ℂ} {x : V1 ι} (hx : x ∈ (theta ρ).maxGenEigenspace σ) {k : ι × Bool}
    (hk : x k ≠ 0) : lam ρ k = σ := by
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨n, hn⟩ := hx
  have := congrArg (· k) hn
  simp only [theta_sub_pow_apply, DFinsupp.zero_apply] at this
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hk)).1

lemma lof_mem (i : ι × Bool) (a : ℂ) :
    DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) i a ∈ (theta ρ).maxGenEigenspace (lam ρ i) := by
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  ext k
  rw [theta_sub_pow_apply, lof_eval, DFinsupp.zero_apply]
  split_ifs with h
  · subst h; simp
  · simp

/-- **`prop:trivial-model` (i)**, AW3 perfectness in degree one: if every multiplicity of `Σ` is
finite, `B` restricts to a perfect pairing `V^1_{Θ∼σ} × V^1_{Θ∼1-σ} → ℂ` for every `σ`, i.e.
`V^1_{Θ∼1-σ} → (V^1_{Θ∼σ})^*` is bijective. -/
theorem blockPairing_bijective (hfin : ∀ σ, {i | lam ρ i = σ}.Finite) (σ : ℂ) :
    Function.Bijective
      (AW4Star.blockPairing (theta ρ) (theta ρ) B (LinearMap.id : ℂ →ₗ[ℂ] ℂ) σ (1 - σ)) := by
  have hfd : ∀ τ, FiniteDimensional ℂ ((theta ρ).maxGenEigenspace τ) := fun τ => by
    have hlt : Module.rank ℂ ((theta ρ).maxGenEigenspace τ) < Cardinal.aleph0 := by
      rw [rank_maxGenEigenspace_theta]
      have : Finite {i // lam ρ i = τ} := (hfin τ).to_subtype
      exact Cardinal.lt_aleph0_of_finite _
    exact rank_lt_aleph0_iff.1 hlt
  have hcard : Cardinal.mk {i // lam ρ i = 1 - σ} = Cardinal.mk {i // lam ρ i = σ} :=
    Cardinal.mk_congr
      { toFun := fun i => ⟨swap i.1, by
          have := lam_add_lam_swap ρ i.1; rw [i.2] at this; linear_combination this⟩
        invFun := fun i => ⟨swap i.1, by
          have := lam_add_lam_swap ρ i.1; rw [i.2] at this; linear_combination this⟩
        left_inv := fun i => Subtype.ext (swap_swap _)
        right_inv := fun i => Subtype.ext (swap_swap _) }
  have hdim : finrank ℂ ((theta ρ).maxGenEigenspace (1 - σ)) =
      finrank ℂ (Module.Dual ℂ ((theta ρ).maxGenEigenspace σ)) := by
    rw [Subspace.dual_finrank_eq]
    simp only [Module.finrank, rank_maxGenEigenspace_theta, hcard]
  have hinj : Function.Injective
      (AW4Star.blockPairing (theta ρ) (theta ρ) B (LinearMap.id : ℂ →ₗ[ℂ] ℂ) σ (1 - σ)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have hx0 : (x : V1 ι) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨k, hk⟩ : ∃ k, (x : V1 ι) k ≠ 0 := by
      by_contra h; push Not at h; exact hx0 (DFinsupp.ext h)
    have hlk := lam_eq_of_mem ρ x.2 hk
    have h2 : lam ρ (swap k) = σ := by
      have := lam_add_lam_swap ρ k; rw [hlk] at this; linear_combination this
    have hmem := lof_mem ρ (swap k) 1
    rw [h2] at hmem
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hx) ⟨_, hmem⟩
    rw [AW4Star.blockPairing_apply, LinearMap.zero_apply, LinearMap.id_apply, B_lof,
      swap_swap] at this
    exact hk ((mul_eq_zero.1 this).resolve_left (mul_ne_zero one_ne_zero (sgn_ne_zero _)))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

end WeilRH.TrivialModel
