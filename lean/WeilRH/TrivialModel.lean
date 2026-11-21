/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Duality
import WeilRH.LocalCores
import WeilRH.OneBranch

/-!
# The trivial model (`def:trivial-model`, `prop:trivial-model`)

Source: the manuscript `latex/notes.tex`, `def:trivial-model` and `prop:trivial-model`.

The divisor `Σ` is encoded by a family `ρ : ι → ℂ` of designated first members, one for each pair
of basis vectors `(e_p, f_p)`: `e_p` has eigenvalue `ρ_p` and `f_p` has eigenvalue `1 - ρ_p`. A pair
at `1/2` is a `p` with `ρ_p = 1/2`. Symmetry of `Σ` under `ρ ↦ 1 - ρ` and evenness of `m(1/2)`
then hold by construction, and every such divisor arises this way. The multiplicity of `σ` in `Σ`
is `#{i : ι × Bool // lam ρ i = σ}`.

`V^1 = ⨁_{ι × Bool} ℂ` with `Θ_1 = diag(lam ρ)`; the degree-one slice of the trivial model is the
`WeightedStarDatum 1 0 1 V^1 V^1 ℂ` with cup product `u ∪ v = B(u, v) η` (`V^2 = ℂη ≅ ℂ`),
`Θ_2 = 1`, `Tr(cη) = c`, and `*_1 e_p = f_p`, `*_1 f_p = -e_p` on the line and `*_1 = 0` off it.

## Main results

* `TrivialModel.model`: the degree-one slice of `def:trivial-model`.
* **`prop:trivial-model` (i)**: `model_cup_derivation` (AW1 in bidegree `(1, 1)`),
  `model_tr_equivariant` (AW3 trace), `B_nondegenerate` (nondegeneracy of `B`), `spec_theta` and
  `rank_maxGenEigenspace_theta` (`Sp_1 = Σ` with multiplicities), `spectralCore_theta`.
* **`prop:trivial-model` (ii)**: `model_isPositive` (positivity of `h_1`) and `star_star`
  (`*_1² = -1`).
* **`prop:trivial-model` (iii)**: `exists_datum_iff`.

Degrees `0` and `2`, the full graded product and AW3's blockwise perfectness are in
`WeilRH.TrivialModelFull`.
-/

open Module Complex ComplexConjugate DirectSum WeilRH.Spectral

namespace WeilRH.TrivialModel

variable {ι : Type} (ρ : ι → ℂ)

/-- The eigenvalue of the basis vector indexed by `i`: `ρ_p` for `e_p = (p, true)` and `1 - ρ_p`
for `f_p = (p, false)`. -/
def lam (i : ι × Bool) : ℂ := if i.2 then ρ i.1 else 1 - ρ i.1

/-- The partner of a basis vector: `e_p ↔ f_p`. -/
def swap (i : ι × Bool) : ι × Bool := (i.1, !i.2)

/-- `B(e_p, f_p) = 1 = -B(f_p, e_p)`: the sign of the first argument. -/
def sgn (i : ι × Bool) : ℂ := if i.2 then 1 else -1

@[simp] lemma swap_swap (i : ι × Bool) : swap (swap i) = i := by
  simp [swap]

lemma swap_ne (i : ι × Bool) : swap i ≠ i := by
  obtain ⟨p, b⟩ := i; cases b <;> simp [swap]

lemma swap_eq_iff {i j : ι × Bool} : swap i = j ↔ i = swap j := by
  constructor <;> rintro rfl <;> simp

lemma sgn_mul_self (i : ι × Bool) : sgn i * sgn i = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_swap_mul (i : ι × Bool) : sgn (swap i) * sgn i = -1 := by
  obtain ⟨p, b⟩ := i; cases b <;> simp [sgn, swap]

@[simp] lemma conj_sgn (i : ι × Bool) : conj (sgn i) = sgn i := by
  unfold sgn; split_ifs <;> simp

lemma sgn_ne_zero (i : ι × Bool) : sgn i ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

lemma lam_add_lam_swap (i : ι × Bool) : lam ρ i + lam ρ (swap i) = 1 := by
  obtain ⟨p, b⟩ := i; cases b <;> simp [lam, swap]

/-- On the line `Re ρ = 1/2`, `1 - ρ = conj ρ`, so the partner's eigenvalue is the conjugate. -/
lemma lam_swap_of_line (hline : ∀ p, (ρ p).re = 1 / 2) (i : ι × Bool) :
    lam ρ (swap i) = conj (lam ρ i) := by
  have key : ∀ p, 1 - ρ p = conj (ρ p) := fun p =>
    Complex.ext (by simp [hline p]; norm_num) (by simp)
  obtain ⟨p, b⟩ := i
  cases b
  · simp [lam, swap, key]
  · simp [lam, swap, key]

variable [DecidableEq ι]

/-- `V^1 = ⨁_{ι × Bool} ℂ`, the algebraic direct sum of the lines `ℂ e_{ρ,k}`. -/
abbrev V1 (ι : Type) := ⨁ _ : ι × Bool, ℂ

lemma lof_eval (j k : ι × Bool) (b : ℂ) :
    (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) j b) k = if j = k then b else 0 := by
  split_ifs with h
  · subst h; exact DirectSum.lof_apply (M := fun _ : ι × Bool => ℂ) ℂ j b
  · rw [DirectSum.lof_eq_of]; exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)

/-- `Θ_1 e = λ e` on each basis line. -/
noncomputable def theta : Module.End ℂ (V1 ι) :=
  Suspension.diag fun i => lam ρ i • (1 : Module.End ℂ ℂ)

omit [DecidableEq ι] in
lemma theta_apply (x : V1 ι) (k : ι × Bool) : theta ρ x k = lam ρ k * x k := by
  simp [theta, Suspension.diag_apply]

/-- The alternating form `B` on `V^1`: `B(e_p, f_p) = 1 = -B(f_p, e_p)`, zero on other pairs. -/
noncomputable def B : V1 ι →ₗ[ℂ] V1 ι →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ (ι × Bool) _ fun i =>
    LinearMap.toSpanSingleton ℂ _ (sgn i • DirectSum.component ℂ (ι × Bool) (fun _ => ℂ) (swap i))

lemma B_lof (i : ι × Bool) (a : ℂ) (v : V1 ι) :
    B (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) i a) v = a * sgn i * v (swap i) := by
  simp only [B, DirectSum.toModule_lof, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    smul_eq_mul, ← DirectSum.apply_eq_component]
  ring

/-- `B(u, v) = Σ_{i ∈ s} sgn(i) u_i v_{swap i}` for any finite `s` containing the support of `u`. -/
lemma B_eq_sum (u v : V1 ι) {s : Finset (ι × Bool)} (hs : u.support ⊆ s) :
    B u v = ∑ i ∈ s, u i * sgn i * v (swap i) := by
  conv_lhs => rw [← DirectSum.sum_support_of u]
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [← DirectSum.lof_eq_of ℂ, B_lof]
  refine Finset.sum_subset hs fun i _ hi => ?_
  rw [DFinsupp.notMem_support_iff.1 hi]; ring

lemma B_lof_lof (i j : ι × Bool) :
    B (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) i 1) (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) j 1) =
      if j = swap i then sgn i else 0 := by
  rw [B_lof, lof_eval]; split_ifs <;> ring

/-- `B` is alternating on basis vectors: `B(e_p, f_p) = 1`, `B(f_p, e_p) = -1`. -/
lemma B_e_f (p : ι) :
    B (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (p, true) 1)
      (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (p, false) 1) = 1 ∧
    B (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (p, false) 1)
      (DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (p, true) 1) = -1 := by
  simp [B_lof_lof, swap, sgn]

/-- **`prop:trivial-model` (i)**, the derivation rule of AW1 in bidegree `(1, 1)`:
`B(Θu, v) + B(u, Θv) = B(u, v)`, because `B(e_{ρ,k}, e_{ρ',l}) ≠ 0` forces `ρ + ρ' = 1`. -/
theorem B_theta (u v : V1 ι) : B u v = B (theta ρ u) v + B u (theta ρ v) := by
  have hsu : (theta ρ u).support ⊆ u.support := fun i hi => by
    rw [DFinsupp.mem_support_iff] at hi ⊢; rw [theta_apply] at hi; exact right_ne_zero_of_mul hi
  rw [B_eq_sum u v subset_rfl, B_eq_sum _ v hsu, B_eq_sum u _ subset_rfl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [theta_apply, theta_apply]
  have := lam_add_lam_swap ρ i
  linear_combination (-(u i * sgn i * v (swap i))) * this

/-- **`prop:trivial-model` (i)**, AW3 nondegeneracy: `B` is nondegenerate on `V^1`. -/
theorem B_nondegenerate {u : V1 ι} (hu : u ≠ 0) : ∃ v, B u v ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push Not at h; exact hu (DFinsupp.ext h)
  refine ⟨DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (swap i) 1, ?_⟩
  rw [B_eq_sum u _ (Finset.subset_union_left (s₂ := {i}))]
  rw [Finset.sum_eq_single i]
  · rw [lof_eval]; simp only [↓reduceIte, mul_one]
    exact mul_ne_zero hi (sgn_ne_zero i)
  · intro j _ hj
    have hne : swap i ≠ swap j := fun h => hj (by simpa using congrArg swap h.symm)
    rw [lof_eval]; simp [hne]
  · intro h; exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self i)) h

section Star

/-- Componentwise conjugation on `V^1`. -/
noncomputable def conjV : V1 ι →ₗ⋆[ℂ] V1 ι where
  toFun x := DFinsupp.mapRange (fun _ c => conj c) (fun _ => map_zero _) x
  map_add' x y := by
    ext i; simp [DFinsupp.mapRange_apply]
  map_smul' c x := by
    ext i
    change conj ((c • x) i) = (conj c • DFinsupp.mapRange (fun _ c => conj c) (fun _ => map_zero _) x) i
    rw [DirectSum.smul_apply, DirectSum.smul_apply]
    simp [DFinsupp.mapRange_apply]

omit [DecidableEq ι] in
@[simp] lemma conjV_apply (x : V1 ι) (k : ι × Bool) : conjV x k = conj (x k) := by
  simp [conjV, DFinsupp.mapRange_apply]

/-- The linear part of `*_1`: `e_p ↦ f_p`, `f_p ↦ -e_p`. -/
noncomputable def swapSign : V1 ι →ₗ[ℂ] V1 ι :=
  DirectSum.toModule ℂ (ι × Bool) _ fun i => sgn i • DirectSum.lof ℂ (ι × Bool) (fun _ => ℂ) (swap i)

lemma swapSign_apply (x : V1 ι) (k : ι × Bool) :
    swapSign x k = sgn (swap k) * x (swap k) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [← DirectSum.lof_eq_of ℂ]
    simp only [swapSign, DirectSum.toModule_lof, LinearMap.smul_apply, DirectSum.smul_apply,
      lof_eval, smul_eq_mul, swap_eq_iff]
    split_ifs with h
    · subst h; simp
    · ring
  | add x y hx hy => simp [hx, hy, mul_add]

/-- The star `*_1` on the line: `*_1 e_p = f_p`, `*_1 f_p = -e_p`, antilinear. -/
noncomputable def starLine : V1 ι →ₗ⋆[ℂ] V1 ι := swapSign.comp conjV

lemma starLine_apply (x : V1 ι) (k : ι × Bool) :
    starLine x k = sgn (swap k) * conj (x (swap k)) := by
  simp [starLine, swapSign_apply]

/-- **`prop:trivial-model` (ii)**, `*_1² = -1`. -/
theorem star_star (x : V1 ι) : starLine (starLine x) = -x := by
  ext k
  rw [starLine_apply, starLine_apply, swap_swap, map_mul, conj_sgn, conj_conj,
    DFinsupp.neg_apply, ← mul_assoc, sgn_swap_mul, neg_one_mul]

/-- The star `*_1` of `def:trivial-model`: `starLine` if `Σ` lies on `Re s = 1/2`, else `0`. -/
noncomputable def star1 : V1 ι →ₗ⋆[ℂ] V1 ι := by
  classical exact if ∀ p, (ρ p).re = 1 / 2 then starLine else 0

lemma star1_of_line (h : ∀ p, (ρ p).re = 1 / 2) : star1 ρ = starLine := by
  unfold star1; simp [h]

lemma star1_of_not (h : ¬ ∀ p, (ρ p).re = 1 / 2) : star1 ρ = 0 := by
  unfold star1
  split_ifs with h'
  · exact absurd h' h
  · rfl

lemma theta_starLine (hline : ∀ p, (ρ p).re = 1 / 2) (v : V1 ι) :
    theta ρ (starLine v) = starLine (theta ρ v) := by
  ext k
  have h := lam_swap_of_line ρ hline (swap k)
  rw [swap_swap] at h
  rw [theta_apply, starLine_apply, starLine_apply, theta_apply, map_mul, h]
  ring

end Star

/-- The degree-one slice of the trivial model (`def:trivial-model`): a Weil datum of type `(1, 0)`
in degree `1`, with `V^1 = V^{2d-1}`, `V^2 = ℂη ≅ ℂ`, `Θ_2 = 1`, `u ∪ v = B(u, v) η`,
`Tr(cη) = c` and the star `*_1` of `star1`. The two fields `cup_derivation` and `tr_equivariant` are
**`prop:trivial-model` (i)** in bidegree `(1, 1)`. -/
noncomputable def model : WeightedStarDatum 1 0 1 (V1 ι) (V1 ι) ℂ where
  ΘV := theta ρ
  ΘW := theta ρ
  ΘT := LinearMap.id
  cup := B
  cup_derivation u v := by rw [LinearMap.id_apply, B_theta ρ u v]
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := star1 ρ
  star_comm v := by
    by_cases h : ∀ p, (ρ p).re = 1 / 2
    · rw [star1_of_line ρ h, theta_starLine ρ h]; simp
    · rw [star1_of_not ρ h]; simp

@[simp] lemma model_ΘV : (model ρ).ΘV = theta ρ := rfl

/-- **`prop:trivial-model` (i)**, AW1 for `U = 𝟙` in bidegree `(1, 1)`. -/
theorem model_cup_derivation (u v : V1 ι) :
    (model ρ).ΘT ((model ρ).cup u v) = (model ρ).cup ((model ρ).ΘV u) v +
      (model ρ).cup u ((model ρ).ΘW v) :=
  (model ρ).cup_derivation u v

/-- **`prop:trivial-model` (i)**, the AW3 trace: `Tr(Θ_2 x) = Tr(x)`. -/
theorem model_tr_equivariant (x : ℂ) : (model ρ).tr ((model ρ).ΘT x) = (model ρ).tr x := by
  simp [model]

/-- On the line, `h_1(u, v) = Σ_i u_i conj(v_i)`: the standard form in the basis `e_{ρ,k}`. -/
lemma h_eq_sum (hline : ∀ p, (ρ p).re = 1 / 2) (u v : V1 ι) {s : Finset (ι × Bool)}
    (hs : u.support ⊆ s) : (model ρ).h u v = ∑ i ∈ s, u i * conj (v i) := by
  simp only [WeightedStarDatum.h, WeightedStarDatum.B, model, LinearMap.id_apply,
    star1_of_line ρ hline]
  rw [B_eq_sum u _ hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starLine_apply, swap_swap]
  linear_combination (u i * conj (v i)) * sgn_mul_self i

/-- **`prop:trivial-model` (ii)**: if `Σ` lies on `Re s = 1/2`, then `h_1` is positive definite
Hermitian (AW4 positivity; the star law is the field `star_comm` of `model`). -/
theorem model_isPositive (hline : ∀ p, (ρ p).re = 1 / 2) : (model ρ).IsPositive where
  conj_symm u v := by
    classical
    rw [h_eq_sum ρ hline u v (Finset.subset_union_left (s₂ := v.support)),
      h_eq_sum ρ hline v u (Finset.subset_union_right (s₁ := u.support)), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, conj_conj, mul_comm]
  re_pos u hu := by
    classical
    rw [h_eq_sum ρ hline u u subset_rfl, Complex.re_sum]
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push Not at h; exact hu (DFinsupp.ext h)
    have hmem : i ∈ u.support := DFinsupp.mem_support_iff.2 hi
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, hmem, ?_⟩
    · rw [Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
    · rw [Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_pos.2 hi

/-- **`prop:trivial-model` (ii)**, `*_1² = -1` for the star of the model on the line. -/
theorem model_star_star (hline : ∀ p, (ρ p).re = 1 / 2) (x : V1 ι) :
    (model ρ).star ((model ρ).star x) = -x := by
  change star1 ρ (star1 ρ x) = -x
  rw [star1_of_line ρ hline]; exact star_star x

/-! ### The spectrum: `Sp_1 = Σ` -/

lemma rank_maxGen_scalar (c σ : ℂ) :
    Module.rank ℂ ((c • (1 : Module.End ℂ ℂ)).maxGenEigenspace σ) = if c = σ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [OneBranch.maxGen_scalar_self, rank_top, rank_self]
  · rw [OneBranch.maxGen_scalar_eq_bot (Ne.symm h), rank_bot]

/-- **`prop:trivial-model` (i)**, `Sp_1 = Σ` with multiplicities: the generalized `σ`-eigenspace
of `Θ_1` has dimension `#{i // λ_i = σ}`, the multiplicity of `σ` in `Σ`. -/
theorem rank_maxGenEigenspace_theta (σ : ℂ) :
    Module.rank ℂ ((theta ρ).maxGenEigenspace σ) = Cardinal.mk {i // lam ρ i = σ} := by
  rw [theta, R7.rank_maxGenEigenspace_diag]
  simp_rw [rank_maxGen_scalar]
  rw [← Cardinal.mk_congr (Equiv.sigmaPLiftEquivSubtype fun i => lam ρ i = σ), Cardinal.mk_sigma]
  congr 1; ext i
  split_ifs with h <;> simp [h]

/-- **`prop:trivial-model` (i)**, the support of `Sp_1`: `spec Θ_1 = {ρ_p} ∪ {1 - ρ_p}`. -/
theorem spec_theta : spec (theta ρ) = Set.range (lam ρ) := by
  ext σ
  rw [theta, R7.spec_diag]
  simp only [OneBranch.spec_scalar, Set.mem_singleton_iff, Set.mem_range, eq_comm]

/-- **`prop:trivial-model` (i)**, the spectral-core condition. If every multiplicity of `Σ` is
finite and `Σ` has no finite accumulation point, `(V^1, Θ_1)` is a spectral core. -/
theorem spectralCore_theta (hfin : ∀ σ, {i | lam ρ i = σ}.Finite)
    (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range (lam ρ)))) :
    SpectralCore (theta ρ) where
  iSup_eq_top := by
    rw [eq_top_iff]
    rintro x -
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      refine Submodule.mem_iSup_of_mem (lam ρ i) ?_
      rw [Module.End.mem_maxGenEigenspace]
      refine ⟨1, ?_⟩
      ext k
      rw [pow_one, LinearMap.sub_apply, ← DirectSum.lof_eq_of ℂ, DFinsupp.sub_apply, theta_apply,
        LinearMap.smul_apply, Module.End.one_apply, DirectSum.smul_apply, lof_eval, smul_eq_mul]
      split_ifs with h
      · subst h; simp
      · simp
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  finiteDimensional σ := by
    have hlt : Module.rank ℂ ((theta ρ).maxGenEigenspace σ) < Cardinal.aleph0 := by
      rw [rank_maxGenEigenspace_theta]
      have : Finite {i // lam ρ i = σ} := (hfin σ).to_subtype
      exact Cardinal.lt_aleph0_of_finite _
    exact rank_lt_aleph0_iff.1 hlt
  noAccPt z := by rw [spec_theta]; exact hdisc z

/-- **`prop:trivial-model` (iii).** Some Weil datum of type `(1, 0)` in degree `1` with
`Sp_1 = Σ` (with multiplicities) satisfies AW1, AW3 and AW4 (star law and positivity of `h_1`) iff
`Σ` lies on `Re s = 1/2`. -/
theorem exists_datum_iff :
    (∃ (V W T : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W)
      (_ : Module ℂ W) (_ : AddCommGroup T) (_ : Module ℂ T)
      (D : WeightedStarDatum 1 0 1 V W T), D.IsPositive ∧
        ∀ σ, Module.rank ℂ (D.ΘV.maxGenEigenspace σ) = Cardinal.mk {i // lam ρ i = σ}) ↔
      ∀ p, (ρ p).re = 1 / 2 := by
  constructor
  · rintro ⟨V, W, T, _, _, _, _, _, _, D, hD, hrank⟩ p
    have hne : D.ΘV.maxGenEigenspace (ρ p) ≠ ⊥ := by
      intro h
      have := hrank (ρ p)
      rw [h, rank_bot] at this
      have hpos : (Cardinal.mk {i // lam ρ i = ρ p}) ≠ 0 :=
        Cardinal.mk_ne_zero_iff.2 ⟨⟨(p, true), by simp [lam]⟩⟩
      exact hpos this.symm
    have hev : D.ΘV.HasEigenvalue (ρ p) :=
      (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (f := D.ΘV) (μ := ρ p) (k := ⊤)
        (by simp)).1 hne
    exact WeightedStarDatum.re_eq_half_of_curve D hD hev
  · intro hline
    exact ⟨V1 ι, V1 ι, ℂ, _, _, _, _, _, _, model ρ, model_isPositive ρ hline,
      rank_maxGenEigenspace_theta ρ⟩

end WeilRH.TrivialModel
