/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Content
import WeilRH.Negative

/-!
# Assembling the blocks of `prop:content` (iii)

Source: the manuscript `latex/notes.tex`, `prop:content` (iii) and its proof.

The proof of (iii) takes `V^1` to be the algebraic direct sum of three kinds of block: the trivial
model on the part of `Σ` on the line, one real-pair plane `ℂe ⊕ ℂf` for each real pair and unit of
multiplicity, and one block of `def:R2-block` for each quartet and unit of multiplicity, with `B`
and `*` the direct sums of the blocks' forms and stars. All three blocks share one shape, which this
file formalizes once (`PairingModel.Data`): a basis `(e_x)_{x ∈ X}` of `V = ⨁_X ℂ` with

* `Θ e_x = λ_x e_x`;
* `B(e_x, e_y) = sgn(x)` if `y = σ x` and `0` otherwise, for an involution `σ` with
  `λ_x + λ_{σx} = 1`;
* `(*v)_x = t_x · conj(v_{τ x})` for an involution `τ` with `λ_x = conj(λ_{τ x})`.

Then `h(u, v) = Σ_x g_x u_x conj(v_{π x})`, where `g_x = sgn(x) t(σ x)` and `π = τ ∘ σ`
(`PairingModel.h_eq_sum`).

## Main results

* `PairingModel.datum`: a Weil datum of type `(1, 0)` in degree one (AW1 for `U = 𝟙`, the AW3 trace
  and the star law of AW4) for any `PairingModel.Data`.
* `PairingModel.rank_maxGenEigenspace_theta`: `Sp_1` is `λ` with multiplicities.
* `PairingModel.h_conj_symm`, `PairingModel.h_nondegenerate`: `h_1` is Hermitian and nondegenerate
  when `π` is an involution with `conj(g_x) = g_{π x}` and `t` vanishes nowhere.
* `PairingModel.h_add_self`, `PairingModel.h_sub_self`: `h_1(e_x ± e_{πx}, e_x ± e_{πx}) =
  ±(g_x + g_{πx})` when `π x ≠ x`.
* **`prop:content` (iii)**: `ContentAssembly.content_indef`. For a divisor given by line points
  `ρL`, real pairs `ρP` and quartets `lQ` (one family member per unit of multiplicity), the
  direct sum `ContentAssembly.D` of the three kinds of block is a Weil datum of type `(1, 0)` with
  `Sp_1 = Σ` with multiplicities, `h_1` Hermitian, nondegenerate and satisfying `(eq:inf-pol)` with
  weight one, and `h_1` indefinite as soon as there is a real pair or a quartet.

The quartet block is the block of `def:R2-block` with `λ = 1/2 + a + iT`: `B(u, v) = uᵀΩv` and
`*v = S v̄` in the coordinates `(e₁, e₂, f₁, f₂)` ordered as `Fin 4`.
-/

open Module Complex ComplexConjugate DirectSum WeilRH.Spectral

namespace WeilRH.PairingModel

/-- The shape shared by the blocks of `prop:content` (iii): eigenvalues `lam`, the pairing
involution `swp` of `B` with signs `sgn`, and the involution `tau` and coefficients `t` of the
star. -/
structure Data (X : Type) where
  /-- The involution pairing `e_x` with `e_{σ x}` under `B`. -/
  swp : X → X
  swp_swp : ∀ x, swp (swp x) = x
  /-- `B(e_x, e_{σ x}) = sgn x`. -/
  sgn : X → ℂ
  sgn_ne : ∀ x, sgn x ≠ 0
  /-- The eigenvalue of `Θ_1` on `e_x`. -/
  lam : X → ℂ
  lam_add : ∀ x, lam x + lam (swp x) = 1
  /-- The involution of the star. -/
  tau : X → X
  tau_tau : ∀ x, tau (tau x) = x
  /-- The coefficients of the star. -/
  t : X → ℂ
  t_ne : ∀ x, t x ≠ 0
  lam_tau : ∀ x, lam x = conj (lam (tau x))

variable {X : Type} (P : Data X)

namespace Data

/-- `g_x = sgn(x) t(σ x)`, the coefficient of `h_1`. -/
def g (x : X) : ℂ := P.sgn x * P.t (P.swp x)

/-- `π = τ ∘ σ`, the involution of `h_1`. -/
def π (x : X) : X := P.tau (P.swp x)

lemma swp_injective : Function.Injective P.swp :=
  fun a b h => by rw [← P.swp_swp a, h, P.swp_swp]

lemma tau_eq_iff {a b : X} : P.tau a = b ↔ a = P.tau b :=
  ⟨fun h => by rw [← h, P.tau_tau], fun h => by rw [h, P.tau_tau]⟩

end Data

variable [DecidableEq X]

/-- `V^1 = ⨁_X ℂ`. -/
abbrev V (X : Type) := ⨁ _ : X, ℂ

lemma lof_eval (j k : X) (b : ℂ) :
    (DirectSum.lof ℂ X (fun _ => ℂ) j b) k = if j = k then b else 0 := by
  split_ifs with h
  · subst h; exact DirectSum.lof_apply (M := fun _ : X => ℂ) ℂ j b
  · rw [DirectSum.lof_eq_of]; exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)

/-- `Θ_1 e_x = λ_x e_x`. -/
noncomputable def theta : Module.End ℂ (V X) :=
  Suspension.diag fun i => P.lam i • (1 : Module.End ℂ ℂ)

omit [DecidableEq X] in
lemma theta_apply (x : V X) (k : X) : theta P x k = P.lam k * x k := by
  simp [theta, Suspension.diag_apply]

/-- The form `B`: `B(e_x, e_y) = sgn(x)` if `y = σ x`, else `0`. -/
noncomputable def B : V X →ₗ[ℂ] V X →ₗ[ℂ] ℂ :=
  DirectSum.toModule ℂ X _ fun i =>
    LinearMap.toSpanSingleton ℂ _ (P.sgn i • DirectSum.component ℂ X (fun _ => ℂ) (P.swp i))

lemma B_lof (i : X) (a : ℂ) (v : V X) :
    B P (DirectSum.lof ℂ X (fun _ => ℂ) i a) v = a * P.sgn i * v (P.swp i) := by
  simp only [B, DirectSum.toModule_lof, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    smul_eq_mul, ← DirectSum.apply_eq_component]
  ring

/-- `B(u, v) = Σ_{i ∈ s} sgn(i) u_i v_{σ i}` for any finite `s` containing the support of `u`. -/
lemma B_eq_sum (u v : V X) {s : Finset X} (hs : u.support ⊆ s) :
    B P u v = ∑ i ∈ s, u i * P.sgn i * v (P.swp i) := by
  conv_lhs => rw [← DirectSum.sum_support_of u]
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [← DirectSum.lof_eq_of ℂ, B_lof]
  refine Finset.sum_subset hs fun i _ hi => ?_
  rw [DFinsupp.notMem_support_iff.1 hi]; ring

/-- AW1 in bidegree `(1, 1)`: `B(u, v) = B(Θu, v) + B(u, Θv)`. -/
theorem B_theta (u v : V X) : B P u v = B P (theta P u) v + B P u (theta P v) := by
  have hsu : (theta P u).support ⊆ u.support := fun i hi => by
    rw [DFinsupp.mem_support_iff] at hi ⊢; rw [theta_apply] at hi; exact right_ne_zero_of_mul hi
  rw [B_eq_sum P u v subset_rfl, B_eq_sum P _ v hsu, B_eq_sum P u _ subset_rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [theta_apply, theta_apply]
  have := P.lam_add i
  linear_combination (-(u i * P.sgn i * v (P.swp i))) * this

/-- `B` is nondegenerate. -/
theorem B_nondegenerate {u : V X} (hu : u ≠ 0) : ∃ v, B P u v ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push Not at h; exact hu (DFinsupp.ext h)
  refine ⟨DirectSum.lof ℂ X (fun _ => ℂ) (P.swp i) 1, ?_⟩
  rw [B_eq_sum P u _ (Finset.subset_union_left (s₂ := {i}))]
  rw [Finset.sum_eq_single i]
  · rw [lof_eval]; simp only [↓reduceIte, mul_one]
    exact mul_ne_zero hi (P.sgn_ne i)
  · intro j _ hj
    have hne : P.swp i ≠ P.swp j := fun h => hj (P.swp_injective h).symm
    rw [lof_eval]; simp [hne]
  · intro h; exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self i)) h

/-- Componentwise conjugation on `V`. -/
noncomputable def conjV : V X →ₗ⋆[ℂ] V X where
  toFun x := DFinsupp.mapRange (fun _ c => conj c) (fun _ => map_zero _) x
  map_add' x y := by
    ext i; simp [DFinsupp.mapRange_apply]
  map_smul' c x := by
    ext i
    change conj ((c • x) i) =
      (conj c • DFinsupp.mapRange (fun _ c => conj c) (fun _ => map_zero _) x) i
    rw [DirectSum.smul_apply, DirectSum.smul_apply]
    simp [DFinsupp.mapRange_apply]

omit [DecidableEq X] in
@[simp] lemma conjV_apply (x : V X) (k : X) : conjV x k = conj (x k) := by
  simp [conjV, DFinsupp.mapRange_apply]

/-- The linear part of the star: `(L x)_k = t_k x_{τ k}`. -/
noncomputable def perm : V X →ₗ[ℂ] V X :=
  DirectSum.toModule ℂ X _ fun i => P.t (P.tau i) • DirectSum.lof ℂ X (fun _ => ℂ) (P.tau i)

lemma perm_apply (x : V X) (k : X) : perm P x k = P.t k * x (P.tau k) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [← DirectSum.lof_eq_of ℂ]
    simp only [perm, DirectSum.toModule_lof, LinearMap.smul_apply, DirectSum.smul_apply,
      lof_eval, smul_eq_mul, P.tau_eq_iff]
    split_ifs with h
    · subst h; simp [P.tau_tau]
    · ring
  | add x y hx hy => simp [hx, hy, mul_add]

/-- The star `*_1`: `(*v)_k = t_k conj(v_{τ k})`. -/
noncomputable def star : V X →ₗ⋆[ℂ] V X := (perm P).comp conjV

lemma star_apply (x : V X) (k : X) : star P x k = P.t k * conj (x (P.tau k)) := by
  simp [star, perm_apply]

/-- The star law of AW4 (`d = j = 1`): `Θ ∘ * = * ∘ Θ`. -/
lemma theta_star (v : V X) : theta P (star P v) = star P (theta P v) := by
  ext k
  rw [theta_apply, star_apply, star_apply, theta_apply, map_mul, ← P.lam_tau k]
  ring

/-- The Weil datum of type `(1, 0)` in degree one: `V^2 = ℂη ≅ ℂ`, `Θ_2 = 1`, `u ∪ v = B(u, v) η`,
`Tr(cη) = c`. The fields `cup_derivation`, `tr_equivariant` and `star_comm` are AW1 for `U = 𝟙`,
the AW3 trace and the star law of AW4. -/
noncomputable def datum : WeightedStarDatum 1 0 1 (V X) (V X) ℂ where
  ΘV := theta P
  ΘW := theta P
  ΘT := LinearMap.id
  cup := B P
  cup_derivation u v := by rw [LinearMap.id_apply, B_theta P u v]
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := star P
  star_comm v := by rw [theta_star]; simp

@[simp] lemma datum_ΘV : (datum P).ΘV = theta P := rfl

/-- `h_1(u, v) = Σ_{i ∈ s} g_i u_i conj(v_{π i})` for any finite `s` containing the support of
`u`. -/
lemma h_eq_sum (u v : V X) {s : Finset X} (hs : u.support ⊆ s) :
    (datum P).h u v = ∑ i ∈ s, P.g i * u i * conj (v (P.π i)) := by
  simp only [WeightedStarDatum.h, WeightedStarDatum.B, datum, LinearMap.id_apply]
  rw [B_eq_sum P u _ hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_apply]; simp only [Data.g, Data.π]; ring

lemma h_lof_lof (i j : X) :
    (datum P).h (DirectSum.lof ℂ X (fun _ => ℂ) i 1) (DirectSum.lof ℂ X (fun _ => ℂ) j 1) =
      if j = P.π i then P.g i else 0 := by
  classical
  rw [h_eq_sum P _ _ (s := {i}) (fun k hk => by
    rw [DFinsupp.mem_support_iff, lof_eval] at hk
    split_ifs at hk with h
    · exact Finset.mem_singleton.2 h.symm
    · exact absurd rfl hk)]
  rw [Finset.sum_singleton, lof_eval, lof_eval]
  split_ifs <;> simp_all

variable (hπ : ∀ x, P.π (P.π x) = x)

omit [DecidableEq X] in
include hπ in
lemma π_injective : Function.Injective P.π :=
  fun a b h => by rw [← hπ a, h, hπ]

include hπ in
/-- `h_1` is Hermitian when `π` is an involution with `conj(g_x) = g_{π x}`. -/
theorem h_conj_symm (hg : ∀ x, conj (P.g x) = P.g (P.π x)) (u v : V X) :
    conj ((datum P).h u v) = (datum P).h v u := by
  classical
  set S := u.support ∪ v.support
  set s := S ∪ S.image P.π
  have hs : ∀ i ∈ s, P.π i ∈ s := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [hπ]; exact Finset.mem_union_left _ hj
  rw [h_eq_sum P u v (s := s) (fun i hi => Finset.mem_union_left _ (Finset.mem_union_left _ hi)),
    h_eq_sum P v u (s := s) (fun i hi => Finset.mem_union_left _ (Finset.mem_union_right _ hi)),
    map_sum]
  refine Finset.sum_nbij' P.π P.π (fun i hi => hs i hi) (fun i hi => hs i hi)
    (fun i _ => hπ i) (fun i _ => hπ i) fun i _ => ?_
  rw [map_mul, map_mul, conj_conj, hg, hπ]
  ring

include hπ in
/-- `h_1` is nondegenerate. -/
theorem h_nondegenerate {u : V X} (hu : u ≠ 0) : ∃ v, (datum P).h u v ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push Not at h; exact hu (DFinsupp.ext h)
  refine ⟨DirectSum.lof ℂ X (fun _ => ℂ) (P.π i) 1, ?_⟩
  rw [h_eq_sum P u _ (Finset.subset_union_left (s₂ := {i}))]
  rw [Finset.sum_eq_single i]
  · rw [lof_eval]; simp only [↓reduceIte, map_one, mul_one]
    exact mul_ne_zero (mul_ne_zero (P.sgn_ne i) (P.t_ne _)) hi
  · intro j _ hj
    have hne : P.π i ≠ P.π j := fun h => hj (π_injective P hπ h).symm
    rw [lof_eval]; simp [hne]
  · intro h; exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self i)) h

include hπ in
/-- `h_1(e_x + c e_{πx}, e_x + c e_{πx}) = g_x conj(c) + c g_{πx}` when `π x ≠ x`. -/
lemma h_pair (x : X) (hx : P.π x ≠ x) (c : ℂ) :
    (datum P).h (DirectSum.lof ℂ X (fun _ => ℂ) x 1 + DirectSum.lof ℂ X (fun _ => ℂ) (P.π x) c)
      (DirectSum.lof ℂ X (fun _ => ℂ) x 1 + DirectSum.lof ℂ X (fun _ => ℂ) (P.π x) c) =
      P.g x * conj c + c * P.g (P.π x) := by
  classical
  set w := DirectSum.lof ℂ X (fun _ => ℂ) x 1 + DirectSum.lof ℂ X (fun _ => ℂ) (P.π x) c
  have hw : ∀ k, w k = (if x = k then 1 else 0) + (if P.π x = k then c else 0) := fun k => by
    simp only [w, DirectSum.add_apply, lof_eval]
  rw [h_eq_sum P w w (s := {x, P.π x}) (fun k hk => by
    rw [DFinsupp.mem_support_iff, hw] at hk
    by_cases h1 : x = k
    · exact h1 ▸ Finset.mem_insert_self _ _
    · by_cases h2 : P.π x = k
      · exact h2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · simp [h1, h2] at hk)]
  rw [Finset.sum_pair hx.symm]
  simp only [hw, hπ]
  simp [hx, hx.symm, mul_comm]

/-- `Sp_1 = λ` with multiplicities. -/
theorem rank_maxGenEigenspace_theta (σ : ℂ) :
    Module.rank ℂ ((theta P).maxGenEigenspace σ) = Cardinal.mk {x // P.lam x = σ} := by
  rw [theta, R7.rank_maxGenEigenspace_diag]
  simp_rw [TrivialModel.rank_maxGen_scalar]
  rw [← Cardinal.mk_congr (Equiv.sigmaPLiftEquivSubtype fun i => P.lam i = σ), Cardinal.mk_sigma]
  congr 1; ext i
  split_ifs with h <;> simp [h]

/-- The support of `Sp_1`: `spec Θ_1 = {λ_x}`. -/
theorem spec_theta : spec (theta P) = Set.range P.lam := by
  ext σ
  rw [theta, R7.spec_diag]
  simp only [OneBranch.spec_scalar, Set.mem_singleton_iff, Set.mem_range, eq_comm]

/-- The degree-one spectral-core condition for arbitrary block data: if every value of `λ` is
taken finitely often and `{λ_x}` has no finite accumulation point, `(V^1, Θ_1)` is a spectral
core. This is the hypothesis `def:trivial-model` and `prop:content` (iii) place on the divisor. -/
theorem spectralCore_theta (hfin : ∀ σ, {x | P.lam x = σ}.Finite)
    (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range P.lam))) :
    Spectral.SpectralCore (theta P) where
  iSup_eq_top := by
    rw [eq_top_iff]
    rintro x -
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      refine Submodule.mem_iSup_of_mem (P.lam i) ?_
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
    have hlt : Module.rank ℂ ((theta P).maxGenEigenspace σ) < Cardinal.aleph0 := by
      rw [rank_maxGenEigenspace_theta]
      have : Finite {x // P.lam x = σ} := (hfin σ).to_subtype
      exact Cardinal.lt_aleph0_of_finite _
    exact rank_lt_aleph0_iff.1 hlt
  noAccPt z := by rw [spec_theta]; exact hdisc z

end WeilRH.PairingModel

namespace WeilRH.ContentAssembly

open PairingModel

/-! ### The three kinds of block of `prop:content` (iii) -/

/-- The index set: two basis vectors per line unit (`ιL`), two per real-pair unit (`ιP`), four
per quartet unit (`ιQ`). -/
abbrev X (ιL ιP ιQ : Type) := (ιL × Bool) ⊕ (ιP × Bool) ⊕ (ιQ × Fin 4)

/-- `sgn(e) = 1`, `sgn(f) = -1` (`true = e`). -/
def bsgn (b : Bool) : ℂ := if b then 1 else -1

/-- `B` on the quartet block pairs `e₁ ↔ f₁` and `e₂ ↔ f₂` (`Ω` of `def:R2-block`). -/
def qswp : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- `Ω_{e₁f₁} = Ω_{e₂f₂} = 1`, `Ω_{f₁e₁} = Ω_{f₂e₂} = -1`. -/
def qsgn : Fin 4 → ℂ := ![1, 1, -1, -1]

/-- The star of the quartet block, `*v = S v̄` with `S = diag(R, R)`, `R = [[0, -1], [1, 0]]`. -/
def qtau : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The coefficients of `S`. -/
def qt : Fin 4 → ℂ := ![-1, 1, -1, 1]

/-- `Θ = diag(λ, λ̄, 1 - λ, 1 - λ̄)` on the quartet block. -/
noncomputable def qlam (l : ℂ) : Fin 4 → ℂ := ![l, conj l, 1 - l, 1 - conj l]

/-- The quartet block is the block of `def:R2-block`: `B(u, v) = uᵀΩv`. -/
theorem R2_Ω (i j : Fin 4) : R2.Ω i j = if j = qswp i then qsgn i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [R2.Ω, qswp, qsgn]

/-- The quartet block is the block of `def:R2-block`: the star is `v ↦ S v̄`. -/
theorem R2_S (i j : Fin 4) : R2.S i j = if j = qtau i then qt i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [R2.S, qtau, qt]

/-- The quartet block is the block of `def:R2-block`: `Θ = diag(λ, λ̄, 1 - λ, 1 - λ̄)` with
`λ = 1/2 + a + iT`. -/
theorem R2_Θ (a T : ℝ) : R2.Θ a T = Matrix.diagonal (qlam (R2.lam a T)) := by
  rw [R2.Θ_eq_diagonal]; rfl

variable {ιL ιP ιQ : Type}

/-- The pairing involution `σ`. -/
def swp : X ιL ιP ιQ → X ιL ιP ιQ
  | .inl (p, b) => .inl (p, !b)
  | .inr (.inl (p, b)) => .inr (.inl (p, !b))
  | .inr (.inr (q, k)) => .inr (.inr (q, qswp k))

/-- The signs of `B`. -/
def sgn : X ιL ιP ιQ → ℂ
  | .inl (_, b) => bsgn b
  | .inr (.inl (_, b)) => bsgn b
  | .inr (.inr (_, k)) => qsgn k

/-- The involution of the star: `swap` on the line (`*e = f`, `*f = -e`), the identity on a real
pair (`*(ae + bf) = -āe + b̄f`), `S` on a quartet. -/
def tau : X ιL ιP ιQ → X ιL ιP ιQ
  | .inl (p, b) => .inl (p, !b)
  | .inr (.inl (p, b)) => .inr (.inl (p, b))
  | .inr (.inr (q, k)) => .inr (.inr (q, qtau k))

/-- The coefficients of the star. -/
def t : X ιL ιP ιQ → ℂ
  | .inl (_, b) => -bsgn b
  | .inr (.inl (_, b)) => -bsgn b
  | .inr (.inr (_, k)) => qt k

/-- The divisor `Σ`: the line unit `p` contributes `ρL p, 1 - ρL p`, the real-pair unit `p`
contributes `ρP p, 1 - ρP p`, the quartet unit `q` contributes `λ, λ̄, 1 - λ, 1 - λ̄` with
`λ = lQ q`. The multiplicity of `σ` in `Σ` is `#{x // lamX x = σ}`. -/
noncomputable def lamX (ρL : ιL → ℂ) (ρP : ιP → ℝ) (lQ : ιQ → ℂ) : X ιL ιP ιQ → ℂ
  | .inl (p, b) => if b then ρL p else 1 - ρL p
  | .inr (.inl (p, b)) => if b then (ρP p : ℂ) else 1 - ρP p
  | .inr (.inr (q, k)) => qlam (lQ q) k

/-- The data of the direct sum of the blocks; the line points must lie on `Re s = 1/2`. -/
noncomputable def data (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ)
    (lQ : ιQ → ℂ) : Data (X ιL ιP ιQ) where
  swp := swp
  swp_swp := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩) <;> simp [swp]
    fin_cases k <;> rfl
  sgn := sgn
  sgn_ne := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩)
    · cases b <;> simp [sgn, bsgn]
    · cases b <;> simp [sgn, bsgn]
    · fin_cases k <;> simp [sgn, qsgn]
  lam := lamX ρL ρP lQ
  lam_add := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩)
    · cases b <;> simp [lamX, swp]
    · cases b <;> simp [lamX, swp]
    · fin_cases k <;> simp [lamX, swp, qswp, qlam]
  tau := tau
  tau_tau := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩) <;> simp [tau]
    fin_cases k <;> rfl
  t := t
  t_ne := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩)
    · cases b <;> simp [t, bsgn]
    · cases b <;> simp [t, bsgn]
    · fin_cases k <;> simp [t, qt]
  lam_tau := by
    rintro (⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩)
    · have h := hline p
      cases b <;> simp [lamX, tau, Complex.ext_iff, h] <;> norm_num
    · cases b <;> simp [lamX, tau, Complex.conj_ofReal]
    · fin_cases k <;> simp [lamX, tau, qtau, qlam]

/-- **`prop:content` (iii)**, the datum: the direct sum of the line block, the real-pair planes
and the quartet blocks of `def:R2-block`. -/
noncomputable def D (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ)
    (lQ : ιQ → ℂ) [DecidableEq ιL] [DecidableEq ιP] [DecidableEq ιQ] :
    WeightedStarDatum 1 0 1 (V (X ιL ιP ιQ)) (V (X ιL ιP ιQ)) ℂ :=
  datum (data ρL hline ρP lQ)

variable (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ) (lQ : ιQ → ℂ)

lemma π_π (x : X ιL ιP ιQ) : (data ρL hline ρP lQ).π ((data ρL hline ρP lQ).π x) = x := by
  rcases x with ⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩
  · simp [Data.π, data, swp, tau]
  · simp [Data.π, data, swp, tau]
  · fin_cases k <;> rfl

lemma conj_g (x : X ιL ιP ιQ) :
    conj ((data ρL hline ρP lQ).g x) = (data ρL hline ρP lQ).g ((data ρL hline ρP lQ).π x) := by
  rcases x with ⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩
  · cases b <;> simp [Data.g, Data.π, data, swp, tau, sgn, t, bsgn]
  · cases b <;> simp [Data.g, Data.π, data, swp, tau, sgn, t, bsgn]
  · fin_cases k <;> simp [Data.g, Data.π, data, swp, tau, sgn, t, qsgn, qt, qswp, qtau]

variable [DecidableEq ιL] [DecidableEq ιP] [DecidableEq ιQ]

/-- **`prop:content` (iii).** For a divisor `Σ` given by line points `ρL` (on `Re s = 1/2`), real
pairs `ρP` and quartets `lQ`, one family member per unit of multiplicity, the direct sum `D` of
the blocks is a Weil datum of type `(1, 0)` (AW1 for `U = 𝟙`, the AW3 trace and the star law of
AW4 are the fields of `D`) with

* `Sp_1 = Σ` with multiplicities,
* `h_1` Hermitian,
* `h_1` nondegenerate,
* `h_1` satisfying `(eq:inf-pol)` with weight one,
* `h_1` indefinite (`h_1(u, u) = 2`, `h_1(v, v) = -2`) as soon as there is a real pair or a
  quartet. -/
theorem content_indef :
    (∀ σ, Module.rank ℂ ((D ρL hline ρP lQ).ΘV.maxGenEigenspace σ) =
      Cardinal.mk {x // lamX ρL ρP lQ x = σ}) ∧
    (∀ u v, conj ((D ρL hline ρP lQ).h u v) = (D ρL hline ρP lQ).h v u) ∧
    (∀ u, u ≠ 0 → ∃ v, (D ρL hline ρP lQ).h u v ≠ 0) ∧
    (∀ u v, (D ρL hline ρP lQ).h ((D ρL hline ρP lQ).ΘV u) v +
      (D ρL hline ρP lQ).h u ((D ρL hline ρP lQ).ΘV v) = 1 * (D ρL hline ρP lQ).h u v) ∧
    (Nonempty ιP ∨ Nonempty ιQ →
      ∃ u v, (D ρL hline ρP lQ).h u u = 2 ∧ (D ρL hline ρP lQ).h v v = -2) := by
  set P := data ρL hline ρP lQ
  have hπ := π_π ρL hline ρP lQ
  refine ⟨fun σ => rank_maxGenEigenspace_theta P σ, h_conj_symm P hπ (conj_g ρL hline ρP lQ),
    fun u hu => h_nondegenerate P hπ hu, fun u v => by simpa using (D ρL hline ρP lQ).polarization_identity u v,
    ?_⟩
  rintro (⟨⟨p⟩⟩ | ⟨⟨q⟩⟩)
  · set x : X ιL ιP ιQ := .inr (.inl (p, true))
    have hx : P.π x ≠ x := by simp [x, P, Data.π, data, swp, tau]
    have h1 : P.g x = 1 := by simp [x, P, Data.g, data, swp, sgn, t, bsgn]
    have h2 : P.g (P.π x) = 1 := by simp [x, P, Data.g, Data.π, data, swp, tau, sgn, t, bsgn]
    refine ⟨_, _, (h_pair P hπ x hx 1).trans ?_, (h_pair P hπ x hx (-1)).trans ?_⟩ <;>
      rw [h1, h2] <;> norm_num
  · set x : X ιL ιP ιQ := .inr (.inr (q, 0))
    have hx : P.π x ≠ x := by simp [x, P, Data.π, data, swp, tau, qswp, qtau]
    have h1 : P.g x = -1 := by simp [x, P, Data.g, data, swp, sgn, t, qsgn, qt, qswp]
    have h2 : P.g (P.π x) = -1 := by
      simp [x, P, Data.g, Data.π, data, swp, tau, sgn, t, qsgn, qt, qswp, qtau]
    refine ⟨_, _, (h_pair P hπ x hx (-1)).trans ?_, (h_pair P hπ x hx 1).trans ?_⟩ <;>
      rw [h1, h2] <;> norm_num

end WeilRH.ContentAssembly
