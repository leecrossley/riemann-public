/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Duality
import WeilRH.Kronecker

/-!
# Hodge index on the arithmetic surface ⟺ AW4-E (Künneth report, Theorem 6; claim C-K6)

Source: `ai/2026-09-25-arithmetic-kunneth-conjecture/report.md`, §4 (K6) and §5, **Theorem 6**
(with Prop. 5 for the tensor-product form).

## The model (finite-dimensional, eigenspace level)

`SurfaceDatum V` is the degree-one data of Theorem 6 on a **finite-dimensional** complex space
`V = V¹` (the theorems that need it assume `[FiniteDimensional ℂ V]`):

* `Θ : End V` (the flow generator; its generalized eigenspaces `V_ρ := Θ.maxGenEigenspace ρ`);
* a bilinear pairing `B : V × V → ℂ` of weight one, `B(Θx, y) + B(x, Θy) = B(x, y)` (AW1–AW3 for
  `V¹ × V¹ → V² → ℂ(-1)`: `V_ρ` pairs with `V_{1-ρ}`), nondegenerate in the first variable
  (perfectness; only this half is used);
* an antilinear bijection `∗ : V → V` with `Θ∗ = ∗Θ` (so `∗V_ρ = V_{ρ̄}`) and
  `B(∗x, ∗y) = conj B(x, y)`;
* `h₁(x, y) := B(x, ∗y)` Hermitian. **Positivity is not assumed.**

It is the `(d, w, j) = (1, 0, 1)` instance of `WeilRH.WeightedStarDatum` with `W = V`, `T = ℂ`
(`toWeightedStarDatum`), so Q1 Lemma 4.2 (`derivation_law`) applies verbatim.

The Künneth form `h_S = h₁ ⊗ h₁` on the algebraic classes `N_S = ⊕_ρ V_ρ ⊗ V_{1-ρ}` is encoded
**block by block** through Gram matrices: `blockGram ρ` is the Kronecker product of the Gram
matrices of `h₁` on `V_ρ` and on `V_{1-ρ}` (in `Module.finBasis`), i.e. the Gram matrix of `h₁ ⊗ h₁`
on `V_ρ ⊗ V_{1-ρ}` in the product basis, and `HodgeIndex` says every block is positive definite.
Blockwise positivity is the report's clause (c): by (i) the blocks with `Re ρ ≠ ½` are
`h_S`-isotropic, and once all `Re ρ = ½` distinct blocks are `h_S`-orthogonal
(`h_eq_zero_of_mem_maxGenEigenspace`), so positivity on `N_S` is positivity on each block.

## Main results

* `h_eq_zero_of_mem_maxGenEigenspace`: `h₁(V_ρ, V_σ) = 0` unless `ρ + σ̄ = 1`.
* `h_eq_zero_of_re_ne_half` (**Theorem 6(i)**): `h₁ ≡ 0` on `V_ρ` when `Re ρ ≠ ½`
  (and `hS_block_eq_zero`: `h_S ≡ 0` on the block `V_ρ ⊗ V_{1-ρ}`).
* `hasEigenvalue_one_sub`: `ρ ∈ Spec Θ ⇒ 1 - ρ ∈ Spec Θ` (perfectness of `B`).
* `hodgeIndex_iff_pureDefinite` (**Theorem 6(iii), ⟺**): `h_S` positive definite on every block
  iff every eigenvalue has `Re ρ = ½` and `h₁` is definite (either sign) on each `V_ρ`.
* `hodgePure_iff_pureDefinite`: the same with positivity of `h_S` only on pure tensors `x ⊗ y`.
* `re_eq_half_of_hodgeIndex`, `isSemisimple_of_hodgeIndex` (**Theorem 6(iii), ⟹**): the Hodge
  index clause forces `Re ρ = ½` for every eigenvalue and `Θ` semisimple.
* `re_eq_half_of_definiteOn`, `isSemisimple_restrict_of_definiteOn`: the report's own route —
  on each `V_ρ`, `±h₁` is a `PosHermForm` satisfying (P) with weight one, and the existing C-PUR
  results (`PosHermForm.re_eq_half`, `PosHermForm.isSemisimple`) apply.

The matrix core (tensor positivity) is `WeilRH.posDef_kronecker_iff` in `WeilRH/Kronecker.lean`.
-/

open scoped ComplexConjugate Kronecker ComplexOrder
open Module Matrix Polynomial

namespace WeilRH

/-- The degree-one data of the Künneth report's Theorem 6 (AW1–AW3 on `X̄_K` plus the *algebraic*
part of AW4; positivity of `h₁` is **not** assumed). -/
structure SurfaceDatum (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The flow generator `Θ₁` on `V¹`. -/
  Θ : Module.End ℂ V
  /-- The duality pairing `B(x, y) = Tr(x ∪ y)` on `V¹ × V¹`. -/
  B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ
  /-- AW1 + AW3 (trace to `ℂ(-1)`): `B(Θx, y) + B(x, Θy) = B(x, y)`. -/
  B_weight : ∀ x y, B (Θ x) y + B x (Θ y) = B x y
  /-- Perfectness of `B` (first variable). -/
  B_nondeg : ∀ x, (∀ y, B x y = 0) → x = 0
  /-- The antilinear star `∗₁`. -/
  star : V →ₗ⋆[ℂ] V
  /-- `∗₁` is bijective. -/
  star_bijective : Function.Bijective star
  /-- `Θ∗₁ = ∗₁Θ` (hence `∗₁ V_ρ = V_{ρ̄}`). -/
  star_comm : ∀ x, Θ (star x) = star (Θ x)
  /-- `B(∗x, ∗y) = conj B(x, y)`. -/
  B_star : ∀ x y, B (star x) (star y) = conj (B x y)
  /-- `h₁(x, y) = B(x, ∗y)` is Hermitian. -/
  h_conj_symm : ∀ x y, conj (B x (star y)) = B y (star x)

namespace SurfaceDatum

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (D : SurfaceDatum V)

/-- `h₁(x, y) := B(x, ∗₁ y)` (linear in `x`, conjugate-linear in `y`). -/
def h (x y : V) : ℂ := D.B x (D.star y)

/-- The generalized eigenspace `V_ρ = V¹_{Θ∼ρ}`. -/
abbrev Vρ (ρ : ℂ) : Submodule ℂ V := D.Θ.maxGenEigenspace ρ

/-! ### Link with `WeightedStarDatum` (Q1 Lemma 4.2) -/

/-- A `SurfaceDatum` is a `WeightedStarDatum` of type `(1, 0)` in degree `1` with `W = V¹`,
`T = ℂ(-1)` (`Θ = 1`, i.e. the identity), `∪ = B`, `tr = id`. -/
def toWeightedStarDatum : WeightedStarDatum 1 0 1 V V ℂ where
  ΘV := D.Θ
  ΘW := D.Θ
  ΘT := LinearMap.id
  cup := D.B
  cup_derivation u v := by simp [D.B_weight]
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := D.star
  star_comm v := by simp [D.star_comm]

@[simp] lemma toWeightedStarDatum_h (u v : V) : D.toWeightedStarDatum.h u v = D.h u v := rfl

@[simp] lemma toWeightedStarDatum_ΘV : D.toWeightedStarDatum.ΘV = D.Θ := rfl

/-- **Q1 Lemma 4.2 for the surface datum**: `h₁(Θu, v) + h₁(u, Θv) = h₁(u, v)`. -/
theorem derivation_law (u v : V) : D.h (D.Θ u) v + D.h u (D.Θ v) = D.h u v := by
  simpa using D.toWeightedStarDatum.derivation_law u v

/-! ### Sesquilinearity -/

lemma h_add_left (u u' v : V) : D.h (u + u') v = D.h u v + D.h u' v := by simp [h]
lemma h_add_right (u v v' : V) : D.h u (v + v') = D.h u v + D.h u v' := by simp [h]
lemma h_sub_left (u u' v : V) : D.h (u - u') v = D.h u v - D.h u' v := by simp [h]
lemma h_sub_right (u v v' : V) : D.h u (v - v') = D.h u v - D.h u v' := by simp [h]
lemma h_smul_left (c : ℂ) (u v : V) : D.h (c • u) v = c * D.h u v := by simp [h]
lemma h_smul_right (c : ℂ) (u v : V) : D.h u (c • v) = conj c * D.h u v := by simp [h]
@[simp] lemma h_zero_left (v : V) : D.h 0 v = 0 := by simp [h]
@[simp] lemma h_zero_right (u : V) : D.h u 0 = 0 := by simp [h]

lemma h_conj (u v : V) : conj (D.h u v) = D.h v u := D.h_conj_symm u v

lemma h_self_im (x : V) : (D.h x x).im = 0 := by
  have := congrArg Complex.im (D.h_conj x x)
  simp only [Complex.conj_im] at this
  linarith

/-- `h₁(∗x, ∗y) = h₁(y, x)`. -/
lemma h_star_star (x y : V) : D.h (D.star x) (D.star y) = D.h y x := by
  simp only [h]
  rw [D.B_star, D.h_conj_symm]

lemma star_eq_zero_iff {x : V} : D.star x = 0 ↔ x = 0 :=
  ⟨fun hx => D.star_bijective.1 (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩

/-! ### Theorem 6 (i): isotropy off the critical line -/

/-- Generalized eigenvectors for `ρ`, `σ` with `ρ + σ̄ ≠ 1` are `h₁`-orthogonal
(induction on the lengths of the Jordan chains, using only the derivation law). -/
theorem h_eq_zero_of_pow {ρ σ : ℂ} (hρσ : ρ + conj σ ≠ 1) :
    ∀ (k l : ℕ) (x y : V), ((D.Θ - ρ • 1) ^ k) x = 0 → ((D.Θ - σ • 1) ^ l) y = 0 →
      D.h x y = 0 := by
  intro k
  induction k with
  | zero => intro l x y hx _; simp only [pow_zero, Module.End.one_apply] at hx; simp [hx]
  | succ k ihk =>
    intro l
    induction l with
    | zero => intro x y _ hy; simp only [pow_zero, Module.End.one_apply] at hy; simp [hy]
    | succ l ihl =>
      intro x y hx hy
      rw [pow_succ, Module.End.mul_apply] at hx hy
      have h1 := ihk (l + 1) _ y hx (by rw [pow_succ, Module.End.mul_apply]; exact hy)
      have h2 := ihl x _ (by rw [pow_succ, Module.End.mul_apply]; exact hx) hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, D.h_sub_left,
        D.h_sub_right, D.h_smul_left, D.h_smul_right] at h1 h2
      have key := D.derivation_law x y
      have : (1 - ρ - conj σ) * D.h x y = 0 := by linear_combination h1 + h2 - key
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linear_combination -h) hρσ
      · exact h

/-- `h₁(V_ρ, V_σ) = 0` unless `ρ + σ̄ = 1`. In particular, once every eigenvalue lies on
`Re = ½` (so `1 - ρ̄ = ρ`), distinct generalized eigenspaces are `h₁`-orthogonal. -/
theorem h_eq_zero_of_mem_maxGenEigenspace {ρ σ : ℂ} (hρσ : ρ + conj σ ≠ 1) {x y : V}
    (hx : x ∈ D.Vρ ρ) (hy : y ∈ D.Vρ σ) : D.h x y = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
  obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hy
  exact D.h_eq_zero_of_pow hρσ k l x y hk hl

lemma add_conj_ne_one {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) : ρ + conj ρ ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.conj_re, Complex.one_re] at this
  exact hρ (by linarith)

/-- **Künneth Theorem 6 (i).** If `Re ρ ≠ ½`, `h₁` vanishes identically on `V_ρ`. -/
theorem h_eq_zero_of_re_ne_half {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) {x y : V}
    (hx : x ∈ D.Vρ ρ) (hy : y ∈ D.Vρ ρ) : D.h x y = 0 :=
  D.h_eq_zero_of_mem_maxGenEigenspace (add_conj_ne_one hρ) hx hy

/-- **Künneth Theorem 6 (i), surface form.** If `Re ρ ≠ ½`, the Künneth form
`h_S(x ⊗ y, x' ⊗ y') = h₁(x, x') h₁(y, y')` vanishes on the block `V_ρ ⊗ V_{1-ρ}`. -/
theorem hS_block_eq_zero {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) {x x' y y' : V}
    (hx : x ∈ D.Vρ ρ) (hx' : x' ∈ D.Vρ ρ) (_hy : y ∈ D.Vρ (1 - ρ)) (_hy' : y' ∈ D.Vρ (1 - ρ)) :
    D.h x x' * D.h y y' = 0 := by
  rw [D.h_eq_zero_of_re_ne_half hρ hx hx', zero_mul]

/-! ### The star and the spectrum -/

lemma star_sub_pow (ρ : ℂ) (k : ℕ) (x : V) :
    ((D.Θ - conj ρ • 1) ^ k) (D.star x) = D.star (((D.Θ - ρ • 1) ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
    congr 1
    simp [D.star_comm]

/-- `∗₁` maps `V_ρ` onto `V_{ρ̄}`. -/
lemma star_mem_iff {ρ : ℂ} {x : V} : D.star x ∈ D.Vρ (conj ρ) ↔ x ∈ D.Vρ ρ := by
  simp only [Module.End.mem_maxGenEigenspace, star_sub_pow, star_eq_zero_iff]

lemma exists_star_eq_of_mem {ρ : ℂ} {y : V} (hy : y ∈ D.Vρ (conj ρ)) :
    ∃ x ∈ D.Vρ ρ, D.star x = y := by
  obtain ⟨x, rfl⟩ := D.star_bijective.2 y
  exact ⟨x, D.star_mem_iff.1 hy, rfl⟩

/-- Spectral symmetry `ρ ↦ 1 - ρ`, from perfectness of the weight-one pairing `B`. -/
theorem hasEigenvalue_one_sub [FiniteDimensional ℂ V] {ρ : ℂ} (hρ : D.Θ.HasEigenvalue ρ) :
    D.Θ.HasEigenvalue (1 - ρ) := by
  obtain ⟨x, hx⟩ := hρ.exists_hasEigenvector
  have hΘx : D.Θ x = ρ • x := hx.apply_eq_smul
  by_contra hne
  have hker : LinearMap.ker (D.Θ - (1 - ρ) • 1) = ⊥ := by
    rw [← Module.End.eigenspace_def]
    simpa [Module.End.hasEigenvalue_iff] using hne
  have hsurj : LinearMap.range (D.Θ - (1 - ρ) • 1) = ⊤ :=
    (LinearMap.isUnit_iff_range_eq_top _).1 ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)
  apply hx.2
  apply D.B_nondeg x
  intro z
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1 hsurj z
  rw [← hy]
  have key := D.B_weight x y
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
    map_smul, smul_eq_mul, hΘx, LinearMap.smul_apply] at key ⊢
  linear_combination key

lemma hasEigenvalue_of_mem {ρ : ℂ} {x : V} (hx : x ∈ D.Vρ ρ) (hx0 : x ≠ 0) :
    D.Θ.HasEigenvalue ρ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k)
    ((Submodule.ne_bot_iff _).2 ⟨x, Module.End.mem_genEigenspace_nat.2 hk, hx0⟩)

/-! ### Definiteness, the Hodge index clause and AW4-E -/

/-- `h₁` is definite (positive or negative) on the submodule `p`. -/
def DefiniteOn (p : Submodule ℂ V) : Prop :=
  (∀ x ∈ p, x ≠ 0 → 0 < (D.h x x).re) ∨ (∀ x ∈ p, x ≠ 0 → (D.h x x).re < 0)

/-- The right-hand side of Theorem 6(iii): every eigenvalue lies on `Re = ½` and `h₁` is
definite on each generalized eigenspace. -/
def PureDefinite : Prop :=
  ∀ ρ : ℂ, D.Θ.HasEigenvalue ρ → ρ.re = 1 / 2 ∧ D.DefiniteOn (D.Vρ ρ)

/-- The Hodge index clause tested on pure tensors: `h_S(x ⊗ y, x ⊗ y) = h₁(x, x) h₁(y, y) > 0`
for nonzero `x ∈ V_ρ`, `y ∈ V_{1-ρ}`. (A consequence of `HodgeIndex`, and equivalent to it.) -/
def HodgePure : Prop :=
  ∀ (ρ : ℂ) (x y : V), x ∈ D.Vρ ρ → y ∈ D.Vρ (1 - ρ) → x ≠ 0 → y ≠ 0 →
    0 < (D.h x x).re * (D.h y y).re

lemma re_mul_self (x y : V) : (D.h x x * D.h y y).re = (D.h x x).re * (D.h y y).re := by
  simp [Complex.mul_re, D.h_self_im]

/-- A sign-splitting lemma: if `f a · g b > 0` for all `a, b` (both types inhabited) then `f`, `g`
are both positive or both negative. -/
lemma sign_split {α β : Type*} (f : α → ℝ) (g : β → ℝ) (a₀ : α) (b₀ : β)
    (h : ∀ a b, 0 < f a * g b) :
    ((∀ a, 0 < f a) ∧ ∀ b, 0 < g b) ∨ ((∀ a, f a < 0) ∧ ∀ b, g b < 0) := by
  by_cases hb : 0 < g b₀
  · have hf : ∀ a, 0 < f a := fun a => pos_of_mul_pos_left (h a b₀) hb.le
    exact Or.inl ⟨hf, fun b => pos_of_mul_pos_right (h a₀ b) (hf a₀).le⟩
  · have hb' : g b₀ < 0 := by
      rcases (not_lt.1 hb).lt_or_eq with hb | hb
      · exact hb
      · have := h a₀ b₀; rw [hb, mul_zero] at this; exact absurd this (lt_irrefl 0)
    have hf : ∀ a, f a < 0 := fun a => by have := h a b₀; nlinarith
    exact Or.inr ⟨hf, fun b => by have := h a₀ b; have := hf a₀; nlinarith⟩

/-- Under `HodgePure`, every eigenvalue has `Re ρ = ½`: an eigenvector of `ρ` is `h₁`-isotropic
otherwise (Theorem 6(i)) and `V_{1-ρ} ≠ 0` (spectral symmetry). -/
theorem re_eq_half_of_hodgePure [FiniteDimensional ℂ V] (hH : D.HodgePure) {ρ : ℂ}
    (hρ : D.Θ.HasEigenvalue ρ) : ρ.re = 1 / 2 := by
  obtain ⟨x, hx⟩ := hρ.exists_hasEigenvector
  obtain ⟨y, hy⟩ := (D.hasEigenvalue_one_sub hρ).exists_hasEigenvector
  have hxV : x ∈ D.Vρ ρ := Module.End.eigenspace_le_maxGenEigenspace hx.1
  have hyV : y ∈ D.Vρ (1 - ρ) := Module.End.eigenspace_le_maxGenEigenspace hy.1
  by_contra hne
  have := hH ρ x y hxV hyV hx.2 hy.2
  rw [D.h_eq_zero_of_re_ne_half hne hxV hxV] at this
  simp at this

theorem definiteOn_of_hodgePure [FiniteDimensional ℂ V] (hH : D.HodgePure) {ρ : ℂ}
    (hρ : D.Θ.HasEigenvalue ρ) : D.DefiniteOn (D.Vρ ρ) := by
  obtain ⟨x₀, hx₀⟩ := hρ.exists_hasEigenvector
  obtain ⟨y₀, hy₀⟩ := (D.hasEigenvalue_one_sub hρ).exists_hasEigenvector
  let α := {x : V // x ∈ D.Vρ ρ ∧ x ≠ 0}
  let β := {y : V // y ∈ D.Vρ (1 - ρ) ∧ y ≠ 0}
  have := sign_split (fun a : α => (D.h a.1 a.1).re) (fun b : β => (D.h b.1 b.1).re)
    ⟨x₀, Module.End.eigenspace_le_maxGenEigenspace hx₀.1, hx₀.2⟩
    ⟨y₀, Module.End.eigenspace_le_maxGenEigenspace hy₀.1, hy₀.2⟩
    (fun a b => hH ρ a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2)
  rcases this with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl fun x hx hx0 => h1 ⟨x, hx, hx0⟩
  · exact Or.inr fun x hx hx0 => h1 ⟨x, hx, hx0⟩

theorem pureDefinite_of_hodgePure [FiniteDimensional ℂ V] (hH : D.HodgePure) : D.PureDefinite :=
  fun _ hρ => ⟨D.re_eq_half_of_hodgePure hH hρ, D.definiteOn_of_hodgePure hH hρ⟩

lemma one_sub_eq_conj {ρ : ℂ} (hρ : ρ.re = 1 / 2) : 1 - ρ = conj ρ := by
  apply Complex.ext <;> (simp [hρ]; try norm_num)

theorem hodgePure_of_pureDefinite (hP : D.PureDefinite) : D.HodgePure := by
  intro ρ x y hx hy hx0 hy0
  obtain ⟨hre, hdef⟩ := hP ρ (D.hasEigenvalue_of_mem hx hx0)
  rw [one_sub_eq_conj hre] at hy
  obtain ⟨x', hx', rfl⟩ := D.exists_star_eq_of_mem hy
  have hx'0 : x' ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  rw [D.h_star_star]
  rcases hdef with h | h
  · exact mul_pos (h x hx hx0) (h x' hx' hx'0)
  · exact mul_pos_of_neg_of_neg (h x hx hx0) (h x' hx' hx'0)

/-- Pure-tensor positivity of `h_S` is equivalent to AW4-E on `V¹` (Theorem 6(iii)). -/
theorem hodgePure_iff_pureDefinite [FiniteDimensional ℂ V] : D.HodgePure ↔ D.PureDefinite :=
  ⟨D.pureDefinite_of_hodgePure, D.hodgePure_of_pureDefinite⟩

/-! ### Semisimplicity -/

/-- Under AW4-E, `Θ` has no Jordan blocks: `V_ρ = ker (Θ - ρ)`. -/
theorem maxGenEigenspace_eq_eigenspace (hP : D.PureDefinite) (ρ : ℂ) :
    D.Vρ ρ = D.Θ.eigenspace ρ := by
  refine le_antisymm ?_ Module.End.eigenspace_le_maxGenEigenspace
  intro x hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
  -- `N² z = 0 ⇒ N z = 0`, where `N = Θ - ρ`.
  have sq : ∀ z : V, (D.Θ - ρ • 1) ((D.Θ - ρ • 1) z) = 0 → (D.Θ - ρ • 1) z = 0 := by
    intro z hz
    by_contra hne
    set y := (D.Θ - ρ • 1) z with hy_def
    have hyE : y ∈ D.Θ.eigenspace ρ := by
      rw [Module.End.eigenspace_def, LinearMap.mem_ker]; exact hz
    have hΘy : D.Θ y = ρ • y := Module.End.mem_eigenspace_iff.1 hyE
    have hρ : D.Θ.HasEigenvalue ρ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hyE, hne⟩
    obtain ⟨hre, hdef⟩ := hP ρ hρ
    have hyy : D.h y y = 0 := by
      have key := D.derivation_law z y
      have e1 : D.h y y = D.h (D.Θ z) y - ρ * D.h z y := by
        rw [hy_def]
        simp [D.h_sub_left, D.h_smul_left]
      rw [hΘy, D.h_smul_right] at key
      have hc : ρ + conj ρ = 1 := by
        apply Complex.ext <;> (simp [hre]; try norm_num)
      rw [e1]
      linear_combination key - D.h z y * hc
    have hyV : y ∈ D.Vρ ρ := Module.End.eigenspace_le_maxGenEigenspace hyE
    rcases hdef with h | h
    · have := h y hyV hne; rw [hyy] at this; simp at this
    · have := h y hyV hne; rw [hyy] at this; simp at this
  have : ∀ n : ℕ, ∀ z : V, ((D.Θ - ρ • 1) ^ n) z = 0 → (D.Θ - ρ • 1) z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; simp only [pow_zero, Module.End.one_apply] at hz; simp [hz]
    | succ n ih =>
      intro z hz
      rw [pow_succ, Module.End.mul_apply] at hz
      exact sq z (ih _ hz)
  rw [Module.End.mem_eigenspace_iff]
  have := this k x hk
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
  exact sub_eq_zero.1 this

/-- Over `ℂ` in finite dimension, if every generalized eigenspace is an eigenspace then the
endomorphism is semisimple (it is annihilated by the squarefree `∏_{ρ ∈ Spec} (X - ρ)`). -/
theorem _root_.WeilRH.isSemisimple_of_maxGenEigenspace_eq_eigenspace [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : ∀ ρ, f.maxGenEigenspace ρ = f.eigenspace ρ) : f.IsSemisimple := by
  classical
  let s := (minpoly ℂ f).roots.toFinset
  let p : ℂ[X] := ∏ μ ∈ s, (X - C μ)
  have hsq : Squarefree p :=
    (Polynomial.separable_prod_X_sub_C_iff'.2 (Set.injOn_id _)).squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
  have htop : ⨆ μ, f.eigenspace μ = ⊤ := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    simp only [hf]
  ext v
  have hv : v ∈ ⨆ μ, f.eigenspace μ := by rw [htop]; trivial
  rw [LinearMap.zero_apply]
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
    by_cases hv0 : v = 0
    · simp [hv0]
    have hμ : f.HasEigenvalue μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩
    have hμs : μ ∈ s := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (minpoly.ne_zero
        (Algebra.IsIntegral.isIntegral f))]
      exact Module.End.hasEigenvalue_iff_isRoot.1 hμ
    change aeval f (∏ μ ∈ s, (X - C μ)) v = 0
    rw [← Finset.prod_erase_mul _ _ hμs, map_mul, Module.End.mul_apply]
    have : (aeval f (X - C μ)) v = 0 := by
      simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
      rw [Module.End.mem_eigenspace_iff.1 hv, sub_self]
    rw [this, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]

/-- **Theorem 6(iii), semisimplicity.** Under AW4-E, `Θ₁` is semisimple. -/
theorem isSemisimple_of_pureDefinite [FiniteDimensional ℂ V] (hP : D.PureDefinite) :
    D.Θ.IsSemisimple :=
  isSemisimple_of_maxGenEigenspace_eq_eigenspace D.Θ (D.maxGenEigenspace_eq_eigenspace hP)

/-! ### Gram matrices and the Hodge index clause on `N_S` -/

/-- The Gram matrix of `h₁` in a basis `b` of a submodule `p`, in the convention of
`Matrix.PosDef`: `G i j = h₁(b j, b i)`, so that `vᴴ G v = h₁(Σ vⱼ bⱼ, Σ vᵢ bᵢ)`. -/
noncomputable def gram {p : Submodule ℂ V} {ι : Type*} (b : Basis ι ℂ p) : Matrix ι ι ℂ :=
  fun i j => D.h (b j) (b i)

lemma gram_isHermitian {p : Submodule ℂ V} {ι : Type*} (b : Basis ι ℂ p) :
    (D.gram b).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, gram, RCLike.star_def]
  exact D.h_conj _ _

lemma h_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    D.h (∑ i ∈ s, f i) w = ∑ i ∈ s, D.h (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, D.h_add_left, ih]

lemma h_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    D.h w (∑ i ∈ s, f i) = ∑ i ∈ s, D.h w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, D.h_add_right, ih]

lemma h_sum_sum {ι : Type*} [Fintype ι] (v : ι → ℂ) (e : ι → V) :
    D.h (∑ j, v j • e j) (∑ i, v i • e i) = ∑ i, ∑ j, conj (v i) * D.h (e j) (e i) * v j := by
  simp only [D.h_sum_left, D.h_smul_left, D.h_sum_right, D.h_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Fintype.sum_congr _ _ fun _ => Fintype.sum_congr _ _ fun _ => by ring

lemma gram_quad {p : Submodule ℂ V} {ι : Type*} [Fintype ι] (b : Basis ι ℂ p) (v : ι → ℂ) :
    Star.star v ⬝ᵥ (D.gram b *ᵥ v) =
      D.h ((b.equivFun.symm v : p) : V) ((b.equivFun.symm v : p) : V) := by
  rw [Basis.equivFun_symm_apply, Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  rw [D.h_sum_sum]
  simp only [dotProduct, mulVec, gram, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  exact Fintype.sum_congr _ _ fun _ => Fintype.sum_congr _ _ fun _ => by ring

lemma forall_basis_iff {p : Submodule ℂ V} {ι : Type*} [Fintype ι] (b : Basis ι ℂ p)
    (P : V → Prop) :
    (∀ v : ι → ℂ, v ≠ 0 → P ((b.equivFun.symm v : p) : V)) ↔ ∀ x ∈ p, x ≠ 0 → P x := by
  constructor
  · intro h x hx hx0
    have hne : b.equivFun ⟨x, hx⟩ ≠ 0 := by
      intro h0
      apply hx0
      have := congrArg Subtype.val (b.equivFun.injective (h0.trans (map_zero _).symm))
      simpa using this
    simpa using h _ hne
  · intro h v hv
    refine h _ (b.equivFun.symm v).2 ?_
    intro h0
    apply hv
    have : b.equivFun.symm v = 0 := Subtype.ext (by simpa using h0)
    have := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this

lemma gram_posDef_iff {p : Submodule ℂ V} {ι : Type*} [Fintype ι] (b : Basis ι ℂ p) :
    (D.gram b).PosDef ↔ ∀ x ∈ p, x ≠ 0 → 0 < (D.h x x).re := by
  rw [posDef_iff_re (D.gram_isHermitian b), ← forall_basis_iff b (fun x => 0 < (D.h x x).re)]
  simp only [D.gram_quad]

lemma neg_gram_posDef_iff {p : Submodule ℂ V} {ι : Type*} [Fintype ι] (b : Basis ι ℂ p) :
    (-D.gram b).PosDef ↔ ∀ x ∈ p, x ≠ 0 → (D.h x x).re < 0 := by
  rw [neg_posDef_iff_re (D.gram_isHermitian b), ← forall_basis_iff b (fun x => (D.h x x).re < 0)]
  simp only [D.gram_quad]

variable [FiniteDimensional ℂ V]

/-- The Gram matrix of the Künneth form `h_S = h₁ ⊗ h₁` on the block `V_ρ ⊗ V_{1-ρ}` of
`N_S = ⊕_ρ V_ρ ⊗ V_{1-ρ}`, in the product of the bases `Module.finBasis`: the Kronecker product
of the Gram matrices of `h₁` on `V_ρ` and on `V_{1-ρ}` (Prop. 5). -/
noncomputable def blockGram (ρ : ℂ) :
    Matrix (Fin (finrank ℂ (D.Vρ ρ)) × Fin (finrank ℂ (D.Vρ (1 - ρ))))
      (Fin (finrank ℂ (D.Vρ ρ)) × Fin (finrank ℂ (D.Vρ (1 - ρ)))) ℂ :=
  D.gram (Module.finBasis ℂ (D.Vρ ρ)) ⊗ₖ D.gram (Module.finBasis ℂ (D.Vρ (1 - ρ)))

/-- **The Hodge index clause (K6)(c) / AW4-E on the surface**: the Künneth form `h_S = h₁ ⊗ h₁`
is positive definite on every block `V_ρ ⊗ V_{1-ρ}` of `N_S`. -/
def HodgeIndex : Prop := ∀ ρ : ℂ, (D.blockGram ρ).PosDef

lemma nonempty_fin_of_mem {p : Submodule ℂ V} {x : V} (hx : x ∈ p) (hx0 : x ≠ 0) :
    Nonempty (Fin (finrank ℂ p)) :=
  ⟨⟨0, Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩⟩⟩

lemma posDef_of_isEmpty {n : Type*} [Fintype n] [IsEmpty n] (M : Matrix n n ℂ) : M.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨by ext i; exact isEmptyElim i, fun x hx => absurd (_root_.funext isEmptyElim) hx⟩

theorem hodgePure_of_hodgeIndex (hH : D.HodgeIndex) : D.HodgePure := by
  intro ρ x y hx hy hx0 hy0
  have := nonempty_fin_of_mem hx hx0
  have := nonempty_fin_of_mem hy hy0
  have hK := (posDef_kronecker_iff (D.gram_isHermitian _) (D.gram_isHermitian _)).1 (hH ρ)
  rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos ((D.gram_posDef_iff _).1 h1 x hx hx0) ((D.gram_posDef_iff _).1 h2 y hy hy0)
  · exact mul_pos_of_neg_of_neg ((D.neg_gram_posDef_iff _).1 h1 x hx hx0)
      ((D.neg_gram_posDef_iff _).1 h2 y hy hy0)

theorem hodgeIndex_of_hodgePure (hH : D.HodgePure) : D.HodgeIndex := by
  intro ρ
  by_cases hx : ∃ x ∈ D.Vρ ρ, x ≠ 0
  · by_cases hy : ∃ y ∈ D.Vρ (1 - ρ), y ≠ 0
    · obtain ⟨x₀, hx₀, hx₀0⟩ := hx
      obtain ⟨y₀, hy₀, hy₀0⟩ := hy
      have := nonempty_fin_of_mem hx₀ hx₀0
      have := nonempty_fin_of_mem hy₀ hy₀0
      rw [blockGram, posDef_kronecker_iff (D.gram_isHermitian _) (D.gram_isHermitian _),
        D.gram_posDef_iff, D.gram_posDef_iff, D.neg_gram_posDef_iff, D.neg_gram_posDef_iff]
      have := sign_split
        (fun a : {x : V // x ∈ D.Vρ ρ ∧ x ≠ 0} => (D.h a.1 a.1).re)
        (fun b : {y : V // y ∈ D.Vρ (1 - ρ) ∧ y ≠ 0} => (D.h b.1 b.1).re)
        ⟨x₀, hx₀, hx₀0⟩ ⟨y₀, hy₀, hy₀0⟩ (fun a b => hH ρ a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2)
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun x hx hx0 => h1 ⟨x, hx, hx0⟩, fun y hy hy0 => h2 ⟨y, hy, hy0⟩⟩
      · exact Or.inr ⟨fun x hx hx0 => h1 ⟨x, hx, hx0⟩, fun y hy hy0 => h2 ⟨y, hy, hy0⟩⟩
    · push Not at hy
      have : finrank ℂ (D.Vρ (1 - ρ)) = 0 := by
        rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]; exact hy
      have : IsEmpty (Fin (finrank ℂ (D.Vρ ρ)) × Fin (finrank ℂ (D.Vρ (1 - ρ)))) := by
        rw [this]; infer_instance
      exact posDef_of_isEmpty _
  · push Not at hx
    have : finrank ℂ (D.Vρ ρ) = 0 := by
      rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]; exact hx
    have : IsEmpty (Fin (finrank ℂ (D.Vρ ρ)) × Fin (finrank ℂ (D.Vρ (1 - ρ)))) := by
      rw [this]; infer_instance
    exact posDef_of_isEmpty _

/-- `HodgeIndex` (positivity of `h_S` on each block) is equivalent to its pure-tensor form. -/
theorem hodgeIndex_iff_hodgePure : D.HodgeIndex ↔ D.HodgePure :=
  ⟨D.hodgePure_of_hodgeIndex, D.hodgeIndex_of_hodgePure⟩

/-- **Künneth Theorem 6 (iii), ⟺ (C-K6).** The Hodge index clause — `h_S = h₁ ⊗ h₁` positive
definite on `N_S = ⊕_ρ V_ρ ⊗ V_{1-ρ}` (blockwise) — holds iff every eigenvalue of `Θ₁` has
`Re ρ = ½` and `h₁` is definite (of either sign) on each `V_ρ` (AW4-E). -/
theorem hodgeIndex_iff_pureDefinite : D.HodgeIndex ↔ D.PureDefinite :=
  D.hodgeIndex_iff_hodgePure.trans D.hodgePure_iff_pureDefinite

/-- **Künneth Theorem 6 (iii), RH direction.** The Hodge index clause forces `Re ρ = ½` for every
eigenvalue `ρ` of `Θ₁`. -/
theorem re_eq_half_of_hodgeIndex (hH : D.HodgeIndex) {ρ : ℂ} (hρ : D.Θ.HasEigenvalue ρ) :
    ρ.re = 1 / 2 :=
  D.re_eq_half_of_hodgePure (D.hodgePure_of_hodgeIndex hH) hρ

/-- **Künneth Theorem 6 (iii), semisimplicity.** The Hodge index clause forces `Θ₁` semisimple. -/
theorem isSemisimple_of_hodgeIndex (hH : D.HodgeIndex) : D.Θ.IsSemisimple :=
  D.isSemisimple_of_pureDefinite (D.hodgeIndex_iff_pureDefinite.1 hH)

/-! ### Link with the C-PUR machinery (`PosHermForm`, `WeightedStarDatum`) -/

omit [FiniteDimensional ℂ V] in
/-- On a submodule where `ε h₁` is positive (`ε = ±1`), `ε h₁` is a `PosHermForm`. -/
def blockForm (ε : ℝ) (p : Submodule ℂ V) (hp : ∀ x ∈ p, x ≠ 0 → 0 < ε * (D.h x x).re) :
    PosHermForm p where
  toFun u v := (ε : ℂ) * D.h u v
  add_left u u' v := by simp [D.h_add_left, mul_add]
  smul_left c u v := by simp [D.h_smul_left]; ring
  conj_symm u v := by simp [D.h_conj]
  re_pos u hu := by
    simpa [Complex.mul_re] using hp u u.2 (by simpa using hu)

omit [FiniteDimensional ℂ V] in
lemma mapsTo_Vρ (ρ : ℂ) : Set.MapsTo D.Θ (D.Vρ ρ) (D.Vρ ρ) :=
  Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl D.Θ) ρ

omit [FiniteDimensional ℂ V] in
lemma blockForm_P (ε : ℝ) (ρ : ℂ) (hp : ∀ x ∈ D.Vρ ρ, x ≠ 0 → 0 < ε * (D.h x x).re)
    (u v : D.Vρ ρ) :
    (D.blockForm ε _ hp).toFun (D.Θ.restrict (D.mapsTo_Vρ ρ) u) v +
      (D.blockForm ε _ hp).toFun u (D.Θ.restrict (D.mapsTo_Vρ ρ) v) =
      ((1 : ℝ) : ℂ) * (D.blockForm ε _ hp).toFun u v := by
  have e : ∀ w : D.Vρ ρ, ((D.Θ.restrict (D.mapsTo_Vρ ρ) w : D.Vρ ρ) : V) = D.Θ w := fun _ => rfl
  simp only [blockForm, e, Complex.ofReal_one, one_mul]
  rw [← mul_add, D.derivation_law]

omit [FiniteDimensional ℂ V] in
lemma exists_eps {p : Submodule ℂ V} (hdef : D.DefiniteOn p) :
    ∃ ε : ℝ, ∀ x ∈ p, x ≠ 0 → 0 < ε * (D.h x x).re := by
  rcases hdef with h | h
  · exact ⟨1, fun x hx hx0 => by simpa using h x hx hx0⟩
  · exact ⟨-1, fun x hx hx0 => by have := h x hx hx0; linarith⟩

omit [FiniteDimensional ℂ V] in
/-- **The report's route to purity (via C-PUR).** If `h₁` is definite on `V_ρ` and `ρ` is an
eigenvalue, then `±h₁|V_ρ` is a `PosHermForm` satisfying (P) of weight one (Q1 Lemma 4.2), so
`PosHermForm.re_eq_half` gives `Re ρ = ½`. -/
theorem re_eq_half_of_definiteOn {ρ : ℂ} (hρ : D.Θ.HasEigenvalue ρ)
    (hdef : D.DefiniteOn (D.Vρ ρ)) : ρ.re = 1 / 2 := by
  obtain ⟨ε, hε⟩ := D.exists_eps hdef
  obtain ⟨x, hx⟩ := hρ.exists_hasEigenvector
  have hxV : x ∈ D.Vρ ρ := Module.End.eigenspace_le_maxGenEigenspace hx.1
  have hρ' : Module.End.HasEigenvalue (D.Θ.restrict (D.mapsTo_Vρ ρ)) ρ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxV⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx.1)
    · simpa using hx.2
  simpa using (D.blockForm ε _ hε).re_eq_half _ 1 (D.blockForm_P ε ρ hε) hρ'

/-- **Semisimplicity on each block via C-PUR.** If `h₁` is definite on `V_ρ`, then `Θ₁|V_ρ` is
semisimple (`PosHermForm.isSemisimple`). -/
theorem isSemisimple_restrict_of_definiteOn {ρ : ℂ} (hdef : D.DefiniteOn (D.Vρ ρ)) :
    Module.End.IsSemisimple (D.Θ.restrict (D.mapsTo_Vρ ρ)) := by
  obtain ⟨ε, hε⟩ := D.exists_eps hdef
  exact (D.blockForm ε _ hε).isSemisimple _ 1 (D.blockForm_P ε ρ hε)

/-- **Corollary (link to `WeightedStarDatum`).** Under the Hodge index clause, the degree-one
datum `D.toWeightedStarDatum` of type `(1, 0)` has the conclusion of
`WeightedStarDatum.re_eq_half_of_curve`: every eigenvalue of `Θ_1` has `Re ρ = ½`, obtained here
through `re_eq_half_of_definiteOn` (C-PUR on each block) rather than from global positivity. -/
theorem toWeightedStarDatum_re_eq_half (hH : D.HodgeIndex) {ρ : ℂ}
    (hρ : D.toWeightedStarDatum.ΘV.HasEigenvalue ρ) : ρ.re = 1 / 2 :=
  D.re_eq_half_of_definiteOn hρ ((D.hodgeIndex_iff_pureDefinite.1 hH ρ hρ).2)

/-- **Non-vacuity.** The line `V¹ = ℂ` with `Θ₁ = ½`, `B(x, y) = xy` and `∗₁ = conj` is a
`SurfaceDatum`. -/
noncomputable def lineModel : SurfaceDatum ℂ where
  Θ := (1 / 2 : ℂ) • LinearMap.id
  B := LinearMap.mul ℂ ℂ
  B_weight x y := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.mul_apply', smul_eq_mul]
    ring
  B_nondeg x hx := by simpa using hx 1
  star := (starLinearEquiv ℂ (A := ℂ)).toLinearMap
  star_bijective := (starLinearEquiv ℂ (A := ℂ)).bijective
  star_comm x := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      starLinearEquiv_apply, smul_eq_mul, star_mul', Complex.star_def, map_div₀, map_one,
      map_ofNat]
  B_star x y := by simp
  h_conj_symm x y := by simp [mul_comm]

end SurfaceDatum

end WeilRH
