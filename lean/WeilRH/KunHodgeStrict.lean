/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.Kunneth
import WeilRH.AW4Forms
import WeilRH.WeightedAlgebra

/-!
# The split-signature datum (`def:split-datum`, `prop:kun-hodge-strict`)

For `ρ = 1/2 + iγ` the *split-signature datum* of `latex/notes.tex` (`def:split-datum`) has
`V¹ = ℂ⁴` with basis `e₁, e₂, f₁, f₂` (here the coordinates `0, 1, 2, 3`),
`Θ₁ eᵢ = ρ eᵢ`, `Θ₁ fᵢ = ρ̄ fᵢ`, the alternating pairing `B(eᵢ, f_k) = δ_{ik} = -B(f_k, eᵢ)`,
`B(eᵢ, e_k) = B(fᵢ, f_k) = 0`, and the antilinear star `∗₁ eᵢ = εᵢ fᵢ`, `∗₁ fᵢ = -εᵢ eᵢ` with
`(ε₁, ε₂) = (1, -1)`.

The degree-one slice of this datum, with AW1 + AW3 (the weight-one derivation rule of `B` and its
perfectness) and the algebraic part of AW4 in degree one (`def:aw4-alg`), is exactly a
`SurfaceDatum` (`Kunneth.lean`); it is `splitDatum γ`.

`prop:kun-hodge-strict`: the datum satisfies AW4-V and AW4-E in degree one
(`aw4V_splitDatum`, `aw4E_splitDatum`), while `h_⊗ = h₁ ⊗ h₁` is not positive definite on
`V_ρ ⊗ V_{ρ̄}` (`not_posDef_blockGram`): `h₁` is indefinite on `V_ρ` (`h(e₁, e₁) = 1`,
`h(e₂, e₂) = -1`), and `h_⊗(e₁ ⊗ f₂, e₁ ⊗ f₂) = h₁(e₁, e₁) h₁(f₂, f₂) = -1`.
Consequently AW4-E in degree one does not imply the Hodge index clause (`not_hodgeIndex`).

The results hold for every real `γ`; the manuscript's `γ > 0` is used there only so that
`V_ρ = ℂe₁ ⊕ ℂe₂` (for `γ ≠ 0`); here only `eᵢ ∈ V_ρ` and `fᵢ ∈ V_{1-ρ}` are used.
-/

namespace WeilRH

namespace KunHodgeStrict

open Matrix ComplexConjugate Module
open scoped ComplexOrder

noncomputable section

/-- The spectral parameter `ρ = 1/2 + iγ`. -/
def ρ (γ : ℝ) : ℂ := 1 / 2 + γ * Complex.I

lemma ρ_add_conj (γ : ℝ) : ρ γ + conj (ρ γ) = 1 := by
  apply Complex.ext <;> simp [ρ]; norm_num

lemma one_sub_ρ (γ : ℝ) : 1 - ρ γ = conj (ρ γ) := by
  rw [← ρ_add_conj γ]; ring

lemma conj_conj_ρ (γ : ℝ) : conj (conj (ρ γ)) = ρ γ := Complex.conj_conj _

/-- The eigenvalues of `Θ₁` on the basis `e₁, e₂, f₁, f₂`. -/
def ev (γ : ℝ) : Fin 4 → ℂ := ![ρ γ, ρ γ, conj (ρ γ), conj (ρ γ)]

@[simp] lemma ev_zero (γ : ℝ) : ev γ 0 = ρ γ := rfl
@[simp] lemma ev_one (γ : ℝ) : ev γ 1 = ρ γ := rfl
@[simp] lemma ev_two (γ : ℝ) : ev γ 2 = conj (ρ γ) := rfl
@[simp] lemma ev_three (γ : ℝ) : ev γ 3 = conj (ρ γ) := rfl

lemma ev_add_conj (γ : ℝ) (i : Fin 4) : ev γ i + conj (ev γ i) = 1 := by
  fin_cases i
  · exact ρ_add_conj γ
  · exact ρ_add_conj γ
  · simp only [Fin.reduceFinMk, ev_two, Complex.conj_conj]; rw [add_comm]; exact ρ_add_conj γ
  · simp only [Fin.reduceFinMk, ev_three, Complex.conj_conj]; rw [add_comm]; exact ρ_add_conj γ

/-- `Θ₁ = diag(ρ, ρ, ρ̄, ρ̄)`. -/
def Θ (γ : ℝ) : Module.End ℂ (Fin 4 → ℂ) where
  toFun x i := ev γ i * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp; ring

@[simp] lemma Θ_apply (γ : ℝ) (x : Fin 4 → ℂ) (i : Fin 4) : Θ γ x i = ev γ i * x i := rfl

/-- The alternating pairing `B(x, y) = x₀y₂ + x₁y₃ - x₂y₀ - x₃y₁`
(`B(eᵢ, fᵢ) = 1 = -B(fᵢ, eᵢ)`). -/
def B : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1)
    (fun x x' y => by simp; ring) (fun c x y => by simp; ring)
    (fun x y y' => by simp; ring) (fun c x y => by simp; ring)

@[simp] lemma B_apply (x y : Fin 4 → ℂ) :
    B x y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := rfl

/-- The antilinear star `∗₁ e₁ = f₁`, `∗₁ e₂ = -f₂`, `∗₁ f₁ = -e₁`, `∗₁ f₂ = e₂`. -/
def star : (Fin 4 → ℂ) →ₗ⋆[ℂ] (Fin 4 → ℂ) where
  toFun x := ![-conj (x 2), conj (x 3), conj (x 0), -conj (x 1)]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp

@[simp] lemma star_apply (x : Fin 4 → ℂ) :
    star x = ![-conj (x 2), conj (x 3), conj (x 0), -conj (x 1)] := rfl

lemma star_star (x : Fin 4 → ℂ) : star (star x) = -x := by
  funext i; fin_cases i <;> simp

/-- **`def:split-datum`, degree one.** The split-signature datum at `ρ = 1/2 + iγ` as a
`SurfaceDatum`: AW1 + AW3 in degree one and the algebraic part of AW4 (`def:aw4-alg`). -/
def splitDatum (γ : ℝ) : SurfaceDatum (Fin 4 → ℂ) where
  Θ := Θ γ
  B := B
  B_weight x y := by
    simp only [B_apply, Θ_apply, ev_zero, ev_one, ev_two, ev_three]
    linear_combination (x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1) * ρ_add_conj γ
  B_nondeg x hx := by
    have h0 := hx (Pi.single 2 1)
    have h1 := hx (Pi.single 3 1)
    have h2 := hx (Pi.single 0 1)
    have h3 := hx (Pi.single 1 1)
    simp at h0 h1 h2 h3
    funext i; fin_cases i <;> simp_all
  star := star
  star_bijective := by
    refine ⟨fun x y h => ?_, fun y => ⟨-star y, by rw [map_neg, star_star, neg_neg]⟩⟩
    have := congrArg star h
    rw [star_star, star_star] at this
    exact neg_injective this
  star_comm x := by
    funext i; fin_cases i <;> simp
  B_star x y := by simp; ring
  h_conj_symm x y := by simp; ring

variable (γ : ℝ)

/-- The basis vectors `e₁, e₂, f₁, f₂` (coordinates `0, 1, 2, 3`). -/
abbrev bv (i : Fin 4) : Fin 4 → ℂ := Pi.single i (1 : ℂ)

lemma bv_ne_zero (i : Fin 4) : bv i ≠ 0 := by
  intro h; have := congrFun h i; simp at this

lemma Θ_bv (i : Fin 4) : (splitDatum γ).Θ (bv i) = ev γ i • bv i := by
  funext k
  change ev γ k * (Pi.single i (1 : ℂ) : Fin 4 → ℂ) k = ev γ i * (Pi.single i (1 : ℂ) : Fin 4 → ℂ) k
  by_cases h : k = i
  · subst h; rfl
  · simp [h]

lemma bv_mem_eigenspace (i : Fin 4) :
    bv i ∈ (splitDatum γ).Θ.eigenspace (ev γ i) :=
  Module.End.mem_eigenspace_iff.2 (Θ_bv γ i)

/-- `e₁, e₂ ∈ V_ρ`. -/
lemma e_mem (i : Fin 4) (hi : i = 0 ∨ i = 1) : bv i ∈ (splitDatum γ).Vρ (ρ γ) := by
  have : ev γ i = ρ γ := by rcases hi with rfl | rfl <;> rfl
  exact Module.End.eigenspace_le_maxGenEigenspace (this ▸ bv_mem_eigenspace γ i)

/-- `f₁, f₂ ∈ V_{1-ρ} = V_{ρ̄}`. -/
lemma f_mem (i : Fin 4) (hi : i = 2 ∨ i = 3) : bv i ∈ (splitDatum γ).Vρ (1 - ρ γ) := by
  have : ev γ i = 1 - ρ γ := by rcases hi with rfl | rfl <;> simp [ev, one_sub_ρ]
  exact Module.End.eigenspace_le_maxGenEigenspace (this ▸ bv_mem_eigenspace γ i)

/-- `h₁(eᵢ, eᵢ) = h₁(fᵢ, fᵢ) = εᵢ` with `(ε₁, ε₂) = (1, -1)`. -/
lemma h_bv : (splitDatum γ).h (bv 0) (bv 0) = 1 ∧ (splitDatum γ).h (bv 1) (bv 1) = -1 ∧
    (splitDatum γ).h (bv 2) (bv 2) = 1 ∧ (splitDatum γ).h (bv 3) (bv 3) = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [SurfaceDatum.h, splitDatum]

/-- `h₁` is indefinite on `V_ρ` (signature `(1, 1)` on `ℂe₁ ⊕ ℂe₂`). -/
theorem not_definiteOn : ¬ (splitDatum γ).DefiniteOn ((splitDatum γ).Vρ (ρ γ)) := by
  obtain ⟨h0, h1, -, -⟩ := h_bv γ
  rintro (h | h)
  · have := h _ (e_mem γ 1 (Or.inr rfl)) (bv_ne_zero 1); rw [h1] at this; norm_num at this
  · have := h _ (e_mem γ 0 (Or.inl rfl)) (bv_ne_zero 0); rw [h0] at this; norm_num at this

/-- Pure tensors in a positive block: if `h_⊗` is positive definite on `V_ρ ⊗ V_{1-ρ}` then
`h₁(x, x) h₁(y, y) > 0` for nonzero `x ∈ V_ρ`, `y ∈ V_{1-ρ}`. -/
lemma pure_pos_of_posDef {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (D : SurfaceDatum V) (σ : ℂ) (hH : (D.blockGram σ).PosDef) {x y : V} (hx : x ∈ D.Vρ σ)
    (hy : y ∈ D.Vρ (1 - σ)) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    0 < (D.h x x).re * (D.h y y).re := by
  have := SurfaceDatum.nonempty_fin_of_mem hx hx0
  have := SurfaceDatum.nonempty_fin_of_mem hy hy0
  have hK := (posDef_kronecker_iff (D.gram_isHermitian _) (D.gram_isHermitian _)).1 hH
  rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos ((D.gram_posDef_iff _).1 h1 x hx hx0) ((D.gram_posDef_iff _).1 h2 y hy hy0)
  · exact mul_pos_of_neg_of_neg ((D.neg_gram_posDef_iff _).1 h1 x hx hx0)
      ((D.neg_gram_posDef_iff _).1 h2 y hy hy0)

/-- **`prop:kun-hodge-strict`, last clause.** `h_⊗ = h₁ ⊗ h₁` is not positive definite on
`V_ρ ⊗ V_{ρ̄}`: `h_⊗(e₁ ⊗ f₂, e₁ ⊗ f₂) = h₁(e₁, e₁) h₁(f₂, f₂) = -1`. -/
theorem not_posDef_blockGram : ¬ ((splitDatum γ).blockGram (ρ γ)).PosDef := by
  intro hH
  obtain ⟨h0, -, -, h3⟩ := h_bv γ
  have := pure_pos_of_posDef (splitDatum γ) (ρ γ) hH (e_mem γ 0 (Or.inl rfl))
    (f_mem γ 3 (Or.inr rfl)) (bv_ne_zero 0) (bv_ne_zero 3)
  rw [h0, h3] at this; norm_num at this

/-- The split-signature datum fails the Hodge index clause. -/
theorem not_hodgeIndex : ¬ (splitDatum γ).HodgeIndex := fun h => not_posDef_blockGram γ (h _)

/-- The standard form `h₀(u, v) = ∑ᵢ uᵢ v̄ᵢ`, the orthogonal sum of positive definite forms on the
two eigenspaces `ℂe₁ ⊕ ℂe₂` and `ℂf₁ ⊕ ℂf₂`. -/
def h₀ : PosHermForm (Fin 4 → ℂ) where
  toFun u v := ∑ i, u i * conj (v i)
  add_left u u' v := by simp [add_mul, Finset.sum_add_distrib]
  smul_left c u v := by simp [Finset.mul_sum, mul_assoc]
  conj_symm u v := by simp [map_sum, mul_comm]
  re_pos u hu := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    simp only [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

/-- `h₀` is a positive infinitesimal polarization of weight one for `Θ₁`. -/
lemma isInfPol_h₀ : Suspension.IsInfPol h₀ (splitDatum γ).Θ 1 := by
  intro u v
  change ∑ i, ev γ i * u i * conj (v i) + ∑ i, u i * conj (ev γ i * v i) =
    ((1 : ℝ) : ℂ) * ∑ i, u i * conj (v i)
  rw [Complex.ofReal_one, one_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  linear_combination (u i * conj (v i)) * ev_add_conj γ i

/-- **`prop:kun-hodge-strict`: AW4-V in degree one.** -/
theorem aw4V_splitDatum : AW4Forms.AW4V (splitDatum γ).Θ 1 := ⟨h₀, isInfPol_h₀ γ⟩

/-- **`prop:kun-hodge-strict`: AW4-E in degree one** (`prop:aw4-forms` (ii)). -/
theorem aw4E_splitDatum : AW4Forms.AW4E (splitDatum γ).Θ 1 :=
  AW4Forms.aw4E_of_aw4V (Spectral.spectralCore_of_finiteDimensional _) (aw4V_splitDatum γ)

/-- **`prop:kun-hodge-strict`.** The split-signature datum at `ρ = 1/2 + iγ` (a `SurfaceDatum`, so
AW1 + AW3 and the algebraic part of AW4 hold in degree one) satisfies AW4-V and AW4-E in degree
one, and `h_⊗` is not positive definite on `V_ρ ⊗ V_{ρ̄}`. -/
theorem kun_hodge_strict :
    AW4Forms.AW4V (splitDatum γ).Θ 1 ∧ AW4Forms.AW4E (splitDatum γ).Θ 1 ∧
      ¬ ((splitDatum γ).blockGram (ρ γ)).PosDef :=
  ⟨aw4V_splitDatum γ, aw4E_splitDatum γ, not_posDef_blockGram γ⟩

end

end KunHodgeStrict

end WeilRH
