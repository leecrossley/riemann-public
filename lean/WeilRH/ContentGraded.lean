/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ContentAssembly
import WeilRH.TrivialModelFull

/-!
# `prop:content` (iii) in degrees 0 and 2

Source: the manuscript `latex/notes.tex`, `prop:content` (iii), `def:trivial-model`.

`ContentAssembly.D` is the degree-one slice of the Weil datum of `prop:content` (iii). As for the
trivial model (`TrivialModelFull`), the full datum adds `V^0 = ℂ·1` and `V^2 = ℂη` with
`Θ_0 = 0`, `Θ_2 = 1`, `Tr = id`, stars `*_0 = *_2 = conj` (`TrivialModel.model0`, `model2`), and
the product `u ∪ v = B(u, v) η` on `V^1` with the unit products otherwise.

## Main results

* `PairingModel.B_antisymm`: `B` is alternating when `sgn(σ x) = -sgn(x)`.
* `PairingModel.mul_assoc'`, `mul_comm_graded`, `one_mul'`, `mul_one'`, `thetaTot_mul`: the product
  on `ℂ·1 ⊕ V^1 ⊕ ℂη` is associative, graded-commutative and unital, and `Θ` is a derivation.
* **`ContentAssembly.content_indef_graded`**: for the assembled datum of `prop:content` (iii) all
  of these hold, and degrees 0 and 2 carry the positive data `model0`, `model2`.
-/

open Module Complex ComplexConjugate DirectSum

namespace WeilRH.PairingModel

variable {X : Type} (P : Data X) [DecidableEq X]

lemma B_lof_lof (i j : X) :
    B P (DirectSum.lof ℂ X (fun _ => ℂ) i 1) (DirectSum.lof ℂ X (fun _ => ℂ) j 1) =
      if j = P.swp i then P.sgn i else 0 := by
  rw [B_lof, lof_eval]; split_ifs <;> ring

/-- `B` is alternating, `B(u, v) = -B(v, u)`, when `sgn(σ x) = -sgn(x)`. -/
theorem B_antisymm (halt : ∀ x, P.sgn (P.swp x) = -P.sgn x) (u v : V X) :
    B P u v = -B P v u := by
  have key : (B P : V X →ₗ[ℂ] V X →ₗ[ℂ] ℂ) = -(B P).flip := by
    refine DirectSum.linearMap_ext ℂ fun i => ?_
    refine LinearMap.ext_ring ?_
    refine DirectSum.linearMap_ext ℂ fun j => ?_
    refine LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.flip_apply, B_lof_lof]
    by_cases h : j = P.swp i
    · subst h
      simp [P.swp_swp, halt]
    · have h' : ¬ i = P.swp j := fun hij => h (by rw [hij, P.swp_swp])
      simp [h, h']
  simpa using LinearMap.congr_fun₂ key u v

/-- The total space `V^0 ⊕ V^1 ⊕ V^2 = ℂ·1 ⊕ V^1 ⊕ ℂη`. -/
abbrev Tot (X : Type) := ℂ × V X × ℂ

/-- The product `(a, u, c)(a', u', c') = (aa', au' + a'u, ac' + ca' + B(u, u'))`. -/
noncomputable def mul (x y : Tot X) : Tot X :=
  (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1, x.1 * y.2.2 + x.2.2 * y.1 + B P x.2.1 y.2.1)

/-- The unit `1 ∈ V^0`. -/
def one : Tot X := (1, 0, 0)

/-- AW1: the product is associative. -/
theorem mul_assoc' (x y z : Tot X) : mul P (mul P x y) z = mul P x (mul P y z) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y; obtain ⟨a'', u'', c''⟩ := z
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by module, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- AW1: the product is graded-commutative (degree-one elements anticommute). -/
theorem mul_comm_graded (halt : ∀ x, P.sgn (P.swp x) = -P.sgn x) (x y : Tot X) :
    mul P y x =
      (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1, x.1 * y.2.2 + x.2.2 * y.1 - B P x.2.1 y.2.1) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y
  simp only [mul, Prod.mk.injEq]
  refine ⟨mul_comm _ _, add_comm _ _, ?_⟩
  rw [B_antisymm P halt u' u]
  ring

/-- AW1: `1 ∈ V^0` is a left unit. -/
@[simp] theorem one_mul' (x : Tot X) : mul P one x = x := by
  obtain ⟨a, u, c⟩ := x; simp [mul, one]

/-- AW1: `1 ∈ V^0` is a right unit. -/
@[simp] theorem mul_one' (x : Tot X) : mul P x one = x := by
  obtain ⟨a, u, c⟩ := x; simp [mul, one]

/-- The flow generator: `Θ_0 = 0`, `Θ_1`, `Θ_2 = 1`. -/
noncomputable def thetaTot (x : Tot X) : Tot X := (0, theta P x.2.1, x.2.2)

/-- AW1: `Θ` is a derivation of the product. -/
theorem thetaTot_mul (x y : Tot X) :
    thetaTot P (mul P x y) = mul P (thetaTot P x) y + mul P x (thetaTot P y) := by
  obtain ⟨a, u, c⟩ := x; obtain ⟨a', u', c'⟩ := y
  simp only [thetaTot, mul, Prod.mk_add_mk, Prod.mk.injEq, map_add, map_smul]
  refine ⟨by ring, by module, ?_⟩
  rw [B_theta P u u']
  ring

end WeilRH.PairingModel

namespace WeilRH.ContentAssembly

open PairingModel

variable {ιL ιP ιQ : Type} (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ)
  (lQ : ιQ → ℂ)

/-- The assembled signs are alternating: `sgn(σ x) = -sgn(x)`. -/
lemma sgn_swp (x : X ιL ιP ιQ) :
    (data ρL hline ρP lQ).sgn ((data ρL hline ρP lQ).swp x) = -(data ρL hline ρP lQ).sgn x := by
  rcases x with ⟨p, b⟩ | ⟨p, b⟩ | ⟨q, k⟩
  · cases b <;> simp [data, swp, sgn, bsgn]
  · cases b <;> simp [data, swp, sgn, bsgn]
  · fin_cases k <;> simp [data, swp, sgn, qsgn, qswp]

variable [DecidableEq ιL] [DecidableEq ιP] [DecidableEq ιQ]

/-- **`prop:content` (iii), degrees 0 and 2.** For the assembled datum of `prop:content` (iii)
(`content_indef` gives its degree-one properties), the graded space `ℂ·1 ⊕ V^1 ⊕ ℂη` with
`u ∪ v = B(u, v)η` is an associative, graded-commutative, unital algebra on which
`Θ = (0, Θ_1, 1)` is a derivation (AW1 for `U = 𝟙`), and degrees 0 and 2 carry the Weil data
`model0`, `model2` of type `(1, 0)` (`Θ_0 = 0`, `Θ_2 = 1`, `*_0 = *_2 = conj`) with positive
definite star forms. -/
theorem content_indef_graded :
    (∀ x y z : Tot (X ιL ιP ιQ), mul (data ρL hline ρP lQ) (mul (data ρL hline ρP lQ) x y) z =
      mul (data ρL hline ρP lQ) x (mul (data ρL hline ρP lQ) y z)) ∧
    (∀ x y : Tot (X ιL ιP ιQ), mul (data ρL hline ρP lQ) y x =
      (x.1 * y.1, x.1 • y.2.1 + y.1 • x.2.1,
        x.1 * y.2.2 + x.2.2 * y.1 - B (data ρL hline ρP lQ) x.2.1 y.2.1)) ∧
    (∀ x : Tot (X ιL ιP ιQ), mul (data ρL hline ρP lQ) one x = x ∧
      mul (data ρL hline ρP lQ) x one = x) ∧
    (∀ x y : Tot (X ιL ιP ιQ), thetaTot (data ρL hline ρP lQ) (mul (data ρL hline ρP lQ) x y) =
      mul (data ρL hline ρP lQ) (thetaTot (data ρL hline ρP lQ) x) y +
        mul (data ρL hline ρP lQ) x (thetaTot (data ρL hline ρP lQ) y)) ∧
    TrivialModel.model0.IsPositive ∧ TrivialModel.model2.IsPositive :=
  ⟨mul_assoc' _, mul_comm_graded _ (sgn_swp ρL hline ρP lQ), fun x => ⟨one_mul' _ x, mul_one' _ x⟩,
    thetaTot_mul _, TrivialModel.model0_isPositive, TrivialModel.model2_isPositive⟩

end WeilRH.ContentAssembly
