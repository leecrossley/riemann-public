/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.WeightedAlgebra
import WeilRH.ContentGraded
import WeilRH.TrivialModelGraded

/-!
# Graded Weil data with nondegenerate Hermitian star forms (`prop:content` (iii))

Source: the manuscript `latex/notes.tex`, `prop:content` (iii), `def:aw` (AW1, AW3, AW4 without
positivity) and `prop:weighted-algebra-obstruction`.

`WeilRH.WeightedAlgebraDatum` asks for positive definite star forms `h_j`. The datum of
`prop:content` (iii) has forms that are Hermitian and nondegenerate but indefinite as soon as the
divisor has a real pair or a quartet, so it cannot be a `WeightedAlgebraDatum`. This file states
the weaker structure and shows that the assembled datum is an instance of it in all degrees.

## Main results

* `WeilRH.HermAlgebraDatum`: the hypotheses of `WeightedAlgebraDatum` with "positive definite"
  replaced by "nondegenerate" (`h_nondeg`).
* `WeilRH.WeightedAlgebraDatum.toHerm`: every positive datum is a nondegenerate one.
* `WeilRH.HermAlgebraDatum.polarization`: `h_j(Θu, v) + h_j(u, Θv) = (w + j) h_j(u, v)` holds without
  positivity.
* `WeilRH.PairingModel.gradedDatum`: for block data with `π` an involution, `conj g_x = g_{π x}`,
  alternating signs, and a spectral core in degree one, `ℂ·1 ⊕ V^1 ⊕ ℂη` is a
  `HermAlgebraDatum _ 1 0`.
* **`WeilRH.ContentAssembly.gradedDatum`, `gradedDatum_indef`**: the assembled datum of
  `prop:content` (iii), for a finite divisor, is a nonzero `HermAlgebraDatum _ 1 0` whose degree-one
  form takes the values `2` and `-2` when there is a real pair or a quartet.
* The remark after `prop:weighted-algebra-obstruction`: `WeilRH.form_identity_sub` (only the trace
  weight minus the star shift enters the form identity), `WeilRH.derivation_unit_eq_zero` (a
  derivation kills the unit) and `WeilRH.trace_weight_eq_shift_of_unit` (with a unit the two weights
  must agree).

## Fidelity

The degree-one spectral-core condition is a hypothesis of `PairingModel.gradedDatum`; for a finite
divisor it is automatic (`ContentAssembly.gradedDatum`). The source states (iii) for a divisor of
the shape `def:trivial-model` allows; no finiteness is needed for the degree-one statements of
`content_indef`, only for this graded packaging.
-/

open Module Complex ComplexConjugate DirectSum

namespace WeilRH

universe u

/-- **Graded Weil datum with nondegenerate Hermitian star forms.** The hypotheses of
`WeightedAlgebraDatum` with positivity of `h_j(u, v) = Tr(u ∪ *_j v)` replaced by nondegeneracy:
every nonzero `u ∈ V^j` pairs nontrivially with some `v ∈ V^j`. -/
structure HermAlgebraDatum (V : Type u) [AddCommGroup V] [Module ℂ V] (d : ℕ) (w : ℝ) where
  /-- The graded piece `V^j`. -/
  G : ℕ → Submodule ℂ V
  /-- `V^j = 0` for `j > 2d`. -/
  vanish : ∀ j, 2 * d < j → G j = ⊥
  /-- The cup product. -/
  mul : V →ₗ[ℂ] V →ₗ[ℂ] V
  mul_mem : ∀ {i k : ℕ} {x y : V}, x ∈ G i → y ∈ G k → mul x y ∈ G (i + k)
  /-- The generator. -/
  Θ : Module.End ℂ V
  Θ_mem : ∀ {j : ℕ} {x : V}, x ∈ G j → Θ x ∈ G j
  /-- `Θ` is a derivation. -/
  Θ_mul : ∀ x y, Θ (mul x y) = mul (Θ x) y + mul x (Θ y)
  /-- Each `(V^j, Θ_j)` is a spectral core. -/
  spectralCore : ∀ j, Spectral.SpectralCore (Θ.restrict (p := G j) (q := G j) fun _ hx => Θ_mem hx)
  /-- The trace on `V^{2d}`. -/
  Tr : V →ₗ[ℂ] ℂ
  Tr_Θ : ∀ x ∈ G (2 * d), Tr (Θ x) = ((d : ℂ) + w) * Tr x
  /-- The antilinear star `*_j : V^j → V^{2d-j}`. -/
  st : ℕ → V →ₗ⋆[ℂ] V
  st_mem : ∀ {j : ℕ} {x : V}, x ∈ G j → st j x ∈ G (2 * d - j)
  /-- `Θ_{2d-j} *_j = *_j Θ_j + (d - j) *_j`. -/
  Θ_st : ∀ {j : ℕ} {x : V}, x ∈ G j → Θ (st j x) = st j (Θ x) + ((d : ℂ) - j) • st j x
  /-- `h_j` is Hermitian. -/
  h_conj : ∀ {j : ℕ} {u v : V}, u ∈ G j → v ∈ G j →
    conj (Tr (mul u (st j v))) = Tr (mul v (st j u))
  /-- `h_j` is nondegenerate. -/
  h_nondeg : ∀ {j : ℕ} {u : V}, u ∈ G j → u ≠ 0 → ∃ v ∈ G j, Tr (mul u (st j v)) ≠ 0

/-- A positive graded Weil datum is a nondegenerate one (take `v = u`). -/
def WeightedAlgebraDatum.toHerm {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ} {w : ℝ}
    (D : WeightedAlgebraDatum V d w) : HermAlgebraDatum V d w where
  G := D.G
  vanish := D.vanish
  mul := D.mul
  mul_mem := D.mul_mem
  Θ := D.Θ
  Θ_mem := D.Θ_mem
  Θ_mul := D.Θ_mul
  spectralCore := D.spectralCore
  Tr := D.Tr
  Tr_Θ := D.Tr_Θ
  st := D.st
  st_mem := D.st_mem
  Θ_st := D.Θ_st
  h_conj := D.h_conj
  h_nondeg {_ u} hu hu0 := ⟨u, hu, fun h => by simpa [h] using D.h_pos hu hu0⟩

namespace HermAlgebraDatum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ} {w : ℝ}
  (D : HermAlgebraDatum V d w)

/-- The form `h_j(u, v) = Tr(u ∪ *_j v)`. -/
def h (j : ℕ) (u v : V) : ℂ := D.Tr (D.mul u (D.st j v))

/-- **The polarization identity of weight `w + j`**, from the derivation, trace and star laws
alone (positivity is not used). -/
theorem polarization {j : ℕ} {u v : V} (hu : u ∈ D.G j) (hv : v ∈ D.G j) :
    D.h j (D.Θ u) v + D.h j u (D.Θ v) = ((w + j : ℝ) : ℂ) * D.h j u v := by
  by_cases hj : j ≤ 2 * d
  · have hx : D.mul u (D.st j v) ∈ D.G (2 * d) := by
      have := D.mul_mem hu (D.st_mem hv)
      rwa [Nat.add_sub_cancel' hj] at this
    have key := D.Tr_Θ _ hx
    rw [D.Θ_mul, D.Θ_st hv, map_add, map_add, map_smul, map_add, map_smul, smul_eq_mul] at key
    simp only [h]
    push_cast
    linear_combination key
  · have : u = 0 := by
      have hG := D.vanish j (by omega)
      rw [hG] at hu
      exact (Submodule.mem_bot ℂ).mp hu
    subst this
    simp [h]

end HermAlgebraDatum

namespace PairingModel

variable {X : Type} (P : Data X) [DecidableEq X]

/-- The product `mul` as a bilinear map. -/
noncomputable def mulL : Tot X →ₗ[ℂ] Tot X →ₗ[ℂ] Tot X :=
  LinearMap.mk₂ ℂ (mul P)
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

@[simp] lemma mulL_apply (x y : Tot X) : mulL P x y = mul P x y := rfl

/-- The flow `thetaTot` as a linear map. -/
noncomputable def thetaL : Module.End ℂ (Tot X) where
  toFun := thetaTot P
  map_add' x y := by simp [thetaTot]
  map_smul' c x := by simp [thetaTot]

omit [DecidableEq X] in
@[simp] lemma thetaL_apply (x : Tot X) : thetaL P x = thetaTot P x := rfl

/-- The grading: `V^0 = ℂ·1`, `V^1`, `V^2 = ℂη`, and `0` above degree `2`. -/
def G : ℕ → Submodule ℂ (Tot X)
  | 0 => LinearMap.ker (LinearMap.snd ℂ ℂ (V X × ℂ))
  | 1 => LinearMap.ker (LinearMap.fst ℂ ℂ (V X × ℂ)) ⊓
      LinearMap.ker ((LinearMap.snd ℂ (V X) ℂ).comp (LinearMap.snd ℂ ℂ (V X × ℂ)))
  | 2 => LinearMap.ker (LinearMap.fst ℂ ℂ (V X × ℂ)) ⊓
      LinearMap.ker ((LinearMap.fst ℂ (V X) ℂ).comp (LinearMap.snd ℂ ℂ (V X × ℂ)))
  | _ + 3 => ⊥

omit [DecidableEq X] in
lemma mem_G0 {x : Tot X} : x ∈ G 0 ↔ x.2.1 = 0 ∧ x.2.2 = 0 := by
  simp [G, Prod.ext_iff]
omit [DecidableEq X] in
lemma mem_G1 {x : Tot X} : x ∈ G 1 ↔ x.1 = 0 ∧ x.2.2 = 0 := by simp [G]
omit [DecidableEq X] in
lemma mem_G2 {x : Tot X} : x ∈ G 2 ↔ x.1 = 0 ∧ x.2.1 = 0 := by simp [G]
omit [DecidableEq X] in
lemma mem_G3 {n : ℕ} {x : Tot X} : x ∈ G (n + 3) ↔ x = 0 := by simp [G]

/-- `V^0 ≅ ℂ`. -/
noncomputable def deg0Equiv : G (X := X) 0 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective ((LinearMap.fst ℂ ℂ (V X × ℂ)).comp (G 0).subtype) <| by
    refine ⟨fun x y h => ?_, fun a => ⟨⟨(a, 0, 0), by simp [mem_G0]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G0] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

/-- `V^2 ≅ ℂ`. -/
noncomputable def deg2Equiv : G (X := X) 2 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective ((LinearMap.snd ℂ (V X) ℂ).comp
      ((LinearMap.snd ℂ ℂ (V X × ℂ)).comp (G 2).subtype)) <| by
    refine ⟨fun x y h => ?_, fun c => ⟨⟨(0, 0, c), by simp [mem_G2]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G2] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

/-- `V^1 ≅ V X`. -/
noncomputable def deg1Equiv : G (X := X) 1 ≃ₗ[ℂ] V X :=
  LinearEquiv.ofBijective ((LinearMap.fst ℂ (V X) ℂ).comp
      ((LinearMap.snd ℂ ℂ (V X × ℂ)).comp (G 1).subtype)) <| by
    refine ⟨fun x y h => ?_, fun u => ⟨⟨(0, u, 0), by simp [mem_G1]⟩, rfl⟩⟩
    obtain ⟨⟨a, u, c⟩, hx⟩ := x; obtain ⟨⟨b, v, e⟩, hy⟩ := y
    rw [mem_G1] at hx hy; obtain ⟨rfl, rfl⟩ := hx; obtain ⟨rfl, rfl⟩ := hy
    simpa using h

omit [DecidableEq X] in
lemma deg1Equiv_symm_apply (u : V X) : ((deg1Equiv (X := X)).symm u : Tot X) = (0, u, 0) := by
  have : (deg1Equiv (X := X)).symm u = ⟨(0, u, 0), by simp [mem_G1]⟩ :=
    (deg1Equiv (X := X)).symm_apply_eq.mpr rfl
  rw [this]

instance : FiniteDimensional ℂ (G (X := X) 0) := deg0Equiv.symm.finiteDimensional
instance : FiniteDimensional ℂ (G (X := X) 2) := deg2Equiv.symm.finiteDimensional
instance (n : ℕ) : FiniteDimensional ℂ (G (X := X) (n + 3)) := by
  rw [show G (X := X) (n + 3) = ⊥ from rfl]; infer_instance

omit [DecidableEq X] in
/-- The degree-one summand is a spectral core when `(V X, Θ_1)` is. -/
theorem spectralCore_G1 (hsc : Spectral.SpectralCore (theta P)) :
    Spectral.SpectralCore ((thetaL P).restrict (p := G (X := X) 1) (q := G 1) fun x hx => by
      obtain ⟨a, u, c⟩ := x; rw [mem_G1] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]) :=
  hsc.of_equiv (deg1Equiv (X := X)).symm fun u => by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, deg1Equiv_symm_apply, deg1Equiv_symm_apply]
    simp [thetaTot]

/-- `*_0(a) = ā η`. -/
noncomputable def st0 : Tot X →ₗ⋆[ℂ] Tot X where
  toFun x := (0, 0, conj x.1)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- `*_1 = star` on `V^1`. -/
noncomputable def st1 : Tot X →ₗ⋆[ℂ] Tot X where
  toFun x := (0, star P x.2.1, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- `*_2(c η) = c̄`. -/
noncomputable def st2 : Tot X →ₗ⋆[ℂ] Tot X where
  toFun x := (conj x.2.2, 0, 0)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The stars `*_j`, with `*_j = 0` for `j > 2`. -/
noncomputable def st : ℕ → Tot X →ₗ⋆[ℂ] Tot X
  | 0 => st0
  | 1 => st1 P
  | 2 => st2
  | _ + 3 => 0

@[simp] lemma st_add_three (n : ℕ) : st P (n + 3) = 0 := rfl

/-- `Tr(a, u, c) = c`. -/
noncomputable def trT : Tot X →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ (V X) ℂ).comp (LinearMap.snd ℂ ℂ (V X × ℂ))

lemma B_star_eq_h (u v : V X) : B P u (star P v) = (datum P).h u v := by
  simp [WeightedStarDatum.h, WeightedStarDatum.B, datum]

/-- **Block data as a graded Weil datum with nondegenerate Hermitian forms**: for `π` an
involution with `conj g_x = g_{π x}` and a spectral core in degree one, `ℂ·1 ⊕ V^1 ⊕ ℂη` with
`Θ = (0, Θ_1, 1)`, `Tr(a, u, c) = c`, stars `conj, *_1, conj` is a `HermAlgebraDatum _ 1 0`. -/
noncomputable def gradedDatum (hπ : ∀ x, P.π (P.π x) = x)
    (hg : ∀ x, conj (P.g x) = P.g (P.π x)) (hsc : Spectral.SpectralCore (theta P)) :
    HermAlgebraDatum (Tot X) 1 0 where
  G := G
  vanish j hj := by
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 3 := ⟨j - 3, by omega⟩
    rfl
  mul := mulL P
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
  Θ := thetaL P
  Θ_mem {j x} hx := by
    obtain ⟨a, u, c⟩ := x
    match j, hx with
    | 0, hx => rw [mem_G0] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | 1, hx => rw [mem_G1] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | 2, hx => rw [mem_G2] at hx ⊢; obtain ⟨rfl, rfl⟩ := hx; simp [thetaTot]
    | n + 3, hx => rw [mem_G3] at hx ⊢; simp [hx, thetaTot]
  Θ_mul x y := by simpa using thetaTot_mul P x y
  spectralCore j := by
    match j with
    | 0 => exact Spectral.spectralCore_of_finiteDimensional _
    | 1 => exact spectralCore_G1 P hsc
    | 2 => exact Spectral.spectralCore_of_finiteDimensional _
    | n + 3 => exact Spectral.spectralCore_of_finiteDimensional _
  Tr := trT
  Tr_Θ x hx := by
    obtain ⟨a, u, c⟩ := x
    rw [show 2 * 1 = 2 from rfl, mem_G2] at hx; obtain ⟨rfl, rfl⟩ := hx
    simp [trT, thetaTot]
  st := st P
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
      simp [st, st1, thetaTot, theta_star]
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
      rw [B_star_eq_h, B_star_eq_h]
      exact h_conj_symm P hπ hg u v
    | 2, hu, hv =>
      rw [mem_G2] at hu hv; obtain ⟨rfl, rfl⟩ := hu; obtain ⟨rfl, rfl⟩ := hv
      simp [st, st2, trT, mul, mul_comm]
    | n + 3, hu, hv => rw [mem_G3] at hu hv; rw [hu, hv]; simp
  h_nondeg {j u} hu hu0 := by
    obtain ⟨a, u, c⟩ := u
    match j, hu with
    | 0, hu =>
      rw [mem_G0] at hu; obtain ⟨rfl, rfl⟩ := hu
      have ha : a ≠ 0 := fun h => hu0 (by simp [h])
      refine ⟨(a, 0, 0), by simp [mem_G0], ?_⟩
      simp only [st, st0, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
        add_zero, map_zero]
      rw [Complex.mul_conj]; exact_mod_cast (Complex.normSq_pos.mpr ha).ne'
    | 1, hu =>
      rw [mem_G1] at hu; obtain ⟨rfl, rfl⟩ := hu
      have hu' : u ≠ 0 := fun h => hu0 (by simp [h])
      obtain ⟨v, hv⟩ := h_nondegenerate P hπ hu'
      refine ⟨(0, v, 0), by simp [mem_G1], ?_⟩
      simp only [st, st1, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
        add_zero, zero_add]
      rwa [B_star_eq_h]
    | 2, hu =>
      rw [mem_G2] at hu; obtain ⟨rfl, rfl⟩ := hu
      have hc : c ≠ 0 := fun h => hu0 (by simp [h])
      refine ⟨(0, 0, c), by simp [mem_G2], ?_⟩
      simp only [st, st2, trT, mulL_apply, mul, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero, zero_mul,
        zero_add, add_zero, map_zero]
      rw [Complex.mul_conj]; exact_mod_cast (Complex.normSq_pos.mpr hc).ne'
    | n + 3, hu => rw [mem_G3] at hu; exact absurd hu hu0

/-- In degree one the form of `gradedDatum` is the form `h_1` of the degree-one datum `datum`. -/
lemma gradedDatum_h_one (hπ : ∀ x, P.π (P.π x) = x)
    (hg : ∀ x, conj (P.g x) = P.g (P.π x)) (hsc : Spectral.SpectralCore (theta P)) (u v : V X) :
    (gradedDatum P hπ hg hsc).h 1 (0, u, 0) (0, v, 0) = (datum P).h u v := by
  simp only [HermAlgebraDatum.h, gradedDatum, st, st1, trT, mulL_apply, mul, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply, mul_zero,
    add_zero, zero_add]
  exact B_star_eq_h P u v

end PairingModel

namespace ContentAssembly

open PairingModel

variable {ιL ιP ιQ : Type} (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ)
  (lQ : ιQ → ℂ) [DecidableEq ιL] [DecidableEq ιP] [DecidableEq ιQ]
  [Fintype ιL] [Fintype ιP] [Fintype ιQ]

/-- **`prop:content` (iii) as one graded datum**: for a finite divisor the assembled datum on
`ℂ·1 ⊕ V^1 ⊕ ℂη` is a `HermAlgebraDatum _ 1 0` (AW1, AW3 trace, AW4 star laws, Hermitian
nondegenerate forms in every degree). -/
noncomputable def gradedDatum : HermAlgebraDatum (Tot (X ιL ιP ιQ)) 1 0 :=
  PairingModel.gradedDatum (data ρL hline ρP lQ) (π_π ρL hline ρP lQ) (conj_g ρL hline ρP lQ)
    (Spectral.spectralCore_of_finiteDimensional _)

/-- **The graded datum of `prop:content` (iii) is nonzero and indefinite**: `1 ∈ V^0`, and with a
real pair or a quartet its degree-one form takes the values `2` and `-2`, so it is not a positive
(`WeightedAlgebraDatum`) datum. -/
theorem gradedDatum_indef :
    one ∈ (gradedDatum ρL hline ρP lQ).G 0 ∧ (one : Tot (X ιL ιP ιQ)) ≠ 0 ∧
    (Nonempty ιP ∨ Nonempty ιQ → ∃ u v : V (X ιL ιP ιQ),
      (gradedDatum ρL hline ρP lQ).h 1 (0, u, 0) (0, u, 0) = 2 ∧
      (gradedDatum ρL hline ρP lQ).h 1 (0, v, 0) (0, v, 0) = -2) := by
  refine ⟨by simp [gradedDatum, PairingModel.gradedDatum, mem_G0, one], fun h => ?_, fun hne => ?_⟩
  · have := congrArg Prod.fst h
    simp [one] at this
  · obtain ⟨u, v, hu, hv⟩ := (content_indef ρL hline ρP lQ).2.2.2.2 hne
    refine ⟨u, v, ?_, ?_⟩
    · rw [gradedDatum, gradedDatum_h_one]; exact hu
    · rw [gradedDatum, gradedDatum_h_one]; exact hv

end ContentAssembly

namespace ContentAssembly

open PairingModel

variable {ιL ιP ιQ : Type} (ρL : ιL → ℂ) (hline : ∀ p, (ρL p).re = 1 / 2) (ρP : ιP → ℝ)
  (lQ : ιQ → ℂ) [DecidableEq ιL] [DecidableEq ιP] [DecidableEq ιQ]
  (hfin : ∀ σ, {x | lamX ρL ρP lQ x = σ}.Finite)
  (hdisc : ∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range (lamX ρL ρP lQ))))

/-- **`prop:content` (iii) as one graded datum, any divisor**: for a divisor with finite
multiplicities and no finite accumulation point (the divisors `def:trivial-model` allows),
the assembled datum on `ℂ·1 ⊕ V^1 ⊕ ℂη` is a `HermAlgebraDatum _ 1 0`. -/
noncomputable def gradedDatumInf : HermAlgebraDatum (Tot (X ιL ιP ιQ)) 1 0 :=
  PairingModel.gradedDatum (data ρL hline ρP lQ) (π_π ρL hline ρP lQ) (conj_g ρL hline ρP lQ)
    (PairingModel.spectralCore_theta _ hfin hdisc)

/-- **The graded datum of `prop:content` (iii) for any divisor is nonzero and indefinite**:
`1 ∈ V^0`, and with a real pair or a quartet its degree-one form takes the values `2` and `-2`. -/
theorem gradedDatumInf_indef :
    one ∈ (gradedDatumInf ρL hline ρP lQ hfin hdisc).G 0 ∧ (one : Tot (X ιL ιP ιQ)) ≠ 0 ∧
    (Nonempty ιP ∨ Nonempty ιQ → ∃ u v : V (X ιL ιP ιQ),
      (gradedDatumInf ρL hline ρP lQ hfin hdisc).h 1 (0, u, 0) (0, u, 0) = 2 ∧
      (gradedDatumInf ρL hline ρP lQ hfin hdisc).h 1 (0, v, 0) (0, v, 0) = -2) := by
  refine ⟨by simp [gradedDatumInf, PairingModel.gradedDatum, mem_G0, one], fun h => ?_,
    fun hne => ?_⟩
  · have := congrArg Prod.fst h
    simp [one] at this
  · obtain ⟨u, v, hu, hv⟩ := (content_indef ρL hline ρP lQ).2.2.2.2 hne
    refine ⟨u, v, ?_, ?_⟩
    · rw [gradedDatumInf, gradedDatum_h_one]; exact hu
    · rw [gradedDatumInf, gradedDatum_h_one]; exact hv

end ContentAssembly

/-! ### Where the weight can sit (remark after `prop:weighted-algebra-obstruction`) -/

section WeightPlacement

variable {V W T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup T] [Module ℂ T]

/-- **Only the difference `τ - κ` enters the form identity.** For a derivation `Θ` of a pairing
`∪ : V × W → T`, a trace with `Tr(Θx) = τ Tr(x)` and an antilinear star with
`Θ(*v) = *(Θv) + κ *v`, the form `h(u, v) = Tr(u ∪ *v)` satisfies
`h(Θu, v) + h(u, Θv) = (τ - κ) h(u, v)`. Moving weight between the trace and the star shift
therefore changes nothing while `τ - κ` is fixed. -/
theorem form_identity_sub (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) (ΘT : Module.End ℂ T)
    (cup : V →ₗ[ℂ] W →ₗ[ℂ] T)
    (hcup : ∀ u w, ΘT (cup u w) = cup (ΘV u) w + cup u (ΘW w))
    (Tr : T →ₗ[ℂ] ℂ) (τ : ℂ) (hTr : ∀ x, Tr (ΘT x) = τ * Tr x)
    (S : V →ₗ⋆[ℂ] W) (κ : ℂ) (hS : ∀ v, ΘW (S v) = S (ΘV v) + κ • S v) (u v : V) :
    Tr (cup (ΘV u) (S v)) + Tr (cup u (S (ΘV v))) = (τ - κ) * Tr (cup u (S v)) := by
  have key := hTr (cup u (S v))
  rw [hcup, hS v, map_add, map_add, map_smul, map_add, map_smul, smul_eq_mul] at key
  linear_combination key

/-- **A derivation kills the unit.** If `1` is a two-sided unit for a bilinear product and `Θ` is
a derivation, then `Θ 1 = 0`. -/
theorem derivation_unit_eq_zero (mul : V →ₗ[ℂ] V →ₗ[ℂ] V) (Θ : Module.End ℂ V) (one : V)
    (hl : ∀ x, mul one x = x) (hr : ∀ x, mul x one = x)
    (hΘ : ∀ x y, Θ (mul x y) = mul (Θ x) y + mul x (Θ y)) : Θ one = 0 := by
  have h := hΘ one one
  rw [hl, hl, hr] at h
  have : Θ one + Θ one - Θ one = 0 := by rw [← h]; abel
  simpa using this

/-- **The unit forces `τ = κ_0`.** With a unit `1 ∈ V^0` (so `Θ 1 = 0`), a trace weight `τ` and a
degree-zero star shift `κ` whose form is nonzero at `1`, the two weights agree. In particular no
redistribution of a nonzero weight between trace and star avoids
`prop:weighted-algebra-obstruction`; only a change of the derivation rule could. -/
theorem trace_weight_eq_shift_of_unit (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W)
    (ΘT : Module.End ℂ T) (cup : V →ₗ[ℂ] W →ₗ[ℂ] T)
    (hcup : ∀ u w, ΘT (cup u w) = cup (ΘV u) w + cup u (ΘW w))
    (Tr : T →ₗ[ℂ] ℂ) (τ : ℂ) (hTr : ∀ x, Tr (ΘT x) = τ * Tr x)
    (S : V →ₗ⋆[ℂ] W) (κ : ℂ) (hS : ∀ v, ΘW (S v) = S (ΘV v) + κ • S v)
    (one : V) (hone : ΘV one = 0) (hpos : Tr (cup one (S one)) ≠ 0) : τ = κ := by
  have h := form_identity_sub ΘV ΘW ΘT cup hcup Tr τ hTr S κ hS one one
  rw [hone, map_zero, map_zero, LinearMap.zero_apply, map_zero, map_zero, map_zero,
    zero_add] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hpos)

end WeightPlacement

end WeilRH
