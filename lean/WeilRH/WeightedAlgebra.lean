/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Multiplicities
import WeilRH.Hermitian
import WeilRH.Spectral

/-!
# The fixed-weight internal algebra obstruction

Source: the manuscript `latex/notes.tex`, `prop:weighted-algebra-obstruction` (with
`def:graded-realization` and `def:spectral-core`).

Let `V^•` be a graded complex algebra of spectral cores in degrees `0, …, 2d`, with a derivation
`Θ`, a trace satisfying `Tr(Θx) = (d + w) Tr(x)`, and antilinear stars `*_j : V^j → V^{2d-j}` with
`Θ *_j = *_j Θ + (d - j) *_j`. If every `h_j(u, v) = Tr(u ∪ *_j v)` is positive definite Hermitian
and `w ≠ 0`, every `V^j` is zero; a nonzero unital algebra forces `w = 0`.

## Encoding

The graded pieces `V^j` are submodules `G j` of one complex vector space `V`, zero above `2d`.
The cup product is a bilinear map `mul : V → V → V` sending `V^i × V^k` into `V^{i+k}`; the trace
and the stars are maps on `V` whose hypotheses are imposed only on the relevant degree. Each
`(V^j, Θ|V^j)` is a `Spectral.SpectralCore`. Associativity, the unit and the spanning of `V` by the
`V^j` are not assumed, since the proof does not use them.

## Main results

* `WeilRH.WeightedAlgebraDatum.polarization`: `h_j(Θu, v) + h_j(u, Θv) = (w + j) h_j(u, v)`.
* `WeilRH.WeightedAlgebraDatum.re_eq_of_hasEigenvalue`: eigenvalues on `V^j` have real part
  `(w + j)/2`.
* `WeilRH.WeightedAlgebraDatum.mul_eq_zero`: for `w ≠ 0` all products vanish.
* `WeilRH.WeightedAlgebraDatum.eq_bot`: for `w ≠ 0` every `V^j` is zero.
* `WeilRH.WeightedAlgebraDatum.eq_zero_of_unit`: a nonzero algebra with a unit in degree zero has
  `w = 0`.
* `WeilRH.WeightedAlgebraDatum.trivialModel`, `trivialModel_nontrivial`: a nonzero unital datum
  with `w = 0`, so the structure is not vacuous; `WeilRH.Spectral.spectralCore_of_finiteDimensional`.
-/

open scoped ComplexConjugate

namespace WeilRH

namespace Spectral

open Filter
/-- Every endomorphism of a finite-dimensional complex space is a spectral core. -/
theorem spectralCore_of_finiteDimensional {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (Θ : Module.End ℂ V) : SpectralCore Θ where
  iSup_eq_top := Module.End.iSup_maxGenEigenspace_eq_top Θ
  finiteDimensional _ := inferInstance
  noAccPt z hz := by
    refine (Set.Infinite.of_accPt hz) ((Module.End.finite_hasEigenvalue Θ).subset ?_)
    intro ρ hρ
    have : Θ.HasUnifEigenvalue ρ ⊤ := hρ
    exact (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).mp this
end Spectral

namespace PosHermForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : PosHermForm V)

/-- Under `h(Θu, v) + h(u, Θv) = κ h(u, v)` for a positive definite Hermitian `h`, generalized
eigenvectors are eigenvectors (any dimension). -/
theorem maxGenEigenspace_eq_eigenspace (Θ : Module.End ℂ V) (κ : ℝ)
    (hP : ∀ u v, h.toFun (Θ u) v + h.toFun u (Θ v) = (κ : ℂ) * h.toFun u v) (ρ : ℂ) :
    Θ.maxGenEigenspace ρ = Θ.eigenspace ρ := by
  let _ : NormedAddCommGroup V := h.core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore h.core.toCore
  exact WeilRH.maxGenEigenspace_eq_eigenspace_of_P Θ κ hP ρ

end PosHermForm

universe u

/-- **`prop:weighted-algebra-obstruction`, hypotheses.** A graded complex algebra of spectral
cores in degrees `0, …, 2d` with derivation `Θ`, trace of weight `d + w`, and stars `*_j` whose
forms `h_j(u, v) = Tr(u ∪ *_j v)` are positive definite Hermitian. -/
structure WeightedAlgebraDatum (V : Type u) [AddCommGroup V] [Module ℂ V] (d : ℕ) (w : ℝ) where
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
  /-- `h_j` is positive definite. -/
  h_pos : ∀ {j : ℕ} {u : V}, u ∈ G j → u ≠ 0 → 0 < (Tr (mul u (st j u))).re

namespace WeightedAlgebraDatum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ} {w : ℝ}
  (D : WeightedAlgebraDatum V d w)

/-- The form `h_j(u, v) = Tr(u ∪ *_j v)`. -/
def h (j : ℕ) (u v : V) : ℂ := D.Tr (D.mul u (D.st j v))

/-- `Θ_j = Θ|V^j`. -/
abbrev Θr (j : ℕ) : Module.End ℂ (D.G j) :=
  D.Θ.restrict (p := D.G j) (q := D.G j) fun _ hx => D.Θ_mem hx

/-- **The polarization identity of weight `w + j`** (first display of the proof of
`prop:weighted-algebra-obstruction`), from the derivation, trace and star laws. -/
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

/-- `h_j` as a positive definite Hermitian form on `V^j`. -/
def form (j : ℕ) : PosHermForm (D.G j) where
  toFun u v := D.h j u v
  add_left u u' v := by simp [h]
  smul_left c u v := by simp [h]
  conj_symm u v := D.h_conj u.2 v.2
  re_pos u hu := D.h_pos u.2 (by simpa using hu)

lemma form_P (j : ℕ) (u v : D.G j) :
    (D.form j).toFun (D.Θr j u) v + (D.form j).toFun u (D.Θr j v) =
      ((w + j : ℝ) : ℂ) * (D.form j).toFun u v :=
  D.polarization u.2 v.2

/-- Every eigenvalue of `Θ_j` has real part `(w + j)/2`. -/
theorem re_eq_of_hasEigenvalue {j : ℕ} {ρ : ℂ} (hρ : (D.Θr j).HasEigenvalue ρ) :
    ρ.re = (w + j) / 2 :=
  (D.form j).re_eq_half _ _ (D.form_P j) hρ

/-- `Θ_j` is diagonalizable: `V^j` is the sum of the eigenspaces of `Θ_j`. -/
theorem iSup_eigenspace (j : ℕ) : ⨆ ρ, (D.Θr j).eigenspace ρ = ⊤ := by
  have := (D.spectralCore j).iSup_eq_top
  simp_rw [(D.form j).maxGenEigenspace_eq_eigenspace _ _ (D.form_P j)] at this
  exact this

lemma hasEigenvalue_of_mem {j : ℕ} {u : V} (hu : u ∈ D.G j) (hu0 : u ≠ 0) {ρ : ℂ}
    (hρ : D.Θ u = ρ • u) : (D.Θr j).HasEigenvalue ρ :=
  Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨u, hu⟩)
    ⟨Module.End.mem_eigenspace_iff.mpr (Subtype.ext hρ), by simpa using hu0⟩

/-- For `w ≠ 0`, the product of two eigenvectors vanishes. -/
theorem mul_eigen_eq_zero (hw : w ≠ 0) {i k : ℕ} {u v : V} (hu : u ∈ D.G i) (hv : v ∈ D.G k)
    {ρ σ : ℂ} (hρ : D.Θ u = ρ • u) (hσ : D.Θ v = σ • v) : D.mul u v = 0 := by
  by_contra hne
  have hu0 : u ≠ 0 := by rintro rfl; simp at hne
  have hv0 : v ≠ 0 := by rintro rfl; simp at hne
  have hprod : D.Θ (D.mul u v) = (ρ + σ) • D.mul u v := by
    rw [D.Θ_mul, hρ, hσ, map_smul, LinearMap.smul_apply, map_smul, add_smul]
  have h1 := D.re_eq_of_hasEigenvalue (D.hasEigenvalue_of_mem hu hu0 hρ)
  have h2 := D.re_eq_of_hasEigenvalue (D.hasEigenvalue_of_mem hv hv0 hσ)
  have h3 := D.re_eq_of_hasEigenvalue (D.hasEigenvalue_of_mem (D.mul_mem hu hv) hne hprod)
  rw [Complex.add_re, h1, h2] at h3
  push_cast at h3
  exact hw (by linarith)

/-- **For `w ≠ 0` all products vanish** (proof of `prop:weighted-algebra-obstruction`). -/
theorem mul_eq_zero (hw : w ≠ 0) {i k : ℕ} {u v : V} (hu : u ∈ D.G i) (hv : v ∈ D.G k) :
    D.mul u v = 0 := by
  suffices H : ∀ x : D.G i, ∀ y : D.G k, D.mul x y = 0 from H ⟨u, hu⟩ ⟨v, hv⟩
  intro x
  have hx : x ∈ ⨆ ρ, (D.Θr i).eigenspace ρ := by rw [D.iSup_eigenspace]; trivial
  refine Submodule.iSup_induction (fun ρ => (D.Θr i).eigenspace ρ)
    (motive := fun x => ∀ y : D.G k, D.mul x y = 0) hx ?_ (by intro y; simp) ?_
  · intro ρ x hx y
    have hy : y ∈ ⨆ σ, (D.Θr k).eigenspace σ := by rw [D.iSup_eigenspace]; trivial
    refine Submodule.iSup_induction (fun σ => (D.Θr k).eigenspace σ)
      (motive := fun y => D.mul x y = 0) hy ?_ (by simp) ?_
    · intro σ y hy
      exact D.mul_eigen_eq_zero hw x.2 y.2
        (congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hx))
        (congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hy))
    · intro y y' hy hy'
      simp [hy, hy']
  · intro x x' hx hx' y
    simp [hx y, hx' y]

/-- **`prop:weighted-algebra-obstruction`, first claim.** If `w ≠ 0`, every `V^j` is zero. -/
theorem eq_bot (hw : w ≠ 0) (j : ℕ) : D.G j = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  by_contra hne
  have := D.h_pos hu hne
  rw [D.mul_eq_zero hw hu (D.st_mem hu)] at this
  simp at this

/-- **`prop:weighted-algebra-obstruction`, second claim.** If the algebra is nonzero and has a
unit in degree zero, then `w = 0`. Only the left unit law is used. -/
theorem eq_zero_of_unit (one : V) (hone : one ∈ D.G 0) (hl : ∀ x, D.mul one x = x)
    (hV : ∃ x : V, x ≠ 0) : w = 0 := by
  by_contra hw
  have h1 : one = 0 := by
    rw [D.eq_bot hw 0] at hone
    exact (Submodule.mem_bot ℂ).mp hone
  obtain ⟨x, hx⟩ := hV
  exact hx (by rw [← hl x, h1, map_zero, LinearMap.zero_apply])


/-! ### Nonvacuity -/
/-- **Nonvacuity of `WeightedAlgebraDatum` with `w = 0`.** The algebra `ℂ` in degree `0`
(`d = 0`), with `Θ = 0`, `Tr = id` and `* = conj`; `h_0(u, v) = u v̄`. -/
noncomputable def trivialModel : WeightedAlgebraDatum ℂ 0 0 where
  G j := if j = 0 then ⊤ else ⊥
  vanish j hj := by simp [show j ≠ 0 by omega]
  mul := LinearMap.mul ℂ ℂ
  mul_mem {i k x y} hx hy := by
    by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> simp_all
  Θ := 0
  Θ_mem := by intro j x hx; simp
  Θ_mul := by simp
  spectralCore j := Spectral.spectralCore_of_finiteDimensional _
  Tr := LinearMap.id
  Tr_Θ := by simp
  st _ := (starLinearEquiv ℂ (A := ℂ)).toLinearMap
  st_mem {j x} hx := by
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj] at hx; subst hx; simp
  Θ_st {j x} hx := by
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj] at hx; subst hx; simp
  h_conj := by intro j u v _ _; simp [mul_comm]
  h_pos := by
    intro j u _ hu
    simp only [LinearMap.id_apply, LinearMap.mul_apply', LinearEquiv.coe_coe, starLinearEquiv_apply]
    rw [Complex.star_def, Complex.mul_conj]
    exact_mod_cast Complex.normSq_pos.mpr hu

/-- The trivial model is nonzero and unital, so it is not excluded by `eq_zero_of_unit`. -/
theorem trivialModel_nontrivial : trivialModel.G 0 ≠ ⊥ ∧ (1 : ℂ) ∈ trivialModel.G 0 ∧
    ∀ x : ℂ, trivialModel.mul 1 x = x := by
  refine ⟨by simp [trivialModel], by simp [trivialModel], fun x => by simp [trivialModel]⟩
end WeightedAlgebraDatum

end WeilRH
