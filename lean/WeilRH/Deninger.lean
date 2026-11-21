/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.FlowCategory
import WeilRH.Unit
import WeilRH.TrivialModelGraded

/-!
# Deninger structures, polarizations and Deninger modules

Source: the manuscript `latex/notes.tex`, `def:deninger-structure`, `def:polarizable`,
`def:deninger-module`, with `def:weil-cohomology` (the Deninger axioms AW1, AW3, AW4 for one Weil
datum), `def:graded-realization` (b) and `prop:polarization-identity`.

A Deninger structure of dimension `d` with unit `U` is a graded algebra of spectral cores in
degrees `0, …, 2d` satisfying AW1 and AW3: an associative, graded-commutative, unital product with
`Θ` a derivation, `V^0 ≅ U` as unital algebras with flow, `V^{2d} ≅ U(-d)`, a flow-equivariant
trace into `ℂ(-d)`, and duality pairings perfect on generalized eigenspaces. A polarization is a
family of stars satisfying AW4; being polarizable is a property.

## Encoding

As in `WeilRH.WeightedAlgebraDatum`, the graded pieces `V^j` are submodules `G j` of one space `V`,
zero above `2d`. The unit `U` is a commutative `ℂ`-algebra with a generator `Θ_U`
(`WeilRH.Unit.arith` on `ℂ` for `𝟙`, `WeilRH.Unit.periodicTheta q` on `WeilRH.Unit.Periodic` for
`𝟙_q`); `U(-d)` is `U` with generator `WeilRH.Unit.twist Θ_U d = Θ_U + d`.

## Main results

* `WeilRH.DeningerStructure` (`def:deninger-structure` (a)); `DeningerStructure.Hom`, `Hom.id`,
  `Hom.comp` (`def:deninger-structure` (b)).
* `DeningerStructure.nondeg_right`: two-sided nondegeneracy of the block pairings.
* `DeningerStructure.Polarization`, `DeningerStructure.Polarizable` (`def:polarizable`).
* `DeningerStructure.Polarization.toWeightedAlgebraDatum`: a polarized Deninger structure is a
  `WeightedAlgebraDatum V d 0`.
* `DeningerStructure.Polarization.infPol`, `re_eq_of_hasEigenvalue`, `iSup_eigenspace`: each
  `(V^j, Θ_j)` is a spectral core with a positive infinitesimal polarization of weight `j`, so a
  polarized Deninger structure is a polarized graded spectral realization of type `(d, 0)` of any
  function whose divisor it realizes (`def:graded-realization` (b)), with eigenvalues on
  `Re s = j/2` and `Θ_j` diagonalizable.
* `WeilRH.WeightedAlgebraDatum.nondeg`: positivity alone forces the AW3 block pairings to be
  nondegenerate when `w = 0`.
* `WeilRH.DeningerModule` (`def:deninger-module` (a)) and `DeningerModule.Hom`
  (`def:deninger-module` (b)).
* `WeilRH.TrivialModel.deningerStructure`, `deningerPolarization`, `polarizable`: the graded
  trivial model of `def:trivial-model` is a polarizable Deninger structure of dimension `1` with
  unit `𝟙`, so the definitions are not vacuous.

## Fidelity

* AW3 perfectness is encoded as nondegeneracy of `Tr(u ∪ v)` on `V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d-ρ}`
  (`nondeg`); with graded commutativity this is two-sided (`nondeg_right`), and since generalized
  eigenspaces are finite-dimensional in a spectral core, two-sided nondegeneracy is equivalent to
  perfectness. That last equivalence is not formalized here.
* The divisor clause of `def:graded-realization` (a), i.e. AW2, refers to a meromorphic function
  and is not part of the structure, exactly as in the notes; the bridge supplies clause (b).
* `def:deninger-theory` (the functor on `\Schbar^{proj}` with its axioms), the compactified
  schemes `def:compactified-schemes`, and the finite-field calibration
  (`prop:finite-field-calibration`, a consequence in the notes, not an axiom) are not formalized.
* `Den_d(U)` is represented by the type `DeningerStructure V d U Θ_U` for fixed `V` with
  `Hom.id`/`Hom.comp`; no bundled `CategoryTheory.Category` instance is built.
-/

open Module Complex ComplexConjugate

namespace WeilRH

universe u v

/-- **`def:deninger-structure` (a).** A Deninger structure of dimension `d` with unit `(U, Θ_U)`:
graded spectral cores `V^j`, `0 ≤ j ≤ 2d`, with a product, unit and trace satisfying AW1 and AW3. -/
structure DeningerStructure (V : Type u) [AddCommGroup V] [Module ℂ V] (d : ℕ)
    (U : Type v) [CommRing U] [Algebra ℂ U] (ΘU : Module.End ℂ U) where
  /-- The graded piece `V^j`. -/
  G : ℕ → Submodule ℂ V
  /-- `V^j = 0` for `j > 2d`. -/
  vanish : ∀ j, 2 * d < j → G j = ⊥
  /-- The cup product. -/
  mul : V →ₗ[ℂ] V →ₗ[ℂ] V
  mul_mem : ∀ {i k : ℕ} {x y : V}, x ∈ G i → y ∈ G k → mul x y ∈ G (i + k)
  /-- AW1: associativity. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- AW1: graded commutativity. -/
  mul_comm_graded : ∀ {i k : ℕ} {x y : V}, x ∈ G i → y ∈ G k →
    mul y x = ((-1 : ℂ) ^ (i * k)) • mul x y
  /-- AW1: the unit `1 ∈ V^0`. -/
  one : V
  one_mem : one ∈ G 0
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  /-- The generator. -/
  Θ : Module.End ℂ V
  Θ_mem : ∀ {j : ℕ} {x : V}, x ∈ G j → Θ x ∈ G j
  /-- AW1: `Θ` is a derivation. -/
  Θ_mul : ∀ x y, Θ (mul x y) = mul (Θ x) y + mul x (Θ y)
  /-- Each `(V^j, Θ_j)` is a spectral core. -/
  spectralCore : ∀ j, Spectral.SpectralCore (Θ.restrict (p := G j) (q := G j) fun _ hx => Θ_mem hx)
  /-- AW1: `V^0 ≅ U`. -/
  e0 : G 0 ≃ₗ[ℂ] U
  e0_one : e0 ⟨one, one_mem⟩ = 1
  e0_mul : ∀ x y : G 0, e0 ⟨mul x y, by simpa using mul_mem x.2 y.2⟩ = e0 x * e0 y
  e0_Θ : ∀ x : G 0, e0 ⟨Θ x, Θ_mem x.2⟩ = ΘU (e0 x)
  /-- AW1: `V^{2d} ≅ U(-d)`. -/
  etop : G (2 * d) ≃ₗ[ℂ] U
  etop_Θ : ∀ x : G (2 * d), etop ⟨Θ x, Θ_mem x.2⟩ = Unit.twist ΘU d (etop x)
  /-- AW3: the trace on `V^{2d}`. -/
  Tr : V →ₗ[ℂ] ℂ
  /-- AW3: the trace is flow-equivariant into `ℂ(-d)`. -/
  Tr_Θ : ∀ x ∈ G (2 * d), Tr (Θ x) = (d : ℂ) * Tr x
  /-- AW3: `B_j(u, v) = Tr(u ∪ v)` is nondegenerate on `V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d-ρ}`. -/
  nondeg : ∀ {j : ℕ} {ρ : ℂ} {u : V}, u ∈ G j → u ∈ Θ.maxGenEigenspace ρ → u ≠ 0 →
    ∃ v ∈ G (2 * d - j), v ∈ Θ.maxGenEigenspace ((d : ℂ) - ρ) ∧ Tr (mul u v) ≠ 0

namespace DeningerStructure

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  {U : Type v} [CommRing U] [Algebra ℂ U] {ΘU : Module.End ℂ U}
  (D : DeningerStructure V d U ΘU)

/-- Right nondegeneracy of the block pairings, from `nondeg` and graded commutativity. -/
theorem nondeg_right {j : ℕ} {σ : ℂ} {v : V} (hv : v ∈ D.G j)
    (hσ : v ∈ D.Θ.maxGenEigenspace σ) (hv0 : v ≠ 0) :
    ∃ u ∈ D.G (2 * d - j), u ∈ D.Θ.maxGenEigenspace ((d : ℂ) - σ) ∧ D.Tr (D.mul u v) ≠ 0 := by
  obtain ⟨u, hu, hρ, hne⟩ := D.nondeg hv hσ hv0
  refine ⟨u, hu, hρ, fun h => hne ?_⟩
  rw [D.mul_comm_graded hv hu, map_smul, smul_eq_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h

/-- **`def:deninger-structure` (b).** A morphism: a graded unital algebra homomorphism commuting
with the generators. Traces need not be preserved. -/
structure Hom {V' : Type u} [AddCommGroup V'] [Module ℂ V'] (D' : DeningerStructure V' d U ΘU) where
  /-- The linear map. -/
  toLin : V →ₗ[ℂ] V'
  map_G : ∀ {j : ℕ} {x : V}, x ∈ D.G j → toLin x ∈ D'.G j
  map_mul : ∀ x y, toLin (D.mul x y) = D'.mul (toLin x) (toLin y)
  map_one : toLin D.one = D'.one
  map_Θ : ∀ x, toLin (D.Θ x) = D'.Θ (toLin x)

/-- The identity morphism. -/
def Hom.id : D.Hom D where
  toLin := LinearMap.id
  map_G hx := hx
  map_mul _ _ := rfl
  map_one := rfl
  map_Θ _ := rfl

/-- Composition of morphisms. -/
def Hom.comp {V' V'' : Type u} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V''] [Module ℂ V'']
    {D' : DeningerStructure V' d U ΘU} {D'' : DeningerStructure V'' d U ΘU}
    (g : D'.Hom D'') (f : D.Hom D') : D.Hom D'' where
  toLin := g.toLin ∘ₗ f.toLin
  map_G hx := g.map_G (f.map_G hx)
  map_mul x y := by simp [f.map_mul, g.map_mul]
  map_one := by simp [f.map_one, g.map_one]
  map_Θ x := by simp [f.map_Θ, g.map_Θ]

/-- **`def:polarizable` (a).** A polarization: antilinear stars `*_j : V^j → V^{2d-j}` such that
`(V^•, Θ, ∪, Tr, *)` satisfies AW4 (star law and positive definite Hermitian forms
`h_j(u, v) = Tr(u ∪ *_j v)`). -/
structure Polarization where
  /-- The star `*_j`. -/
  st : ℕ → V →ₗ⋆[ℂ] V
  st_mem : ∀ {j : ℕ} {x : V}, x ∈ D.G j → st j x ∈ D.G (2 * d - j)
  /-- `Θ_{2d-j} *_j = *_j Θ_j + (d - j) *_j`. -/
  Θ_st : ∀ {j : ℕ} {x : V}, x ∈ D.G j → D.Θ (st j x) = st j (D.Θ x) + ((d : ℂ) - j) • st j x
  /-- `h_j` is Hermitian. -/
  h_conj : ∀ {j : ℕ} {u v : V}, u ∈ D.G j → v ∈ D.G j →
    conj (D.Tr (D.mul u (st j v))) = D.Tr (D.mul v (st j u))
  /-- `h_j` is positive definite. -/
  h_pos : ∀ {j : ℕ} {u : V}, u ∈ D.G j → u ≠ 0 → 0 < (D.Tr (D.mul u (st j u))).re

/-- **`def:polarizable` (b).** `D` is polarizable if it has a polarization. -/
def Polarizable : Prop := Nonempty D.Polarization

namespace Polarization

variable {D} (P : D.Polarization)

/-- **Bridge.** A polarized Deninger structure is a graded positive Weil datum of type `(d, 0)`
(`WeightedAlgebraDatum V d 0`). -/
def toWeightedAlgebraDatum : WeightedAlgebraDatum V d 0 where
  G := D.G
  vanish := D.vanish
  mul := D.mul
  mul_mem := D.mul_mem
  Θ := D.Θ
  Θ_mem := D.Θ_mem
  Θ_mul := D.Θ_mul
  spectralCore := D.spectralCore
  Tr := D.Tr
  Tr_Θ x hx := by rw [D.Tr_Θ x hx]; simp
  st := P.st
  st_mem := P.st_mem
  Θ_st := P.Θ_st
  h_conj := P.h_conj
  h_pos := P.h_pos

/-- **`def:graded-realization` (b) for a polarized Deninger structure** (with
`prop:polarization-identity`): `h_j` is a positive infinitesimal polarization of weight `j` on
`(V^j, Θ_j)`. -/
theorem infPol (j : ℕ) (u v : D.G j) :
    (P.toWeightedAlgebraDatum.form j).toFun (P.toWeightedAlgebraDatum.Θr j u) v +
      (P.toWeightedAlgebraDatum.form j).toFun u (P.toWeightedAlgebraDatum.Θr j v) =
      ((j : ℝ) : ℂ) * (P.toWeightedAlgebraDatum.form j).toFun u v := by
  have := P.toWeightedAlgebraDatum.form_P j u v
  simpa using this

/-- **Purity.** Every eigenvalue of `Θ_j` on a polarizable Deninger structure has real part
`j/2`. -/
theorem re_eq_of_hasEigenvalue {j : ℕ} {ρ : ℂ}
    (hρ : (P.toWeightedAlgebraDatum.Θr j).HasEigenvalue ρ) : ρ.re = j / 2 := by
  have := P.toWeightedAlgebraDatum.re_eq_of_hasEigenvalue hρ
  simpa using this

/-- **Semisimplicity.** `Θ_j` is diagonalizable on a polarizable Deninger structure. -/
theorem iSup_eigenspace (j : ℕ) : ⨆ ρ, (P.toWeightedAlgebraDatum.Θr j).eigenspace ρ = ⊤ :=
  P.toWeightedAlgebraDatum.iSup_eigenspace j

end Polarization

end DeningerStructure

/-! ### Positivity forces the AW3 nondegeneracy -/

namespace WeightedAlgebraDatum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ} (D : WeightedAlgebraDatum V d 0)

lemma restrict_sub_smul_pow (j : ℕ) (ρ : ℂ) (k : ℕ) (x : D.G j) :
    ((((D.Θr j) - ρ • 1) ^ k) x : V) = ((D.Θ - ρ • 1) ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    simp [Θr]

/-- In a positive datum of weight `0`, a generalized `ρ`-eigenvector in `V^j` is an eigenvector. -/
lemma eigen_of_mem {j : ℕ} {ρ : ℂ} {u : V} (hu : u ∈ D.G j) (hρ : u ∈ D.Θ.maxGenEigenspace ρ) :
    D.Θ u = ρ • u := by
  have hmem : (⟨u, hu⟩ : D.G j) ∈ (D.Θr j).maxGenEigenspace ρ := by
    rw [Module.End.mem_maxGenEigenspace] at hρ ⊢
    obtain ⟨k, hk⟩ := hρ
    exact ⟨k, Subtype.ext (by rw [restrict_sub_smul_pow, hk]; rfl)⟩
  rw [(D.form j).maxGenEigenspace_eq_eigenspace _ _ (D.form_P j)] at hmem
  have := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hmem)
  simpa [Θr] using this

/-- **AW4 forces AW3 nondegeneracy (weight `0`).** For `u ≠ 0` in `V^j_{Θ∼ρ}`, `v = *_j u` lies in
`V^{2d-j}_{Θ∼d-ρ}` and `Tr(u ∪ v) = h_j(u, u) ≠ 0`. -/
theorem nondeg {j : ℕ} {ρ : ℂ} {u : V} (hu : u ∈ D.G j) (hρ : u ∈ D.Θ.maxGenEigenspace ρ)
    (hu0 : u ≠ 0) :
    ∃ v ∈ D.G (2 * d - j), v ∈ D.Θ.maxGenEigenspace ((d : ℂ) - ρ) ∧ D.Tr (D.mul u v) ≠ 0 := by
  have heig := D.eigen_of_mem hu hρ
  have hre : ρ.re = j / 2 := by
    have := D.re_eq_of_hasEigenvalue (D.hasEigenvalue_of_mem hu hu0 heig)
    simpa using this
  refine ⟨D.st j u, D.st_mem hu, ?_, fun h => ?_⟩
  · apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff, D.Θ_st hu, heig, LinearMap.map_smulₛₗ, ← add_smul]
    congr 1
    apply Complex.ext <;> simp [hre]
    ring
  · have := D.h_pos hu hu0
    rw [h] at this
    simp at this

end WeightedAlgebraDatum

/-! ### Deninger modules -/

/-- **`def:deninger-module` (a).** A Deninger module over `D`: graded spectral cores `M^j`,
`j ∈ ℤ`, zero for `|j|` large, with an associative graded action of the algebra `V^•` for which
`Θ` is a derivation. -/
structure DeningerModule {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    {U : Type v} [CommRing U] [Algebra ℂ U] {ΘU : Module.End ℂ U}
    (D : DeningerStructure V d U ΘU) (M : Type u) [AddCommGroup M] [Module ℂ M] where
  /-- The graded piece `M^j`. -/
  GM : ℤ → Submodule ℂ M
  /-- `M^j = 0` for `|j|` large. -/
  bounded : ∃ N : ℕ, ∀ j : ℤ, (N : ℤ) < |j| → GM j = ⊥
  /-- The action `V × M → M`. -/
  act : V →ₗ[ℂ] M →ₗ[ℂ] M
  act_mem : ∀ {i : ℕ} {k : ℤ} {x : V} {m : M}, x ∈ D.G i → m ∈ GM k → act x m ∈ GM (i + k)
  act_assoc : ∀ x y m, act (D.mul x y) m = act x (act y m)
  /-- The generator. -/
  ΘM : Module.End ℂ M
  ΘM_mem : ∀ {j : ℤ} {m : M}, m ∈ GM j → ΘM m ∈ GM j
  /-- `Θ` is a derivation for the action. -/
  ΘM_act : ∀ x m, ΘM (act x m) = act (D.Θ x) m + act x (ΘM m)
  /-- Each `(M^j, Θ_j)` is a spectral core. -/
  spectralCore : ∀ j,
    Spectral.SpectralCore (ΘM.restrict (p := GM j) (q := GM j) fun _ hm => ΘM_mem hm)

/-- **`def:deninger-module` (b).** A morphism of Deninger modules: a graded `V^•`-linear map
commuting with the generators. -/
structure DeningerModule.Hom {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    {U : Type v} [CommRing U] [Algebra ℂ U] {ΘU : Module.End ℂ U}
    {D : DeningerStructure V d U ΘU} {M M' : Type u} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup M'] [Module ℂ M'] (A : DeningerModule D M) (A' : DeningerModule D M') where
  /-- The linear map. -/
  toLin : M →ₗ[ℂ] M'
  map_G : ∀ {j : ℤ} {m : M}, m ∈ A.GM j → toLin m ∈ A'.GM j
  map_act : ∀ x m, toLin (A.act x m) = A'.act x (toLin m)
  map_Θ : ∀ m, toLin (A.ΘM m) = A'.ΘM (toLin m)

/-! ### Non-vacuity: the trivial model -/

namespace TrivialModel

open WeilRH.Spectral

variable {ι : Type} (ρ : ι → ℂ) [DecidableEq ι] [Fintype ι] (hline : ∀ p, (ρ p).re = 1 / 2)

omit [DecidableEq ι] [Fintype ι] in
lemma mem_G_cases {j : ℕ} {x : Tot ι} (hx : x ∈ G j) :
    (j = 0 ∧ x.2.1 = 0 ∧ x.2.2 = 0) ∨ (j = 1 ∧ x.1 = 0 ∧ x.2.2 = 0) ∨
      (j = 2 ∧ x.1 = 0 ∧ x.2.1 = 0) ∨ x = 0 := by
  match j, hx with
  | 0, hx => exact Or.inl ⟨rfl, mem_G0.mp hx⟩
  | 1, hx => exact Or.inr (Or.inl ⟨rfl, mem_G1.mp hx⟩)
  | 2, hx => exact Or.inr (Or.inr (Or.inl ⟨rfl, mem_G2.mp hx⟩))
  | n + 3, hx => exact Or.inr (Or.inr (Or.inr (mem_G3.mp hx)))

/-- **Non-vacuity of `def:deninger-structure`.** The graded trivial model of `def:trivial-model`,
for a finite family on `Re s = 1/2`, is a Deninger structure of dimension `1` with unit `𝟙`. -/
noncomputable def deningerStructure : DeningerStructure (Tot ι) 1 ℂ Unit.arith where
  G := G
  vanish := (gradedModel ρ hline).vanish
  mul := mulL
  mul_mem := (gradedModel ρ hline).mul_mem
  mul_assoc x y z := mul_assoc' x y z
  mul_comm_graded {i k x y} hx hy := by
    simp only [mulL_apply]
    rw [WeilRH.TrivialModel.mul_comm_graded x y]
    have hx' := mem_G_cases hx
    have hy' := mem_G_cases hy
    obtain ⟨a, u, c⟩ := x; obtain ⟨b, v, e⟩ := y
    simp only [Prod.mk_eq_zero] at hx' hy'
    rcases hx' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hy' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [mul]
  one := one
  one_mem := by simp [mem_G0, one]
  one_mul := one_mul'
  mul_one := mul_one'
  Θ := thetaL ρ
  Θ_mem := (gradedModel ρ hline).Θ_mem
  Θ_mul := (gradedModel ρ hline).Θ_mul
  spectralCore := (gradedModel ρ hline).spectralCore
  e0 := deg0Equiv
  e0_one := rfl
  e0_mul _ _ := rfl
  e0_Θ _ := rfl
  etop := deg2Equiv
  etop_Θ x := by
    obtain ⟨⟨a, u, c⟩, hx⟩ := x
    rw [show 2 * 1 = 2 from rfl, mem_G2] at hx; obtain ⟨rfl, rfl⟩ := hx
    simp [Unit.twist, Unit.arith, deg2Equiv, thetaTot]
  Tr := trT
  Tr_Θ x hx := by
    obtain ⟨a, u, c⟩ := x
    rw [show 2 * 1 = 2 from rfl, mem_G2] at hx; obtain ⟨rfl, rfl⟩ := hx
    simp [trT, thetaTot]
  nondeg hu hρ hu0 := (gradedModel ρ hline).nondeg hu hρ hu0

/-- **Non-vacuity of `def:polarizable`.** The trivial model carries the polarization
`*_0, *_1, *_2` of `prop:trivial-model` (ii). -/
noncomputable def deningerPolarization : (deningerStructure ρ hline).Polarization where
  st := st
  st_mem := (gradedModel ρ hline).st_mem
  Θ_st := (gradedModel ρ hline).Θ_st
  h_conj := (gradedModel ρ hline).h_conj
  h_pos := (gradedModel ρ hline).h_pos

theorem polarizable : (deningerStructure ρ hline).Polarizable :=
  ⟨deningerPolarization ρ hline⟩

/-- The trivial Deninger structure is nonzero. -/
theorem deningerStructure_nontrivial : (one : Tot ι) ∈ (deningerStructure ρ hline).G 0 ∧
    (one : Tot ι) ≠ 0 :=
  gradedModel_nontrivial ρ hline

end TrivialModel

end WeilRH
