import Mathlib
import WeilRH.WeilArakelov

/-!
# The degree-one Deligne datum of `X̄_K` (FM path, step E3, round 55)

Round 55 of `lean/ROADMAP-arakelov.md`, on the Flach–Morin path (decision D8). Source:
Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020),
§3.1, p. 523, checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:
`RΓ_c(X, ℝ(n))` is the mapping fibre of the regulator `RΓ(X, ℝ(n)) → RΓ_D(X/ℝ, ℝ(n))`, with
`RΓ_D(X/ℝ, ℝ(n)) := RΓ(G_ℝ, X(ℂ), ℝ(n)_D)` and `ℝ(n)_D = (2iπ)^n ℝ → Ω⁰ → ⋯ → Ω^{n-1}`.

For `X = Spec 𝒪_K` and `n = 1` the standard values are
`H¹(X, ℝ(1)) = 𝒪_K^× ⊗ ℝ`, `H¹_D(X/ℝ, ℝ(1)) = (ℂ/2πiℝ)^{Hom(K,ℂ)})^{G_ℝ} ≅ ℝ^{InfinitePlace K}`,
and all other groups in the sequence vanish, so the fibre has `H¹_c = ker(reg) = 0` and
`H²_c = coker(reg) ≅ ℝ`. This file builds that sequence as a `DeligneDatum`.

## Main results

* `unitsR K := ℝ ⊗[ℤ] Λ_K`, with `Λ_K = unitLattice K` the image of the units in Mathlib's log
  space (Mathlib's `logEmbeddingEquiv : 𝒪_K^× ⧸ μ(K) ≃ Λ_K`), and `logR K : unitsR K →ₗ[ℝ]
  logSpace K`, the `ℝ`-linear extension of the inclusion; `unitClass K u ∈ Λ_K` is the class of a
  unit.
* `logR_eq_equiv`, `logR_bijective`: `logR` is an isomorphism (Dirichlet's unit theorem: the unit
  lattice is a full-rank `ℤ`-lattice, so a `ℤ`-basis of it is an `ℝ`-basis of `logSpace K`).
* `hyperplane K`, `regR K := hyperplane K ∘ logR K : unitsR K →ₗ[ℝ] (InfinitePlace K → ℝ)` and
  `regR_tmul`: on `1 ⊗ unitClass u` it is round 54's `regulatorMap K u`.
* `regR_injective`: the regulator `⊗ ℝ` is injective; `range_regR`: its image is the sum-zero
  hyperplane `ker (∑_w)`; `sumMap_surjective`: the cokernel map `∑_w` is onto `ℝ`.
* `degreeOne K : DeligneDatum ℝ …`: the genuine (non-degenerate) Deligne datum, concentrated in
  degrees `1` (motivic and Deligne) and `2` (`H²_c`), with `degreeOne_Hc_two : Hc 2 ≃ ℝ` and
  `degreeOne_Del_one_nontrivial`.

## Fidelity

* **Computed honestly:** the regulator `⊗ ℝ`, its injectivity, its image, and hence `H¹_c = 0` and
  `H²_c ≅ ℝ` in the sequence (`degreeOne`'s exactness is proved, not assumed).
* **Modelled by definition (standard, not derived here):**
  - `H¹(Spec 𝒪_K, ℝ(1))` is taken to be `Λ_K ⊗ ℝ ≅ (𝒪_K^×/μ(K)) ⊗ ℝ`. Bloch's cycle complex is not
    in Mathlib; tensoring with `ℝ` kills the finite group `μ(K)`, so this is `𝒪_K^× ⊗ ℝ`, but that
    isomorphism is not formalized.
  - The file sets `backward.isDefEq.respectTransparency.types false`, as Mathlib's
    `DirichletTheorem.lean` does, so that the normed and `Pi` module structures on `logSpace K`
    unify.
  - `H¹_D(X/ℝ, ℝ(1))` is taken to be `ℝ^{InfinitePlace K}`. **Normalization:** the Deligne complex
    gives `u ↦ (log|σ(u)|)` on `(ℂ/2πiℝ)^{Hom(K,ℂ)}`, whose `G_ℝ`-invariants are identified with
    `ℝ^{InfinitePlace K}` by evaluating at one embedding per place. Round 54's `regulatorMap` has
    entries `mult w · log w(u)`, so it equals FM's regulator composed with the invertible diagonal
    rescaling by `mult w ∈ {1, 2}`. Kernels, images and cokernel dimensions are unaffected.
  - All other groups (`H⁰`, `H²` motivic, `H⁰_D`, `H²_D`, …) are set to `0`, as for `X = Spec 𝒪_K`,
    `n = 1` (`Pic(𝒪_K) ⊗ ℝ = 0`, and `X(ℂ)` is a finite set). The map `H^i_c → H^i` is `0`.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace WeilRH.Arakelov

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem TensorProduct Module
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-! ## `𝒪_K^× ⊗ ℝ` and the regulator -/


/-- `𝒪_K^× ⊗ ℝ`, modelled as `ℝ ⊗[ℤ] Λ_K` with `Λ_K = unitLattice K` the image of the units in the
log space. Mathlib's `logEmbeddingEquiv` identifies `Λ_K ≃ 𝒪_K^× ⧸ μ(K)`, and tensoring with `ℝ`
kills `μ(K)`. -/
abbrev unitsR : Type _ := ℝ ⊗[ℤ] unitLattice K

/-- The `ℝ`-linear extension of the inclusion `Λ_K ⊂ logSpace K`, i.e. the logarithmic embedding
`⊗ ℝ`. -/
noncomputable def logR : unitsR K →ₗ[ℝ] logSpace K :=
  (unitLattice K).subtype.liftBaseChange ℝ

@[simp] theorem logR_tmul (c : ℝ) (y : unitLattice K) :
    logR K (c ⊗ₜ y) = c • (y : logSpace K) := by
  simp [logR]

/-- The class of a unit `u` in `Λ_K`. -/
noncomputable def unitClass (x : (𝓞 K)ˣ) : unitLattice K :=
  ⟨logEmbedding K (Additive.ofMul x), Submodule.mem_map_of_mem trivial⟩

@[simp] theorem unitClass_coe (x : (𝓞 K)ˣ) :
    (unitClass K x : logSpace K) = logEmbedding K (Additive.ofMul x) := rfl

/-- The `ℝ`-basis of `unitsR K` coming from the `ℤ`-basis of the unit lattice. -/
noncomputable def basisR : Basis (Fin (rank K)) ℝ (unitsR K) :=
  (basisUnitLattice K).baseChange ℝ

/-- The `ℝ`-basis of `logSpace K` given by the `ℤ`-basis of the unit lattice (it is a full-rank
lattice: `instZLattice_unitLattice`). -/
noncomputable def basisLog : Basis (Fin (rank K)) ℝ (logSpace K) :=
  (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)

theorem logR_basisR (i : Fin (rank K)) : logR K (basisR K i) = basisLog K i := by
  rw [basisR, Basis.baseChange_apply, basisLog, Basis.ofZLatticeBasis_apply, logR_tmul, one_smul]

/-- **Dirichlet.** `logR` is the isomorphism sending `basisR` to `basisLog`. -/
theorem logR_eq_equiv :
    logR K = ((basisR K).equiv (basisLog K) (Equiv.refl _)).toLinearMap := by
  refine (basisR K).ext fun i => ?_
  rw [logR_basisR, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]

theorem logR_bijective : Function.Bijective (logR K) := by
  rw [logR_eq_equiv]; exact LinearEquiv.bijective _

/-! ## From the log space to the sum-zero hyperplane -/

/-- `ℝ^{w ≠ w₀} → ℝ^{InfinitePlace K}`, completing the `w₀` coordinate so that the sum is `0`. -/
noncomputable def hyperplane : logSpace K →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun y w := if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩
  map_add' y z := by
    ext w; by_cases h : w = w₀ <;> simp [h, Finset.sum_add_distrib]; ring
  map_smul' c y := by
    ext w; by_cases h : w = w₀ <;> simp [h, Finset.mul_sum]

/-- The sum map `ℝ^{InfinitePlace K} → ℝ`. -/
noncomputable def sumMap : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ w, f w
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

@[simp] theorem sumMap_apply (f : InfinitePlace K → ℝ) : sumMap K f = ∑ w, f w := rfl

theorem hyperplane_injective : Function.Injective (hyperplane K) := by
  intro y z h
  funext v
  have := congr_fun h v.1
  simpa [hyperplane, v.2] using this

theorem sumMap_hyperplane (y : logSpace K) : sumMap K (hyperplane K y) = 0 := by
  classical
  rw [sumMap_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have h : ∀ x : {w : InfinitePlace K // w ≠ w₀}, hyperplane K y x = y x := fun x => by
    simp [hyperplane, x.2]
  simp only [h]
  simp [hyperplane]

theorem range_hyperplane : LinearMap.range (hyperplane K) = LinearMap.ker (sumMap K) := by
  classical
  ext f
  constructor
  · rintro ⟨y, rfl⟩; exact sumMap_hyperplane K y
  · intro hf
    refine ⟨fun v => f v.1, ?_⟩
    funext w
    by_cases h : w = w₀
    · subst h
      have hs := hf
      rw [LinearMap.mem_ker, sumMap_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hs
      simp only [hyperplane, LinearMap.coe_mk, AddHom.coe_mk, dite_true]
      linarith
    · simp [hyperplane, h]

theorem sumMap_surjective : Function.Surjective (sumMap K) := by
  classical
  intro c
  refine ⟨Pi.single w₀ c, ?_⟩
  simp

/-! ## The regulator `⊗ ℝ` -/

/-- The regulator `𝒪_K^× ⊗ ℝ → ℝ^{InfinitePlace K}` (degree one, `n = 1`). -/
noncomputable def regR : unitsR K →ₗ[ℝ] (InfinitePlace K → ℝ) := hyperplane K ∘ₗ logR K

/-- On `1 ⊗ [u]` the regulator `⊗ ℝ` is round 54's `regulatorMap`. -/
theorem regR_tmul (x : (𝓞 K)ˣ) :
    regR K (1 ⊗ₜ unitClass K x) = regulatorMap K (Additive.ofMul x) := by
  funext w
  rw [regR, LinearMap.comp_apply, logR_tmul, one_smul]
  by_cases h : w = w₀
  · subst h
    simp only [hyperplane, LinearMap.coe_mk, AddHom.coe_mk, dite_true, regulatorMap_apply,
      unitClass_coe]
    rw [sum_logEmbedding_component]; ring
  · simp [hyperplane, h]

/-- **The regulator `⊗ ℝ` is injective** (so `H¹_c = 0`). -/
theorem regR_injective : Function.Injective (regR K) :=
  (hyperplane_injective K).comp (logR_bijective K).1

/-- **The image of the regulator `⊗ ℝ` is the sum-zero hyperplane.** -/
theorem range_regR : LinearMap.range (regR K) = LinearMap.ker (sumMap K) := by
  rw [regR, LinearMap.range_comp, LinearMap.range_eq_top.mpr (logR_bijective K).2,
    Submodule.map_top, range_hyperplane]

/-! ## The degree-one Deligne datum -/

/-- The submodule `M` placed in degree `k` (and `0` elsewhere). -/
def degSub (M : Type*) [AddCommGroup M] [Module ℝ M] (k i : ℤ) : Submodule ℝ M :=
  if i = k then ⊤ else ⊥

theorem degSub_self (M : Type*) [AddCommGroup M] [Module ℝ M] (k : ℤ) : degSub M k k = ⊤ := by
  simp [degSub]

theorem eq_zero_of_mem_degSub {M : Type*} [AddCommGroup M] [Module ℝ M] {k i : ℤ} (h : i ≠ k)
    {x : M} (hx : x ∈ degSub M k i) : x = 0 := by
  simpa [degSub, h] using hx

theorem mem_degSub_self {M : Type*} [AddCommGroup M] [Module ℝ M] (k : ℤ) (x : M) :
    x ∈ degSub M k k := by
  simp [degSub]

/-- Restrict a linear map `f : M → N` to `degSub M k i → degSub N l j` when `i = k ↔ j = l`. -/
def degMap {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (f : M →ₗ[ℝ] N) (k l i j : ℤ) (hij : i = k → j = l) :
    degSub M k i →ₗ[ℝ] degSub N l j :=
  f.restrict fun x hx => by
    by_cases hi : i = k
    · rw [hij hi]; exact mem_degSub_self l _
    · rw [eq_zero_of_mem_degSub hi hx, map_zero]; exact zero_mem _

@[simp] theorem degMap_apply {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (f : M →ₗ[ℝ] N) (k l i j : ℤ) (hij : i = k → j = l) (x : degSub M k i) :
    (degMap f k l i j hij x : N) = f x := rfl

/-- **The degree-one Deligne datum of `X̄_K` (FM §3.1, `n = 1`).** `H¹ = 𝒪_K^× ⊗ ℝ`,
`H¹_D = ℝ^{InfinitePlace K}`, the regulator `regR`, `H²_c = ℝ` with connecting map `∑_w`; all
other groups vanish. Exactness is proved from Dirichlet's unit theorem. -/
noncomputable def degreeOne :
    DeligneDatum ℝ (fun i => degSub (unitsR K) 1 i) (fun i => degSub (InfinitePlace K → ℝ) 1 i)
      (fun i => degSub ℝ 2 i) where
  reg i := degMap (regR K) 1 1 i i id
  toMot i := 0
  conn i := degMap (sumMap K) 1 2 i (i + 1) (fun h => by omega)
  exact_toMot i := by
    rw [LinearMap.range_zero]
    symm
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply regR_injective K
    simpa using congrArg Subtype.val hx
  exact_reg i := by
    ext y
    by_cases hi : i = 1
    · subst hi
      constructor
      · rintro ⟨x, rfl⟩
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        simp only [degMap_apply, ZeroMemClass.coe_zero]
        have : regR K x ∈ LinearMap.range (regR K) := ⟨x, rfl⟩
        rw [range_regR] at this
        exact this
      · intro hy
        have hy' : (y : InfinitePlace K → ℝ) ∈ LinearMap.ker (sumMap K) := by
          have := congrArg Subtype.val hy
          simpa using this
        rw [← range_regR] at hy'
        obtain ⟨x, hx⟩ := hy'
        exact ⟨⟨x, mem_degSub_self 1 x⟩, Subtype.ext hx⟩
    · have : (y : InfinitePlace K → ℝ) = 0 := eq_zero_of_mem_degSub hi y.2
      have hy0 : y = 0 := Subtype.ext this
      subst hy0
      simp only [Submodule.zero_mem]
  exact_conn i := by
    rw [LinearMap.ker_zero, LinearMap.range_eq_top]
    intro z
    by_cases hi : i = 1
    · subst hi
      obtain ⟨f, hf⟩ := sumMap_surjective K (z : ℝ)
      exact ⟨⟨f, mem_degSub_self 1 f⟩, Subtype.ext hf⟩
    · have hz : (z : ℝ) = 0 := eq_zero_of_mem_degSub (by omega) z.2
      exact ⟨0, Subtype.ext (by simp [hz])⟩

/-- `H²_c` of the degree-one datum is `ℝ`. -/
noncomputable def degreeOne_Hc_two : degSub ℝ 2 2 ≃ₗ[ℝ] ℝ :=
  (LinearEquiv.ofEq _ _ (degSub_self ℝ 2)).trans Submodule.topEquiv

/-- `H¹_D` of the degree-one datum is nonzero (`X̄_K` has an infinite place). -/
theorem degreeOne_Del_one_nontrivial : Nontrivial (degSub (InfinitePlace K → ℝ) 1 1) := by
  classical
  refine ⟨⟨0, ?_⟩, ⟨Pi.single w₀ 1, mem_degSub_self 1 _⟩, ?_⟩
  · exact zero_mem _
  · intro h
    have := congr_fun (congrArg Subtype.val h) w₀
    simp at this

/-- The degree-one datum is not degenerate: its connecting map `H¹_D → H²_c` is nonzero. -/
theorem degreeOne_conn_ne_zero : (degreeOne K).conn 1 ≠ 0 := by
  classical
  intro h
  have := congrArg Subtype.val (LinearMap.congr_fun h ⟨Pi.single w₀ 1, mem_degSub_self 1 _⟩)
  simp [degreeOne] at this

end WeilRH.Arakelov
