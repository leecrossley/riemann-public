/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.WeightedAlgebra

/-!
# Flow spaces: kernels, cokernels and additivity of divisors

Source: the manuscript `latex/notes.tex`, `def:flow-category` and `prop:flow-exact` (with
`def:spectral-core`).

`Flow` is the category of spectral cores `(V, Θ)` with `ℂ`-linear maps commuting with the
generators. A morphism preserves generalized eigenspaces, and on generalized eigenspaces it is
exact. Hence kernels and cokernels of morphisms are again spectral cores, and alternating
multiplicities are additive in bounded exact sequences.

## Main results

* `WeilRH.Flow.Obj`, `WeilRH.Flow.Hom`, `CategoryTheory.Category` instance (`def:flow-category`).
* `WeilRH.Flow.map_maxGenEigenspace_le`: a morphism maps `V_{Θ∼ρ}` into `W_{Θ∼ρ}`.
* `WeilRH.Flow.maxGenEigenspace_inf_range`: if `V` is spanned by its generalized eigenspaces then
  `W_{Θ∼ρ} ∩ f(V) = f(V_{Θ∼ρ})` (exactness on blocks, `prop:flow-exact` (a)).
* `WeilRH.Flow.exact_maxGenEigenspace`: for `V' → V → V''` exact in `Flow`, the restricted
  sequence of `ρ`-blocks is exact (`prop:flow-exact` (a), last clause).
* `WeilRH.Flow.spectralCore_ker`, `WeilRH.Flow.spectralCore_coker` (`prop:flow-exact` (a)):
  kernel and cokernel of a morphism of spectral cores, with the induced generators, are spectral
  cores.
* `WeilRH.Flow.alternating_finrank_eq_zero`: a bounded exact sequence of finite-dimensional spaces
  has alternating dimension sum zero.
* `WeilRH.Flow.alternating_mult_eq_zero` (`prop:flow-exact` (b)): for a bounded exact sequence of
  spectral cores, `Σ_n (-1)^n m_{E_n}(ρ) = 0` for every `ρ`.

## Fidelity

`prop:flow-exact` (b) is stated in the notes for a long exact sequence
`⋯ → V'^j → V^j → V''^j → V'^{j+1} → ⋯` indexed by `ℤ` and bounded. Here a bounded exact sequence
is indexed by `ℕ`, starts with an injective map (exactness at the first term) and vanishes from
some index `N` on; a bounded `ℤ`-indexed sequence becomes one of these after a shift, and the
three-term long exact sequence is the special case `E_{3j} = V'^j`, `E_{3j+1} = V^j`,
`E_{3j+2} = V''^j`, where `(-1)^{3j+k} = (-1)^{j+k}` gives the displayed identity coefficientwise.
That reindexing is not formalized.
-/

open Module Filter

namespace WeilRH.Flow

open WeilRH.Spectral

universe u

/-! ### Generalized eigenspaces under commuting maps -/

section Maps

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma comp_sub_smul_pow {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : f ∘ₗ ΘV = ΘW ∘ₗ f) (ρ : ℂ) (k : ℕ) (x : V) :
    f (((ΘV - ρ • 1) ^ k) x) = ((ΘW - ρ • 1) ^ k) (f x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    have := LinearMap.congr_fun hf x
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    simp [this]

/-- A map commuting with the generators sends `V_{Θ∼ρ}` into `W_{Θ∼ρ}`. -/
theorem map_maxGenEigenspace_le {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : f ∘ₗ ΘV = ΘW ∘ₗ f) (ρ : ℂ) :
    (ΘV.maxGenEigenspace ρ).map f ≤ ΘW.maxGenEigenspace ρ := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe] at hx
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [← comp_sub_smul_pow f hf, hk, map_zero]⟩

/-- **Exactness on blocks.** If `V` is spanned by its generalized eigenspaces and `f` commutes with
the generators, then `W_{Θ∼ρ} ∩ f(V) = f(V_{Θ∼ρ})`. Independence of the generalized eigenspaces of
`W` is automatic. -/
theorem maxGenEigenspace_inf_range {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W)
    (hf : f ∘ₗ ΘV = ΘW ∘ₗ f) (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (ρ : ℂ) :
    ΘW.maxGenEigenspace ρ ⊓ LinearMap.range f = (ΘV.maxGenEigenspace ρ).map f := by
  refine le_antisymm ?_ (le_inf (map_maxGenEigenspace_le f hf ρ) (LinearMap.map_le_range))
  rintro z ⟨hz, ⟨y, rfl⟩⟩
  have hy : y ∈ ⨆ σ, ΘV.maxGenEigenspace σ := by rw [hV]; trivial
  rw [iSup_split_single _ ρ, Submodule.mem_sup] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  have hfb : f b ∈ ⨆ (σ) (_ : σ ≠ ρ), ΘW.maxGenEigenspace σ := by
    have h1 : f b ∈ (⨆ (σ) (_ : σ ≠ ρ), ΘV.maxGenEigenspace σ).map f := ⟨b, hb, rfl⟩
    refine (Submodule.map_le_iff_le_comap.mpr ?_) h1
    refine iSup₂_le fun σ hσ => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact (map_maxGenEigenspace_le f hf σ).trans (le_iSup₂_of_le σ hσ le_rfl)
  have hfa : f a ∈ ΘW.maxGenEigenspace ρ := map_maxGenEigenspace_le f hf ρ ⟨a, ha, rfl⟩
  have hfb' : f b ∈ ΘW.maxGenEigenspace ρ := by
    have : f b = f (a + b) - f a := by rw [map_add]; abel
    rw [this]; exact Submodule.sub_mem _ hz hfa
  have hdisj := (Module.End.independent_maxGenEigenspace ΘW) ρ
  have h0 : f b = 0 := by
    have := hdisj.le_bot ⟨hfb', by simpa [iSup_subtype'] using hfb⟩
    simpa using this
  exact ⟨a, ha, by rw [map_add, h0, add_zero]⟩

end Maps

/-! ### Finite-dimensional stable subspaces -/

section Stable

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma maxGenEigenspace_mapsTo (Θ : Module.End ℂ V) (ρ : ℂ) {x : V}
    (hx : x ∈ Θ.maxGenEigenspace ρ) : Θ x ∈ Θ.maxGenEigenspace ρ := by
  have := map_maxGenEigenspace_le (ΘV := Θ) (ΘW := Θ) Θ rfl ρ
  exact this ⟨x, hx, rfl⟩

/-- In a spectral core every vector lies in a finite-dimensional `Θ`-stable subspace. -/
theorem exists_fd_stable {Θ : Module.End ℂ V} (h : SpectralCore Θ) (x : V) :
    ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ (∀ y ∈ E, Θ y ∈ E) ∧ x ∈ E := by
  have hx : x ∈ ⨆ ρ, Θ.maxGenEigenspace ρ := by rw [h.iSup_eq_top]; trivial
  obtain ⟨s, hs⟩ := Submodule.exists_finset_of_mem_iSup _ hx
  rw [← Finset.sup_eq_iSup] at hs
  refine ⟨s.sup fun ρ => Θ.maxGenEigenspace ρ, ?_, ?_, hs⟩
  · have := h.finiteDimensional
    infer_instance
  · intro y hy
    have hle : (s.sup fun ρ => Θ.maxGenEigenspace ρ) ≤
        (s.sup fun ρ => Θ.maxGenEigenspace ρ).comap Θ := by
      refine Finset.sup_le fun ρ hρ => fun z hz => ?_
      exact (Finset.le_sup (f := fun ρ => Θ.maxGenEigenspace ρ) hρ)
        (maxGenEigenspace_mapsTo Θ ρ hz)
    exact hle hy

/-- If every vector lies in a finite-dimensional `Θ`-stable subspace, `V` is spanned by the
generalized eigenspaces of `Θ` (`ℂ` is algebraically closed). -/
theorem iSup_maxGenEigenspace_of_fd_stable {Θ : Module.End ℂ V}
    (h : ∀ x : V, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ (∀ y ∈ E, Θ y ∈ E) ∧ x ∈ E) :
    ⨆ ρ, Θ.maxGenEigenspace ρ = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨E, hfd, hst, hx⟩ := h x
  let ΘE : Module.End ℂ E := Θ.restrict (p := E) (q := E) hst
  have htop := Module.End.iSup_maxGenEigenspace_eq_top ΘE
  have hxE : (⟨x, hx⟩ : E) ∈ ⨆ ρ, ΘE.maxGenEigenspace ρ := by rw [htop]; trivial
  have hmap : (⨆ ρ, ΘE.maxGenEigenspace ρ).map E.subtype ≤ ⨆ ρ, Θ.maxGenEigenspace ρ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun ρ => map_maxGenEigenspace_le E.subtype ?_ ρ
    ext y; simp [ΘE]
  exact hmap ⟨_, hxE, rfl⟩

end Stable

/-! ### The category `Flow` -/

/-- **`def:flow-category`, objects.** A spectral core `(V, Θ)`. -/
structure Obj where
  /-- The underlying space. -/
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module ℂ carrier]
  /-- The generator. -/
  Θ : Module.End ℂ carrier
  /-- `(V, Θ)` is a spectral core. -/
  core : SpectralCore Θ

attribute [instance] Obj.acg Obj.mod

/-- **`def:flow-category`, morphisms.** A `ℂ`-linear map with `f Θ_V = Θ_W f`. -/
@[ext]
structure Hom (V W : Obj.{u}) where
  /-- The linear map. -/
  toLin : V.carrier →ₗ[ℂ] W.carrier
  comm : toLin ∘ₗ V.Θ = W.Θ ∘ₗ toLin

instance : CategoryTheory.Category Obj.{u} where
  Hom := Hom
  id V := ⟨LinearMap.id, by simp⟩
  comp f g := ⟨g.toLin ∘ₗ f.toLin, by
    rw [LinearMap.comp_assoc, f.comm, ← LinearMap.comp_assoc, g.comm, LinearMap.comp_assoc]⟩

/-! ### Kernels and cokernels -/

section KerCoker

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W} (f : V →ₗ[ℂ] W) (hf : f ∘ₗ ΘV = ΘW ∘ₗ f)

include hf in
lemma mem_ker_of_mem {x : V} (hx : x ∈ LinearMap.ker f) : ΘV x ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker] at hx ⊢
  have := LinearMap.congr_fun hf x
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, hx, map_zero]

/-- The generator induced on `ker f`. -/
def kerΘ : Module.End ℂ (LinearMap.ker f) :=
  ΘV.restrict (p := LinearMap.ker f) (q := LinearMap.ker f) fun _ hx => mem_ker_of_mem f hf hx

include hf in
lemma range_le_comap : LinearMap.range f ≤ (LinearMap.range f).comap ΘW := by
  rintro _ ⟨x, rfl⟩
  have := LinearMap.congr_fun hf x
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  exact ⟨ΘV x, this⟩

/-- The generator induced on `coker f = W / f(V)`. -/
def cokerΘ : Module.End ℂ (W ⧸ LinearMap.range f) :=
  (LinearMap.range f).mapQ (LinearMap.range f) ΘW (range_le_comap f hf)

lemma cokerΘ_mkQ : cokerΘ f hf ∘ₗ (LinearMap.range f).mkQ = (LinearMap.range f).mkQ ∘ₗ ΘW := by
  ext y; simp [cokerΘ]

include hf in
/-- **`prop:flow-exact` (a), kernels.** The kernel of a morphism of spectral cores, with the
induced generator, is a spectral core. -/
theorem spectralCore_ker (hV : SpectralCore ΘV) : SpectralCore (kerΘ f hf) := by
  have hsub : (LinearMap.ker f).subtype ∘ₗ kerΘ f hf = ΘV ∘ₗ (LinearMap.ker f).subtype := by
    ext; simp [kerΘ]
  have hle : ∀ ρ, ((kerΘ f hf).maxGenEigenspace ρ).map (LinearMap.ker f).subtype ≤
      ΘV.maxGenEigenspace ρ := fun ρ => map_maxGenEigenspace_le _ hsub ρ
  refine ⟨?_, fun ρ => ?_, fun z hz => ?_⟩
  · refine iSup_maxGenEigenspace_of_fd_stable fun x => ?_
    obtain ⟨E, hfd, hst, hx⟩ := exists_fd_stable hV x
    refine ⟨E.comap (LinearMap.ker f).subtype, ?_, fun y hy => ?_, hx⟩
    · have := hfd
      exact FiniteDimensional.of_injective
        (((LinearMap.ker f).subtype ∘ₗ (E.comap (LinearMap.ker f).subtype).subtype).codRestrict
          E fun y => y.2)
        (fun a b h => by
          ext
          exact congrArg (fun z : E => (z : V)) h)
    · exact hst _ hy
  · have := hV.finiteDimensional ρ
    exact FiniteDimensional.of_injective
      (((LinearMap.ker f).subtype.domRestrict _).codRestrict (ΘV.maxGenEigenspace ρ)
        fun y => hle ρ ⟨y.1, y.2, rfl⟩)
      (fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  · apply hV.noAccPt z
    refine hz.mono (principal_mono.mpr fun ρ hρ hbot => hρ ?_)
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro y hy
    exact Subtype.ext (hbot y.1 (hle ρ ⟨y, hy, rfl⟩))

include hf in
/-- **`prop:flow-exact` (a), cokernels.** The cokernel of a morphism of spectral cores, with the
induced generator, is a spectral core; its `ρ`-block is the image of `W_{Θ∼ρ}`. -/
theorem spectralCore_coker (hW : SpectralCore ΘW) : SpectralCore (cokerΘ f hf) := by
  set π := (LinearMap.range f).mkQ
  have hπ : π ∘ₗ ΘW = cokerΘ f hf ∘ₗ π := (cokerΘ_mkQ f hf).symm
  have himg : ∀ ρ, (cokerΘ f hf).maxGenEigenspace ρ = (ΘW.maxGenEigenspace ρ).map π := by
    intro ρ
    have := maxGenEigenspace_inf_range π hπ hW.iSup_eq_top ρ
    rwa [Submodule.range_mkQ, inf_top_eq] at this
  refine ⟨?_, fun ρ => ?_, fun z hz => ?_⟩
  · have := congrArg (Submodule.map π) hW.iSup_eq_top
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_mkQ] at this
    simp_rw [← himg] at this
    exact this
  · have := hW.finiteDimensional ρ
    rw [himg]
    infer_instance
  · apply hW.noAccPt z
    refine hz.mono (principal_mono.mpr fun ρ hρ hbot => hρ ?_)
    rw [himg, hbot, Submodule.map_bot]

end KerCoker

/-! ### Exactness on blocks -/

section Exact

variable {V' V V'' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V''] [Module ℂ V'']
  {Θ' : Module.End ℂ V'} {Θ : Module.End ℂ V} {Θ'' : Module.End ℂ V''}

/-- **`prop:flow-exact` (a), exactness of `V ↦ V_{Θ∼ρ}`.** If `V' → V → V''` is exact in `Flow`
(`range f = ker g`) and `V'` is spanned by its generalized eigenspaces, then every element of
`V_{Θ∼ρ}` killed by `g` is the image of an element of `V'_{Θ∼ρ}`. -/
theorem exact_maxGenEigenspace (f : V' →ₗ[ℂ] V) (g : V →ₗ[ℂ] V'') (hf : f ∘ₗ Θ' = Θ ∘ₗ f)
    (hex : LinearMap.range f = LinearMap.ker g) (h' : ⨆ ρ, Θ'.maxGenEigenspace ρ = ⊤) (ρ : ℂ)
    {x : V} (hx : x ∈ Θ.maxGenEigenspace ρ) (hgx : g x = 0) :
    ∃ y ∈ Θ'.maxGenEigenspace ρ, f y = x := by
  have : x ∈ Θ.maxGenEigenspace ρ ⊓ LinearMap.range f :=
    ⟨hx, by rw [hex]; exact hgx⟩
  rw [maxGenEigenspace_inf_range f hf h' ρ] at this
  obtain ⟨y, hy, rfl⟩ := this
  exact ⟨y, hy, rfl⟩

end Exact

/-! ### Additivity -/

section Additive

/-- A bounded exact sequence of finite-dimensional spaces `0 → E_0 → E_1 → ⋯`, zero from `N` on,
has alternating dimension sum zero. -/
theorem alternating_finrank_eq_zero (E : ℕ → Type u) [∀ n, AddCommGroup (E n)]
    [∀ n, Module ℂ (E n)] [∀ n, FiniteDimensional ℂ (E n)] (d : ∀ n, E n →ₗ[ℂ] E (n + 1))
    (hinj : LinearMap.ker (d 0) = ⊥)
    (hex : ∀ n, LinearMap.range (d n) = LinearMap.ker (d (n + 1)))
    (N : ℕ) (hN : ∀ n, N ≤ n → Subsingleton (E n)) :
    ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (finrank ℂ (E n) : ℤ) = 0 := by
  set r : ℕ → ℤ := fun n => (finrank ℂ (LinearMap.range (d n)) : ℤ)
  have hdim : ∀ n, (finrank ℂ (E n) : ℤ) =
      (finrank ℂ (LinearMap.ker (d n)) : ℤ) + r n := by
    intro n
    have := LinearMap.finrank_range_add_finrank_ker (d n)
    simp only [r]; omega
  have key : ∀ m, ∑ n ∈ Finset.range (m + 1), (-1 : ℤ) ^ n * (finrank ℂ (E n) : ℤ) =
      (-1) ^ m * r m := by
    intro m
    induction m with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
      rw [hdim 0, hinj, finrank_bot]; simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, hdim (m + 1), ← hex m]
      simp only [r, pow_succ]; ring
  rcases N with _ | N
  · simp
  · rw [key N]
    have : Subsingleton (E (N + 1)) := hN (N + 1) le_rfl
    have : r N = 0 := by
      simp only [r, Nat.cast_eq_zero]
      apply Submodule.finrank_eq_zero.mpr
      rw [Submodule.eq_bot_iff]; intro y _; exact Subsingleton.elim _ _
    rw [this, mul_zero]

/-- **`prop:flow-exact` (b).** Let `0 → E_0 → E_1 → ⋯` be a bounded exact sequence of spectral
cores (`E_n = 0` for `n ≥ N`) whose maps commute with the generators. Then for every `ρ`,
`Σ_n (-1)^n m_{E_n}(ρ) = 0`; equivalently `Σ_n (-1)^n Sp(E_n) = 0`. -/
theorem alternating_mult_eq_zero (E : ℕ → Type u) [∀ n, AddCommGroup (E n)]
    [∀ n, Module ℂ (E n)] (Θ : ∀ n, Module.End ℂ (E n)) (hc : ∀ n, SpectralCore (Θ n))
    (d : ∀ n, E n →ₗ[ℂ] E (n + 1)) (hd : ∀ n, d n ∘ₗ Θ n = Θ (n + 1) ∘ₗ d n)
    (hinj : LinearMap.ker (d 0) = ⊥)
    (hex : ∀ n, LinearMap.range (d n) = LinearMap.ker (d (n + 1)))
    (N : ℕ) (hN : ∀ n, N ≤ n → Subsingleton (E n)) (ρ : ℂ) :
    ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (mult (Θ n) ρ : ℤ) = 0 := by
  have hmaps : ∀ n, ∀ x ∈ (Θ n).maxGenEigenspace ρ, d n x ∈ (Θ (n + 1)).maxGenEigenspace ρ :=
    fun n x hx => map_maxGenEigenspace_le (d n) (hd n) ρ ⟨x, hx, rfl⟩
  let B : ℕ → Type u := fun n => (Θ n).maxGenEigenspace ρ
  have : ∀ n, FiniteDimensional ℂ (B n) := fun n => (hc n).finiteDimensional ρ
  let dB : ∀ n, B n →ₗ[ℂ] B (n + 1) := fun n => (d n).restrict (hmaps n)
  have hdB : ∀ n (x : B n), (dB n x : E (n + 1)) = d n x := fun _ _ => rfl
  refine alternating_finrank_eq_zero B dB ?_ ?_ N ?_
  · rw [Submodule.eq_bot_iff]
    intro x hx
    have : d 0 x = 0 := by rw [← hdB]; exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have : (x : E 0) ∈ LinearMap.ker (d 0) := this
    rw [hinj] at this
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp this)
  · intro n
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [hdB, hdB]
      have : d n x ∈ LinearMap.ker (d (n + 1)) := by rw [← hex]; exact ⟨x, rfl⟩
      simpa using this
    · intro y hy
      have hgy : d (n + 1) y = 0 := by
        rw [← hdB]; exact congrArg Subtype.val (LinearMap.mem_ker.mp hy)
      obtain ⟨x, hx, hxy⟩ :=
        exact_maxGenEigenspace (d n) (d (n + 1)) (hd n) (hex n) (hc n).iSup_eq_top ρ y.2 hgy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  · intro n hn
    have := hN n hn
    infer_instance

end Additive

end WeilRH.Flow
