/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Spectral cores: support of the duality pairing and the spectrum of a tensor product

Source: the manuscript `latex/notes.tex`, `prop:B-support` and `prop:tensor-eigen`
(with `def:spectral-core`).

Generalized eigenspaces `V_{Θ∼ρ} = ⋃ₖ ker (Θ - ρ)ᵏ` are Mathlib's `Module.End.maxGenEigenspace`.

## Main results

* `WeilRH.Spectral.pairing_eq_zero_of_mem_maxGenEigenspace` (`prop:B-support`): if a bilinear
  pairing `B : V × W → K` satisfies `B(Θu, v) + B(u, Θv) = c·B(u, v)` then `B` vanishes on
  `V_{Θ∼ρ} × W_{Θ∼σ}` unless `ρ + σ = c`. The manuscript takes `B = B_j`, `V = V^j`,
  `W = V^{2d-j}`, `c = d`; the hypothesis is the displayed consequence of the derivation rule of
  AW1 and the trace equivariance of AW3, from which its proof starts.
* `WeilRH.Spectral.maxGenEigenspace_tensorSum_eq` (`prop:tensor-eigen`, first display): when `V`
  and `W` are spanned by their generalized eigenspaces,
  `(V ⊗ W)_{Θ∼λ} = ⨆_{ρ+ρ'=λ} V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` for `Θ = Θ_V ⊗ 1 + 1 ⊗ Θ_W`. The block
  `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` is encoded as the range of the tensor product of the two inclusions,
  which is injective over a field (`blockEquiv`).
* `WeilRH.Spectral.isInternal_block`, `isInternal_block_maxGenEigenspace` (`prop:tensor-eigen`,
  directness): `V ⊗ W` is the internal direct sum of all blocks, and `(V ⊗ W)_{Θ∼λ}` the internal
  direct sum of the blocks with `ρ + ρ' = λ` (`iSupIndep_block`: the blocks sit in the joint
  generalized eigenspaces of the commuting pair `Θ_V ⊗ 1`, `1 ⊗ Θ_W`).
* `WeilRH.Spectral.mapsTo_block`, `block_le`, and the `FiniteDimensional` instance on `block`
  (`prop:tensor-eigen`, first sentence): each block is `Θ`-stable, has the single generalized
  eigenvalue `ρ + ρ'`, and is finite-dimensional when `V_{Θ∼ρ}`, `W_{Θ∼ρ'}` are.
* `WeilRH.Spectral.rank_maxGenEigenspace_tensorSum` (`prop:tensor-eigen`, dimension formula):
  `dim (V ⊗ W)_{Θ∼λ} = Σ_{ρ+ρ'=λ} m_V(ρ) m_W(ρ')` as a cardinal identity (`Module.rank`), which
  also covers the infinite sums the manuscript mentions after the proposition.

Only the spanning clause of `def:spectral-core` (b) is assumed; independence of generalized
eigenspaces is automatic (Mathlib's `Module.End.independent_maxGenEigenspace`). The
finite-dimensionality clause enters only through the `FiniteDimensional` instance, and the
discreteness clause is not used.

* `WeilRH.Spectral.SpectralCore` (`def:spectral-core` (b)), `spec`, `mult` (`def:spectral-core`
  (c)); `SpectralCore.tensor_eigen` packages `prop:tensor-eigen` for spectral cores, and
  `finrank_maxGenEigenspace_tensorSum` is the dimension formula as a `finrank` identity when only
  finitely many pairs `(ρ, ρ') ∈ spec Θ_V × spec Θ_W` have `ρ + ρ' = λ`.
* `WeilRH.Spectral.map_maxGenEigenspace_of_equiv`, `SpectralCore.of_equiv`: a linear isomorphism
  intertwining two operators carries generalized eigenspaces to generalized eigenspaces, so the
  spectral-core condition transfers along it.
-/

open TensorProduct

namespace WeilRH.Spectral

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-! ### `prop:B-support` -/

/-- Generalized eigenvectors for `ρ`, `σ` with `ρ + σ ≠ c` are `B`-orthogonal (induction on the
lengths of the Jordan chains). -/
theorem pairing_eq_zero_of_pow (B : V →ₗ[K] W →ₗ[K] K) (ΘV : Module.End K V)
    (ΘW : Module.End K W) (c : K) (hB : ∀ u v, B (ΘV u) v + B u (ΘW v) = c * B u v)
    {ρ σ : K} (hρσ : ρ + σ ≠ c) :
    ∀ (k l : ℕ) (u : V) (v : W), ((ΘV - ρ • 1) ^ k) u = 0 → ((ΘW - σ • 1) ^ l) v = 0 →
      B u v = 0 := by
  intro k
  induction k with
  | zero => intro l u v hu _; simp only [pow_zero, Module.End.one_apply] at hu; simp [hu]
  | succ k ihk =>
    intro l
    induction l with
    | zero => intro u v _ hv; simp only [pow_zero, Module.End.one_apply] at hv; simp [hv]
    | succ l ihl =>
      intro u v hu hv
      rw [pow_succ, Module.End.mul_apply] at hu hv
      have h1 := ihk (l + 1) _ v hu (by rw [pow_succ, Module.End.mul_apply]; exact hv)
      have h2 := ihl u _ (by rw [pow_succ, Module.End.mul_apply]; exact hu) hv
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1 h2
      have key := hB u v
      have : (c - ρ - σ) * B u v = 0 := by linear_combination h1 + h2 - key
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linear_combination -h) hρσ
      · exact h

/-- **`prop:B-support`.** A pairing of weight `c` (`B(Θu, v) + B(u, Θv) = c·B(u, v)`) vanishes on
`V_{Θ∼ρ} × W_{Θ∼σ}` unless `ρ + σ = c`. -/
theorem pairing_eq_zero_of_mem_maxGenEigenspace (B : V →ₗ[K] W →ₗ[K] K) (ΘV : Module.End K V)
    (ΘW : Module.End K W) (c : K) (hB : ∀ u v, B (ΘV u) v + B u (ΘW v) = c * B u v)
    {ρ σ : K} (hρσ : ρ + σ ≠ c) {u : V} {v : W} (hu : u ∈ ΘV.maxGenEigenspace ρ)
    (hv : v ∈ ΘW.maxGenEigenspace σ) : B u v = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hu
  obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  exact pairing_eq_zero_of_pow B ΘV ΘW c hB hρσ k l u v hk hl

/-! ### `prop:tensor-eigen` -/

/-- The operator `Θ = Θ_V ⊗ 1 + 1 ⊗ Θ_W` on `V ⊗ W`. -/
def tensorSum (ΘV : Module.End K V) (ΘW : Module.End K W) : Module.End K (V ⊗[K] W) :=
  ΘV.rTensor W + ΘW.lTensor V

/-- The block `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}`, as a subspace of `V ⊗ W`. -/
def block (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) : Submodule K (V ⊗[K] W) :=
  LinearMap.range (TensorProduct.map (ΘV.maxGenEigenspace ρ).subtype
    (ΘW.maxGenEigenspace ρ').subtype)

lemma tensorSum_sub_smul (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    tensorSum ΘV ΘW - (ρ + ρ') • 1 = (ΘV - ρ • 1).rTensor W + (ΘW - ρ' • 1).lTensor V := by
  apply TensorProduct.ext'
  intro x y
  simp [tensorSum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, add_smul,
    smul_tmul']
  abel

lemma commute_rTensor_lTensor (f : Module.End K V) (g : Module.End K W) :
    Commute (f.rTensor W) (g.lTensor V) := by
  show f.rTensor W ∘ₗ g.lTensor V = g.lTensor V ∘ₗ f.rTensor W
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- If `(Θ_V - ρ)ᵏ x = 0` and `(Θ_W - ρ')ˡ y = 0` then `(Θ - ρ - ρ')^(k+l) (x ⊗ y) = 0`. -/
lemma pow_tmul_eq_zero (ΘV : Module.End K V) (ΘW : Module.End K W) {ρ ρ' : K} {k l : ℕ}
    {x : V} {y : W} (hx : ((ΘV - ρ • 1) ^ k) x = 0) (hy : ((ΘW - ρ' • 1) ^ l) y = 0) :
    ((tensorSum ΘV ΘW - (ρ + ρ') • 1) ^ (k + l)) (x ⊗ₜ y) = 0 := by
  rw [tensorSum_sub_smul, (commute_rTensor_lTensor _ _).add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply,
    LinearMap.rTensor_pow, LinearMap.lTensor_pow, map_nsmul, map_nsmul, LinearMap.lTensor_tmul,
    LinearMap.rTensor_tmul]
  rcases le_or_gt k m with hkm | hkm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkm
    rw [add_comm k n, pow_add, Module.End.mul_apply, hx, map_zero, zero_tmul, smul_zero]
  · obtain ⟨n, hn⟩ : ∃ n, k + l - m = l + n := ⟨k - m, by omega⟩
    rw [hn, add_comm l n, pow_add, Module.End.mul_apply, hy, map_zero, tmul_zero, smul_zero]

/-- `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'} ⊆ (V ⊗ W)_{Θ∼ρ+ρ'}`. -/
theorem block_le (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    block ΘV ΘW ρ ρ' ≤ (tensorSum ΘV ΘW).maxGenEigenspace (ρ + ρ') := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 x.2
    obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 y.2
    rw [TensorProduct.map_tmul, Module.End.mem_maxGenEigenspace]
    exact ⟨k + l, pow_tmul_eq_zero ΘV ΘW hk hl⟩
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- The blocks span `V ⊗ W` when `V` and `W` are spanned by their generalized eigenspaces. -/
theorem iSup_block_eq_top (ΘV : Module.End K V) (ΘW : Module.End K W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) :
    ⨆ p : K × K, block ΘV ΘW p.1 p.2 = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact add_mem ha hb
  | tmul x y =>
    have hx : x ∈ ⨆ ρ, ΘV.maxGenEigenspace ρ := hV ▸ Submodule.mem_top
    have hy : y ∈ ⨆ ρ', ΘW.maxGenEigenspace ρ' := hW ▸ Submodule.mem_top
    induction hx using Submodule.iSup_induction' with
    | zero => simp
    | add x x' _ _ ihx ihx' => rw [add_tmul]; exact add_mem ihx ihx'
    | mem ρ x hxρ =>
      induction hy using Submodule.iSup_induction' with
      | zero => simp
      | add y y' _ _ ihy ihy' => rw [tmul_add]; exact add_mem ihy ihy'
      | mem ρ' y hyρ' =>
        refine Submodule.mem_iSup_of_mem (ρ, ρ') ⟨⟨x, hxρ⟩ ⊗ₜ ⟨y, hyρ'⟩, ?_⟩
        rfl

/-- **`prop:tensor-eigen`** (first display). If `V` and `W` are spanned by their generalized
eigenspaces, the generalized `λ`-eigenspace of `Θ = Θ_V ⊗ 1 + 1 ⊗ Θ_W` on `V ⊗ W` is the sum of
the blocks `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` with `ρ + ρ' = λ`. -/
theorem maxGenEigenspace_tensorSum_eq (ΘV : Module.End K V) (ΘW : Module.End K W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) (lam : K) :
    (tensorSum ΘV ΘW).maxGenEigenspace lam =
      ⨆ (p : K × K) (_ : p.1 + p.2 = lam), block ΘV ΘW p.1 p.2 := by
  set E := (tensorSum ΘV ΘW).maxGenEigenspace
  set S : K → Submodule K (V ⊗[K] W) := fun μ => ⨆ (p : K × K) (_ : p.1 + p.2 = μ),
    block ΘV ΘW p.1 p.2
  have hSE : ∀ μ, S μ ≤ E μ := fun μ =>
    iSup₂_le fun p hp => hp ▸ block_le ΘV ΘW p.1 p.2
  have hStop : ⨆ μ, S μ = ⊤ := by
    rw [eq_top_iff, ← iSup_block_eq_top ΘV ΘW hV hW]
    exact iSup_le fun p => le_iSup_of_le (p.1 + p.2) (le_iSup₂_of_le p rfl le_rfl)
  show E lam = S lam
  refine le_antisymm (fun z hz => ?_) (hSE lam)
  have hz' : z ∈ S lam ⊔ ⨆ (μ) (_ : μ ≠ lam), S μ := by
    rw [← iSup_split_single S lam, hStop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
  have hbE : b ∈ ⨆ (μ) (_ : μ ≠ lam), E μ :=
    (iSup₂_mono fun μ _ => hSE μ) hb
  have hbE' : b ∈ E lam := by
    have := sub_mem hz (hSE lam ha); simpa using this
  have hb0 : b = 0 :=
    (Submodule.disjoint_def.1 (Module.End.independent_maxGenEigenspace _ lam)) b hbE' hbE
  simpa [hb0] using ha

/-! ### `prop:tensor-eigen`: directness, stability, dimension -/

/-- `(f - ρ) ⊗ 1 = f ⊗ 1 - ρ`. -/
lemma rTensor_sub_smul (f : Module.End K V) (ρ : K) :
    (f - ρ • 1).rTensor W = f.rTensor W - ρ • 1 := by
  apply TensorProduct.ext'; intro x y; simp [LinearMap.rTensor_tmul, smul_tmul']

/-- `1 ⊗ (g - ρ) = 1 ⊗ g - ρ`. -/
lemma lTensor_sub_smul (g : Module.End K W) (ρ : K) :
    (g - ρ • 1).lTensor V = g.lTensor V - ρ • 1 := by
  apply TensorProduct.ext'; intro x y; simp [LinearMap.lTensor_tmul]

/-- `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` lies in the generalized `ρ`-eigenspace of `Θ_V ⊗ 1`. -/
lemma block_le_rTensor (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    block ΘV ΘW ρ ρ' ≤ Module.End.maxGenEigenspace (ΘV.rTensor W) ρ := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 x.2
    rw [TensorProduct.map_tmul, Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    rw [← rTensor_sub_smul, LinearMap.rTensor_pow, LinearMap.rTensor_tmul]
    simp [hk]
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}` lies in the generalized `ρ'`-eigenspace of `1 ⊗ Θ_W`. -/
lemma block_le_lTensor (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    block ΘV ΘW ρ ρ' ≤ Module.End.maxGenEigenspace (ΘW.lTensor V) ρ' := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 y.2
    rw [TensorProduct.map_tmul, Module.End.mem_maxGenEigenspace]
    refine ⟨k, ?_⟩
    rw [← lTensor_sub_smul, LinearMap.lTensor_pow, LinearMap.lTensor_tmul]
    simp [hk]
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- The blocks `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}`, `(ρ, ρ') ∈ K × K`, are independent: they are contained in
the joint generalized eigenspaces of the commuting pair `Θ_V ⊗ 1`, `1 ⊗ Θ_W`. -/
theorem iSupIndep_block (ΘV : Module.End K V) (ΘW : Module.End K W) :
    iSupIndep fun p : K × K => block ΘV ΘW p.1 p.2 := by
  let f : Bool → Module.End K (V ⊗[K] W) := fun b => if b then ΘV.rTensor W else ΘW.lTensor V
  have hcomm : ∀ i j, Commute (f i) (f j) := by
    have h := commute_rTensor_lTensor ΘV ΘW
    intro i j; cases i <;> cases j <;> simp [f, h, h.symm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  let g : K × K → Bool → K := fun p b => if b then p.1 else p.2
  have hg : Function.Injective g := by
    intro p q h
    have h1 := congrFun h true; have h2 := congrFun h false
    simp [g] at h1 h2; exact Prod.ext h1 h2
  refine (hind.comp hg).mono fun p => le_iInf fun b => ?_
  cases b
  · simpa [f, g] using block_le_lTensor ΘV ΘW p.1 p.2
  · simpa [f, g] using block_le_rTensor ΘV ΘW p.1 p.2


/-- **`prop:tensor-eigen`** (direct sum). If `V` and `W` are spanned by their generalized
eigenspaces, `V ⊗ W` is the internal direct sum of the blocks `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}`. -/
theorem isInternal_block [DecidableEq K] (ΘV : Module.End K V) (ΘW : Module.End K W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) :
    DirectSum.IsInternal fun p : K × K => block ΘV ΘW p.1 p.2 :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_block ΘV ΘW, iSup_block_eq_top ΘV ΘW hV hW⟩

/-- **`prop:tensor-eigen`** (direct sum in each generalized eigenspace). The generalized
`λ`-eigenspace of `Θ` is the internal direct sum of the blocks with `ρ + ρ' = λ`. -/
theorem isInternal_block_maxGenEigenspace [DecidableEq K] (ΘV : Module.End K V)
    (ΘW : Module.End K W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) (lam : K) :
    DirectSum.IsInternal fun p : {p : K × K // p.1 + p.2 = lam} =>
      (block ΘV ΘW p.1.1 p.1.2).comap ((tensorSum ΘV ΘW).maxGenEigenspace lam).subtype := by
  have hE : (tensorSum ΘV ΘW).maxGenEigenspace lam =
      ⨆ p ∈ {p : K × K | p.1 + p.2 = lam}, block ΘV ΘW p.1 p.2 := by
    rw [maxGenEigenspace_tensorSum_eq ΘV ΘW hV hW lam]; rfl
  rw [hE]
  exact DirectSum.isInternal_biSup_submodule_of_iSupIndep
    (A := fun p : K × K => block ΘV ΘW p.1 p.2)
    {p | p.1 + p.2 = lam} ((iSupIndep_block ΘV ΘW).comp Subtype.val_injective)

/-- The block is the image of `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}`, which embeds (over a field). -/
noncomputable def blockEquiv (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    (ΘV.maxGenEigenspace ρ ⊗[K] ΘW.maxGenEigenspace ρ') ≃ₗ[K] block ΘV ΘW ρ ρ' :=
  LinearEquiv.ofInjective _ (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _)

/-- Each block is `Θ`-stable. -/
theorem mapsTo_block (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K) :
    Set.MapsTo (tensorSum ΘV ΘW) (block ΘV ΘW ρ ρ') (block ΘV ΘW ρ ρ') := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    refine ⟨⟨ΘV x, Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl ΘV) ρ x.2⟩ ⊗ₜ y +
      x ⊗ₜ ⟨ΘW y, Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl ΘW) ρ' y.2⟩, ?_⟩
    simp [tensorSum, TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha; obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, ha', hb', map_add, map_add]⟩

/-- A block of finite-dimensional generalized eigenspaces is finite-dimensional. -/
instance (ΘV : Module.End K V) (ΘW : Module.End K W) (ρ ρ' : K)
    [FiniteDimensional K (ΘV.maxGenEigenspace ρ)] [FiniteDimensional K (ΘW.maxGenEigenspace ρ')] :
    FiniteDimensional K (block ΘV ΘW ρ ρ') :=
  LinearEquiv.finiteDimensional (blockEquiv ΘV ΘW ρ ρ')

end WeilRH.Spectral

namespace WeilRH.Spectral
universe uK u
variable {K : Type uK} [Field K]
variable {V W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **`prop:tensor-eigen`** (dimension formula). If `V` and `W` are spanned by their generalized
eigenspaces, `dim (V ⊗ W)_{Θ∼λ} = Σ_{ρ+ρ'=λ} m_V(ρ) m_W(ρ')`, as cardinals: the sum may be
infinite (the manuscript's remark after the proposition), so `Module.rank` is used. `V` and `W`
share a universe so that the products need no `Cardinal.lift`. -/
theorem rank_maxGenEigenspace_tensorSum (ΘV : Module.End K V) (ΘW : Module.End K W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) (lam : K) :
    Cardinal.lift.{uK} (Module.rank K ((tensorSum ΘV ΘW).maxGenEigenspace lam)) =
      Cardinal.sum fun p : {p : K × K // p.1 + p.2 = lam} =>
        Module.rank K (ΘV.maxGenEigenspace p.1.1) * Module.rank K (ΘW.maxGenEigenspace p.1.2) := by
  classical
  let s : Set (K × K) := {p | p.1 + p.2 = lam}
  let A : K × K → Submodule K (V ⊗[K] W) := fun p => block ΘV ΘW p.1 p.2
  have hE : (tensorSum ΘV ΘW).maxGenEigenspace lam = ⨆ p ∈ s, A p := by
    rw [maxGenEigenspace_tensorSum_eq ΘV ΘW hV hW lam]; rfl
  have hint := DirectSum.isInternal_biSup_submodule_of_iSupIndep (A := A) s
    ((iSupIndep_block ΘV ΘW).comp Subtype.val_injective)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint
  have h1 := e.lift_rank_eq
  rw [rank_directSum] at h1
  rw [hE]
  have h2 : ∀ p : s, Module.rank K ((A p).comap (⨆ i ∈ s, A i).subtype) =
      Module.rank K (ΘV.maxGenEigenspace p.1.1) * Module.rank K (ΘW.maxGenEigenspace p.1.2) := by
    intro p
    rw [(Submodule.comapSubtypeEquivOfLe (le_biSup A p.2)).rank_eq,
      ← (blockEquiv ΘV ΘW p.1.1 p.1.2).rank_eq, rank_tensorProduct']
  simp only [h2] at h1
  rw [Cardinal.lift_id', Cardinal.lift_umax] at h1
  exact h1.symm

end WeilRH.Spectral

namespace WeilRH.Spectral
universe u

variable {V W : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `spec Θ = {ρ : V_{Θ∼ρ} ≠ 0}` (`def:spectral-core` (b)). -/
def spec (Θ : Module.End ℂ V) : Set ℂ := {ρ | Θ.maxGenEigenspace ρ ≠ ⊥}

/-- **`def:spectral-core` (b)**: `(V, Θ)` is a spectral core if `V` is the sum of the generalized
eigenspaces `V_{Θ∼ρ}`, each is finite-dimensional, and `spec Θ` has no accumulation point in `ℂ`.
The sum is automatically direct (`Module.End.independent_maxGenEigenspace`), so only spanning is
recorded. -/
structure SpectralCore (Θ : Module.End ℂ V) : Prop where
  /-- `V` is the sum of its generalized eigenspaces. -/
  iSup_eq_top : ⨆ ρ, Θ.maxGenEigenspace ρ = ⊤
  /-- Each generalized eigenspace is finite-dimensional. -/
  finiteDimensional : ∀ ρ, FiniteDimensional ℂ (Θ.maxGenEigenspace ρ)
  /-- `spec Θ` has no finite accumulation point. -/
  noAccPt : ∀ z : ℂ, ¬ AccPt z (Filter.principal (spec Θ))

/-- The multiplicity `m(ρ) = dim V_{Θ∼ρ}` (`def:spectral-core` (c)). -/
noncomputable def mult (Θ : Module.End ℂ V) (ρ : ℂ) : ℕ := Module.finrank ℂ (Θ.maxGenEigenspace ρ)

/-- A block with `ρ ∉ spec Θ_V` is zero. -/
lemma block_eq_bot_of_left (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) {ρ : ℂ} (ρ' : ℂ)
    (h : ΘV.maxGenEigenspace ρ = ⊥) : block ΘV ΘW ρ ρ' = ⊥ := by
  rw [eq_bot_iff]; rintro _ ⟨z, rfl⟩
  have : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hx : x = 0 := Subtype.ext (by simpa [h] using x.2)
      simp [hx]
    | add a b ha hb => rw [ha, hb, add_zero]
  simp [this]

/-- A block with `ρ' ∉ spec Θ_W` is zero. -/
lemma block_eq_bot_of_right (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) (ρ : ℂ) {ρ' : ℂ}
    (h : ΘW.maxGenEigenspace ρ' = ⊥) : block ΘV ΘW ρ ρ' = ⊥ := by
  rw [eq_bot_iff]; rintro _ ⟨z, rfl⟩
  have : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hy : y = 0 := Subtype.ext (by simpa [h] using y.2)
      simp [hy]
    | add a b ha hb => rw [ha, hb, add_zero]
  simp [this]


/-- The pairs `(ρ, ρ') ∈ spec Θ_V × spec Θ_W` with `ρ + ρ' = λ`. -/
def pairs (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W) (lam : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 + p.2 = lam ∧ p.1 ∈ spec ΘV ∧ p.2 ∈ spec ΘW}

/-- Only pairs in `spec Θ_V × spec Θ_W` contribute to `(V ⊗ W)_{Θ∼λ}`. -/
theorem maxGenEigenspace_tensorSum_eq_pairs (ΘV : Module.End ℂ V) (ΘW : Module.End ℂ W)
    (hV : ⨆ ρ, ΘV.maxGenEigenspace ρ = ⊤) (hW : ⨆ ρ', ΘW.maxGenEigenspace ρ' = ⊤) (lam : ℂ) :
    (tensorSum ΘV ΘW).maxGenEigenspace lam = ⨆ p ∈ pairs ΘV ΘW lam, block ΘV ΘW p.1 p.2 := by
  rw [maxGenEigenspace_tensorSum_eq ΘV ΘW hV hW lam]
  apply le_antisymm
  · refine iSup₂_le fun p hp => ?_
    by_cases h1 : p.1 ∈ spec ΘV
    · by_cases h2 : p.2 ∈ spec ΘW
      · exact le_biSup (fun p : ℂ × ℂ => block ΘV ΘW p.1 p.2) (⟨hp, h1, h2⟩ : p ∈ pairs ΘV ΘW lam)
      · rw [block_eq_bot_of_right ΘV ΘW _ (not_not.1 h2)]; exact bot_le
    · rw [block_eq_bot_of_left ΘV ΘW _ (not_not.1 h1)]; exact bot_le
  · exact iSup₂_le fun p hp => le_biSup (fun p : ℂ × ℂ => block ΘV ΘW p.1 p.2) hp.1

/-- **`prop:tensor-eigen`** (dimension formula, finite case). For spectral cores, if only finitely
many pairs `(ρ, ρ') ∈ spec Θ_V × spec Θ_W` have `ρ + ρ' = λ`, then `(V ⊗ W)_{Θ∼λ}` is
finite-dimensional and `dim (V ⊗ W)_{Θ∼λ} = Σ_{ρ+ρ'=λ} m_V(ρ) m_W(ρ')`. The finiteness hypothesis
is not implied by the spectral-core conditions (the remark after the proposition and
`thm:kun-square`); without it see `rank_maxGenEigenspace_tensorSum`. -/
theorem finrank_maxGenEigenspace_tensorSum {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}
    (hV : SpectralCore ΘV) (hW : SpectralCore ΘW) (lam : ℂ) (hfin : (pairs ΘV ΘW lam).Finite) :
    FiniteDimensional ℂ ((tensorSum ΘV ΘW).maxGenEigenspace lam) ∧
      Module.finrank ℂ ((tensorSum ΘV ΘW).maxGenEigenspace lam) =
        ∑ p ∈ hfin.toFinset, mult ΘV p.1 * mult ΘW p.2 := by
  classical
  have := hV.finiteDimensional; have := hW.finiteDimensional
  set S := hfin.toFinset
  let A : ℂ × ℂ → Submodule ℂ (V ⊗[ℂ] W) := fun p => block ΘV ΘW p.1 p.2
  have hE : (tensorSum ΘV ΘW).maxGenEigenspace lam = ⨆ p ∈ (S : Set (ℂ × ℂ)), A p := by
    rw [maxGenEigenspace_tensorSum_eq_pairs ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top lam,
      hfin.coe_toFinset]
  have hint := DirectSum.isInternal_biSup_submodule_of_iSupIndep (A := A) (S : Set (ℂ × ℂ))
    ((iSupIndep_block ΘV ΘW).comp Subtype.val_injective)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint
  have hfd : ∀ p : (S : Set (ℂ × ℂ)), FiniteDimensional ℂ
      ((A p).comap (⨆ i ∈ (S : Set (ℂ × ℂ)), A i).subtype) := fun p =>
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (le_biSup A p.2)).symm
  have hrk : ∀ p : (S : Set (ℂ × ℂ)), Module.finrank ℂ
      ((A p).comap (⨆ i ∈ (S : Set (ℂ × ℂ)), A i).subtype) = mult ΘV p.1.1 * mult ΘW p.1.2 := by
    intro p
    rw [(Submodule.comapSubtypeEquivOfLe (le_biSup A p.2)).finrank_eq,
      ← (blockEquiv ΘV ΘW p.1.1 p.1.2).finrank_eq, Module.finrank_tensorProduct]
    rfl
  rw [hE]
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_directSum]
  simp only [hrk]
  exact Finset.sum_coe_sort S (fun p => mult ΘV p.1 * mult ΘW p.2)

/-- **`prop:tensor-eigen`** for spectral cores: `V ⊗ W` is the direct sum of the finite-dimensional
`Θ`-stable blocks `V_{Θ∼ρ} ⊗ W_{Θ∼ρ'}`, each in the generalized `(ρ + ρ')`-eigenspace; each
`(V ⊗ W)_{Θ∼λ}` is the direct sum of the blocks with `ρ + ρ' = λ`; and its dimension is
`Σ_{ρ+ρ'=λ} m_V(ρ) m_W(ρ')` as a cardinal. The discreteness clause of `SpectralCore` is not used. -/
theorem SpectralCore.tensor_eigen {ΘV : Module.End ℂ V} {ΘW : Module.End ℂ W}
    (hV : SpectralCore ΘV) (hW : SpectralCore ΘW) :
    DirectSum.IsInternal (fun p : ℂ × ℂ => block ΘV ΘW p.1 p.2) ∧
    (∀ ρ ρ', FiniteDimensional ℂ (block ΘV ΘW ρ ρ')) ∧
    (∀ ρ ρ', Set.MapsTo (tensorSum ΘV ΘW) (block ΘV ΘW ρ ρ') (block ΘV ΘW ρ ρ')) ∧
    (∀ ρ ρ', block ΘV ΘW ρ ρ' ≤ (tensorSum ΘV ΘW).maxGenEigenspace (ρ + ρ')) ∧
    (∀ lam, DirectSum.IsInternal fun p : {p : ℂ × ℂ // p.1 + p.2 = lam} =>
      (block ΘV ΘW p.1.1 p.1.2).comap ((tensorSum ΘV ΘW).maxGenEigenspace lam).subtype) ∧
    (∀ lam, Module.rank ℂ ((tensorSum ΘV ΘW).maxGenEigenspace lam) =
      Cardinal.sum fun p : {p : ℂ × ℂ // p.1 + p.2 = lam} =>
        Module.rank ℂ (ΘV.maxGenEigenspace p.1.1) * Module.rank ℂ (ΘW.maxGenEigenspace p.1.2)) := by
  classical
  have := hV.finiteDimensional; have := hW.finiteDimensional
  refine ⟨isInternal_block ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top, fun _ _ => inferInstance,
    mapsTo_block ΘV ΘW, block_le ΘV ΘW,
    isInternal_block_maxGenEigenspace ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top, fun lam => ?_⟩
  simpa using rank_maxGenEigenspace_tensorSum ΘV ΘW hV.iSup_eq_top hW.iSup_eq_top lam

/-! ### Transport along a linear isomorphism -/

/-- A linear isomorphism `e` with `Θ' ∘ e = e ∘ Θ` maps `V_{Θ∼σ}` onto `W_{Θ'∼σ}`. -/
theorem map_maxGenEigenspace_of_equiv {V' W' : Type*} [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W'] [Module ℂ W'] {Θ : Module.End ℂ V'} {Θ' : Module.End ℂ W'}
    (e : V' ≃ₗ[ℂ] W') (he : ∀ x, Θ' (e x) = e (Θ x)) (σ : ℂ) :
    (Θ.maxGenEigenspace σ).map (e : V' →ₗ[ℂ] W') = Θ'.maxGenEigenspace σ := by
  have h1 : Θ'.comp (e : V' →ₗ[ℂ] W') = (e : V' →ₗ[ℂ] W').comp Θ := LinearMap.ext he
  have h2 : Θ.comp (e.symm : W' →ₗ[ℂ] V') = (e.symm : W' →ₗ[ℂ] V').comp Θ' := by
    ext y; simpa using (congrArg e.symm (he (e.symm y))).symm
  refine le_antisymm (Module.End.map_genEigenspace_le _ h1 σ ⊤) ?_
  intro y hy
  exact ⟨e.symm y, Module.End.map_genEigenspace_le _ h2 σ ⊤ ⟨y, hy, rfl⟩, by simp⟩

/-- The spectral-core condition transfers along a linear isomorphism intertwining the operators. -/
theorem SpectralCore.of_equiv {V' W' : Type*} [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W'] [Module ℂ W'] {Θ : Module.End ℂ V'} {Θ' : Module.End ℂ W'}
    (hΘ : SpectralCore Θ) (e : V' ≃ₗ[ℂ] W') (he : ∀ x, Θ' (e x) = e (Θ x)) :
    SpectralCore Θ' where
  iSup_eq_top := by
    have := congrArg (Submodule.map (e : V' →ₗ[ℂ] W')) hΘ.iSup_eq_top
    rw [Submodule.map_iSup, Submodule.map_top, LinearEquiv.range] at this
    simpa [map_maxGenEigenspace_of_equiv e he] using this
  finiteDimensional σ := by
    have := hΘ.finiteDimensional σ
    rw [← map_maxGenEigenspace_of_equiv e he]
    exact LinearEquiv.finiteDimensional (e.submoduleMap _)
  noAccPt z := by
    have hs : spec Θ' = spec Θ := by
      ext σ
      simp only [spec, Set.mem_ofPred_eq, ← map_maxGenEigenspace_of_equiv e he, ne_eq]
      rw [Submodule.map_eq_bot_iff (e := e)]
    rw [hs]; exact hΘ.noAccPt z

end WeilRH.Spectral
