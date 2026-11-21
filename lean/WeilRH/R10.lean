/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.HilbertSelfAdjoint

/-!
# An abstract Hilbert isomorphism carries no spectral information (`prop:R10`)

Source: `latex/notes.tex`, `prop:R10` and its three proofs.

Let `H₁, H₂` be separable infinite-dimensional complex Hilbert spaces and `(λ_n)`, `(μ_n)` real
sequences with `|λ_n| → ∞`, `|μ_n| → ∞`. Then
1. there is a unitary `H₁ → H₂` (`exists_unitary`);
2. `diag(λ_n)` and `diag(μ_n)` are self-adjoint with pure point spectrum and
   `dim ker(A - x) = #{n | λ_n = x}` (`diag_spectral`);
3. if these counts differ at some `x`, no bounded linear bijection `W` with `W D(A₁) = D(A₂)` and
   `W A₁ = A₂ W` exists (`not_exists_intertwiner`).

## Encoding

* "Separable infinite-dimensional" is encoded by a Hilbert basis indexed by `ℕ`, which such a space
  has; the source's proof starts by choosing one.
* `eigSub A x` is the eigenspace `{v ∈ D(A) | A v = x v}` of a partially defined operator, as a
  subspace of `H`.
* `diag(λ_n)` is round 33's `Hilbert.Diag.op` on its maximal domain; "pure point spectrum" is its
  `Diag.spectral_clause` (every `λ_n` an eigenvalue with finite-dimensional eigenspace, `A - μ`
  bijective from the domain for `μ ∉ {λ_n}`).
* In (iii) boundedness of `W` is kept as in the source; the proof uses only that `W` is a linear
  bijection.
-/

open Filter Topology

namespace WeilRH.R10

/-! ### Eigenspaces of partially defined operators -/

section Eig

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The eigenspace `{v ∈ D(A) | A v = x v}` of a partially defined operator, as a subspace. -/
def eigSub (A : H →ₗ.[ℂ] H) (x : ℂ) : Submodule ℂ H :=
  (LinearMap.ker (A.toFun - x • A.domain.subtype)).map A.domain.subtype

theorem mem_eigSub (A : H →ₗ.[ℂ] H) (x : ℂ) (v : H) :
    v ∈ eigSub A x ↔ ∃ hv : v ∈ A.domain, A ⟨v, hv⟩ = x • v := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    have := sub_eq_zero.1 (LinearMap.mem_ker.1 hw)
    simpa using this
  · rintro ⟨hv, h⟩
    refine ⟨⟨v, hv⟩, LinearMap.mem_ker.2 (sub_eq_zero.2 ?_), rfl⟩
    simpa using h

end Eig

/-! ### (iii) Intertwiners preserve eigenspaces -/

section Intertwine

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- A linear bijection `W` with `W D(A₁) = D(A₂)` and `W A₁ = A₂ W` maps each eigenspace of `A₁`
onto the eigenspace of `A₂` for the same eigenvalue (the proof of `prop:R10` (iii)). -/
theorem map_eigSub (A₁ : H₁ →ₗ.[ℂ] H₁) (A₂ : H₂ →ₗ.[ℂ] H₂) (W : H₁ ≃ₗ[ℂ] H₂)
    (hdom : A₁.domain.map (W : H₁ →ₗ[ℂ] H₂) = A₂.domain)
    (hint : ∀ (v : A₁.domain) (w : A₂.domain), (w : H₂) = W v → A₂ w = W (A₁ v)) (x : ℂ) :
    (eigSub A₁ x).map (W : H₁ →ₗ[ℂ] H₂) = eigSub A₂ x := by
  ext u
  simp only [Submodule.mem_map, mem_eigSub]
  constructor
  · rintro ⟨v, ⟨hv, hAv⟩, rfl⟩
    have hWv : (W : H₁ →ₗ[ℂ] H₂) v ∈ A₂.domain := hdom ▸ Submodule.mem_map_of_mem hv
    refine ⟨hWv, ?_⟩
    rw [hint ⟨v, hv⟩ ⟨_, hWv⟩ rfl, hAv, map_smul]
    rfl
  · rintro ⟨hu, hAu⟩
    rw [← hdom] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    refine ⟨v, ⟨hv, ?_⟩, hvu⟩
    apply W.injective
    have h := hint ⟨v, hv⟩ ⟨u, hdom ▸ ⟨v, hv, hvu⟩⟩ hvu.symm
    rw [map_smul, ← h, hAu]
    exact congrArg (x • ·) hvu.symm

/-- Equal eigenspace dimensions under an intertwining linear bijection. -/
theorem finrank_eigSub_eq (A₁ : H₁ →ₗ.[ℂ] H₁) (A₂ : H₂ →ₗ.[ℂ] H₂) (W : H₁ ≃ₗ[ℂ] H₂)
    (hdom : A₁.domain.map (W : H₁ →ₗ[ℂ] H₂) = A₂.domain)
    (hint : ∀ (v : A₁.domain) (w : A₂.domain), (w : H₂) = W v → A₂ w = W (A₁ v)) (x : ℂ) :
    Module.finrank ℂ (eigSub A₁ x) = Module.finrank ℂ (eigSub A₂ x) := by
  rw [← map_eigSub A₁ A₂ W hdom hint x]
  exact (LinearEquiv.finrank_map_eq W (eigSub A₁ x)).symm

end Intertwine

/-! ### (ii) Diagonal operators -/

section Diag

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `|λ_n| → ∞` makes every bounded set of indices finite. -/
theorem finite_le_of_tendsto {lam : ℕ → ℝ} (hlam : Tendsto (fun n => |lam n|) atTop atTop)
    (R : ℝ) : {n | |lam n| ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlam.eventually_gt_atTop R)
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra h
  exact absurd (hN n (not_lt.1 h)) (not_lt.2 hn)

theorem finite_eq_of_tendsto {lam : ℕ → ℝ} (hlam : Tendsto (fun n => |lam n|) atTop atTop)
    (μ : ℂ) : {k | (lam k : ℂ) = μ}.Finite := by
  refine (finite_le_of_tendsto hlam ‖μ‖).subset fun k hk => ?_
  change (lam k : ℂ) = μ at hk
  change |lam k| ≤ ‖μ‖
  rw [← hk, Complex.norm_real, Real.norm_eq_abs]

/-- `|λ_n| → ∞` makes `{λ_n}` discrete in `ℂ`. -/
theorem not_accPt_of_tendsto {lam : ℕ → ℝ} (hlam : Tendsto (fun n => |lam n|) atTop atTop)
    (z : ℂ) : ¬ AccPt z (Filter.principal (Set.range fun k => (lam k : ℂ))) := by
  rw [accPt_iff_nhds]
  push Not
  set F := finite_le_of_tendsto hlam (‖z‖ + 1)
  set T : Set ℂ := (fun k => (lam k : ℂ)) '' {n | |lam n| ≤ ‖z‖ + 1} \ {z}
  have hT : T.Finite := (F.image _).sdiff
  refine ⟨Metric.ball z 1 ∩ Tᶜ, Filter.inter_mem (Metric.ball_mem_nhds z one_pos)
    (hT.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl), ?_⟩
  rintro y ⟨⟨hball, hTc⟩, k, rfl⟩
  by_contra hne
  apply hTc
  refine ⟨⟨k, ?_, rfl⟩, hne⟩
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have h1 : ‖(lam k : ℂ)‖ ≤ ‖(lam k : ℂ) - z‖ + ‖z‖ := by
    simpa using norm_add_le ((lam k : ℂ) - z) z
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  show |lam k| ≤ ‖z‖ + 1
  linarith

omit [CompleteSpace H] in
/-- The eigenspace of `diag(τ_k)` for `μ` is the span of the `b_k` with `τ_k = μ`. -/
theorem eigSub_op_eq_span {ι : Type*} (b : HilbertBasis ι ℂ H) (τ : ι → ℝ) {μ : ℂ}
    (hfin : {k | (τ k : ℂ) = μ}.Finite) :
    eigSub (Hilbert.Diag.op b τ) μ = Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ}) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hv, h⟩ := (mem_eigSub _ _ _).1 hv
    exact Hilbert.Diag.mem_span_of_op_eq_smul b τ hfin ⟨v, hv⟩ h
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine (mem_eigSub _ _ _).2 ⟨Hilbert.Diag.basis_mem_domain b τ k, ?_⟩
    rw [Hilbert.Diag.op_basis, show (τ k : ℂ) = μ from hk]

omit [CompleteSpace H] in
/-- `dim ker(diag(τ_k) - μ) = #{k | τ_k = μ}`. -/
theorem finrank_eigSub_op {ι : Type*} (b : HilbertBasis ι ℂ H) (τ : ι → ℝ) {μ : ℂ}
    (hfin : {k | (τ k : ℂ) = μ}.Finite) :
    Module.finrank ℂ (eigSub (Hilbert.Diag.op b τ) μ) = Nat.card {k | (τ k : ℂ) = μ} := by
  classical
  have := hfin.fintype
  rw [eigSub_op_eq_span b τ hfin, Set.image_eq_range]
  exact (finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)).trans
    Nat.card_eq_fintype_card.symm

/-- **`prop:R10` (ii).** For `|λ_n| → ∞`, `A = diag(λ_n)` on its maximal domain is self-adjoint,
has pure point spectrum `{λ_n}` (round 33's spectral clause), and `dim ker(A - x) = #{n | λ_n = x}`
for every real `x`. -/
theorem diag_spectral (b : HilbertBasis ℕ ℂ H) (lam : ℕ → ℝ)
    (hlam : Tendsto (fun n => |lam n|) atTop atTop) :
    IsSelfAdjoint (Hilbert.Diag.op b lam) ∧
    ((∀ k, Hilbert.Diag.op b lam ⟨b k, Hilbert.Diag.basis_mem_domain b lam k⟩ =
        (lam k : ℂ) • b k) ∧
      (∀ (μ : ℂ) (x : (Hilbert.Diag.op b lam).domain), Hilbert.Diag.op b lam x = μ • (x : H) →
        (x : H) ∈ Submodule.span ℂ (b '' {k | (lam k : ℂ) = μ})) ∧
      (∀ μ : ℂ, μ ∉ Set.range (fun k => (lam k : ℂ)) →
        ∀ y : H, ∃! x : (Hilbert.Diag.op b lam).domain,
          Hilbert.Diag.op b lam x - μ • (x : H) = y)) ∧
    ∀ x : ℝ, Module.finrank ℂ (eigSub (Hilbert.Diag.op b lam) x) = Nat.card {n | lam n = x} := by
  refine ⟨Hilbert.Diag.isSelfAdjoint b lam,
    Hilbert.Diag.spectral_clause b lam (finite_eq_of_tendsto hlam) (not_accPt_of_tendsto hlam),
    fun x => ?_⟩
  rw [finrank_eigSub_op b lam (finite_eq_of_tendsto hlam x)]
  simp only [Complex.ofReal_inj]

end Diag

/-! ### (i) and (iii) -/

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- **`prop:R10` (i).** Two Hilbert spaces with `ℕ`-indexed Hilbert bases are unitarily
isomorphic: send `e_n` to `f_n`. -/
theorem exists_unitary (b₁ : HilbertBasis ℕ ℂ H₁) (b₂ : HilbertBasis ℕ ℂ H₂) :
    Nonempty (H₁ ≃ₗᵢ[ℂ] H₂) :=
  ⟨b₁.repr.trans b₂.repr.symm⟩

/-- **`prop:R10` (iii).** If `#{n | λ_n = x} ≠ #{n | μ_n = x}` for some real `x`, there is no
bounded linear bijection `W : H₁ → H₂`, unitary or not, with `W D(A₁) = D(A₂)` and
`W A₁ = A₂ W` on `D(A₁)`, where `A₁ = diag(λ_n)` and `A₂ = diag(μ_n)`. -/
theorem not_exists_intertwiner (b₁ : HilbertBasis ℕ ℂ H₁) (b₂ : HilbertBasis ℕ ℂ H₂)
    (lam mu : ℕ → ℝ) (hlam : Tendsto (fun n => |lam n|) atTop atTop)
    (hmu : Tendsto (fun n => |mu n|) atTop atTop) {x : ℝ}
    (hx : Nat.card {n | lam n = x} ≠ Nat.card {n | mu n = x}) :
    ¬ ∃ W : H₁ →L[ℂ] H₂, Function.Bijective W ∧
      (Hilbert.Diag.op b₁ lam).domain.map (W : H₁ →ₗ[ℂ] H₂) = (Hilbert.Diag.op b₂ mu).domain ∧
      ∀ (v : (Hilbert.Diag.op b₁ lam).domain) (w : (Hilbert.Diag.op b₂ mu).domain),
        (w : H₂) = W v → Hilbert.Diag.op b₂ mu w = W (Hilbert.Diag.op b₁ lam v) := by
  rintro ⟨W, hbij, hdom, hint⟩
  set We : H₁ ≃ₗ[ℂ] H₂ := LinearEquiv.ofBijective (W : H₁ →ₗ[ℂ] H₂) hbij
  have h := finrank_eigSub_eq (Hilbert.Diag.op b₁ lam) (Hilbert.Diag.op b₂ mu) We hdom hint x
  rw [((diag_spectral b₁ lam hlam).2.2 x), ((diag_spectral b₂ mu hmu).2.2 x)] at h
  exact hx h

end WeilRH.R10
