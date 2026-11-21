import WeilRH.ArakelovZeta
import WeilRH.CompactifiedScheme

/-!
# Hodge data at infinity and Flach–Morin's `ζ(X_∞, s)` (FM path, step 1)

Round 52 of `lean/ROADMAP-arakelov.md`, the first step of the Flach–Morin path (decision D8).
Source: Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13
(2020), pp. 520–521, checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:

* the Hodge decomposition `H^i(X(ℂ), ℂ) ≅ ⊕_{p+q=i} H^{p,q}`, the Hodge numbers
  `h^{p,q} = dim H^{p,q}` and `h^{p,±} = dim (H^{p,p})^{F_∞ = ±(-1)^p}` (p. 520–521);
* `ζ(X_∞, s) := ∏_i L_∞(h^i(X_ℚ), s)^{(-1)^i}` (p. 521);
* formula (1), p. 521:
  `L_∞(h^i, s) = ∏_{p<q, p+q=i} Γ_ℂ(s-p)^{h^{p,q}} · ∏_{p=i/2} Γ_ℝ(s-p)^{h^{p,+}} Γ_ℝ(s-p+1)^{h^{p,-}}`,
  with `Γ_ℂ(s) = (2π)^{-s} Γ(s)`, `Γ_ℝ(s) = 2^{-1/2} π^{-s/2} Γ(s/2)` (`GammaCFM`, `GammaRFM`).

## Main results

* `involution_finrank_add`: for a linear involution `T` of a finite-dimensional complex space,
  `dim V^{T=1} + dim V^{T=-1} = dim V`.
* `HodgeDatum`: an interface for the real Hodge structure at infinity — finite-dimensional complex
  spaces `H p q` (the pieces `H^{p,q}`), zero for `p + q > top`, and `F_∞ : H^{p,q} ≃ H^{q,p}`, an
  involution (FM's `F_∞` is complex-linear on `H^i(X(ℂ),ℂ)` and exchanges `H^{p,q}` and `H^{q,p}`).
  `HodgeDatum.h`, `hplus`, `hminus` are FM's Hodge numbers; `h_symm`: `h^{p,q} = h^{q,p}`;
  `hplus_add_hminus`: `h^{p,+} + h^{p,-} = h^{p,p}`.
* `HodgeDatum.LInfty`, `HodgeDatum.zetaInfty`: FM's `L_∞(h^i, s)` and `ζ(X_∞, s)` from the datum.
* `Xbar.hodge K`: the Hodge datum of `X̄_K`: `H^{0,0} = ℂ^{Hom(K, ℂ)}` with `F_∞ f = f ∘ conj`,
  all other pieces `0`. Its Hodge numbers are **computed**: `Xbar.hplus_zero : h^{0,+} = r₁ + r₂`
  (the `F_∞`-invariant functions are those factoring through the infinite places) and
  `Xbar.hminus_zero : h^{0,-} = r₂` (from `involution_finrank_add` and `#Hom(K,ℂ) = r₁ + 2r₂`).
* `Xbar.zetaInfty_hodge`: **`ζ(X_∞, s)` computed from the Hodge datum equals round 50's
  `zetaInftyFM K s`**, so round 50's use of `h^{0,±}` as given exponents is now a theorem.
* `Xbar.pointsPullback_Finf`: on `ℂ^{X_∞}` with `X_∞ = X̄_K(ℂ)` (round 46), pullback along the
  scheme-theoretic `F_∞` corresponds to `f ↦ f ∘ conj` under `pointsEquiv`.

## Not formalized

* The datum is an **interface**: no Hodge decomposition is constructed from a complex manifold
  `X(ℂ)` (Mathlib has neither analytification nor Hodge theory). `X̄_K` is the honest instance
  because `X(ℂ)` is finite, so `H^*(X(ℂ),ℂ) = H^0 = ℂ^{X_∞} = H^{0,0}`.
* Compatibility of `F_∞` with complex conjugation of coefficients (the real structure) is not
  encoded; FM's formula only uses `F_∞` and the Hodge numbers.
-/

open NumberField NumberField.InfinitePlace Complex Module

noncomputable section

namespace WeilRH.Arakelov

/-! ### Linear involutions -/

section Involution

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The `c`-eigenspace `{x | T x = c • x}` of an endomorphism. -/
def eigenSub (T : V →ₗ[ℂ] V) (c : ℂ) : Submodule ℂ V := LinearMap.ker (T - c • LinearMap.id)

lemma mem_eigenSub {T : V →ₗ[ℂ] V} {c : ℂ} {x : V} : x ∈ eigenSub T c ↔ T x = c • x := by
  simp [eigenSub, sub_eq_zero]

/-- For a linear involution `T` of a finite-dimensional complex space,
`dim V^{T=1} + dim V^{T=-1} = dim V`. -/
theorem involution_finrank_add [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : ∀ x, T (T x) = x) :
    finrank ℂ (eigenSub T 1) + finrank ℂ (eigenSub T (-1)) = finrank ℂ V := by
  have hsup : eigenSub T 1 ⊔ eigenSub T (-1) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have h1 : (2⁻¹ : ℂ) • (x + T x) ∈ eigenSub T 1 := by
      rw [mem_eigenSub, map_smul, map_add, hT, one_smul, add_comm]
    have h2 : (2⁻¹ : ℂ) • (x - T x) ∈ eigenSub T (-1) := by
      rw [mem_eigenSub, map_smul, map_sub, hT, neg_one_smul, ← smul_neg, neg_sub]
    have hx : x = (2⁻¹ : ℂ) • (x + T x) + (2⁻¹ : ℂ) • (x - T x) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ x, smul_smul, inv_mul_cancel₀ two_ne_zero,
        one_smul]
    rw [hx]; exact Submodule.add_mem_sup h1 h2
  have hinf : eigenSub T 1 ⊓ eigenSub T (-1) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
    rw [mem_eigenSub, one_smul] at h1
    rw [mem_eigenSub, h1, neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul ℂ x] at h2
    exact (Submodule.mem_bot ℂ).2 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)
  have := Submodule.finrank_sup_add_finrank_inf_eq (eigenSub T 1) (eigenSub T (-1))
  rw [hsup, hinf, finrank_bot, add_zero, finrank_top] at this
  exact this.symm

end Involution

/-! ### The Hodge-datum interface -/

/-- **Hodge data at infinity** (FM pp. 520–521): finite-dimensional complex spaces `H p q`
standing for `H^{p,q} ⊂ H^{p+q}(X(ℂ), ℂ)`, vanishing above degree `top`, with the action of
`F_∞` (pullback by complex conjugation on `X(ℂ)`), a linear isomorphism `H^{p,q} ≃ H^{q,p}` that
is an involution. -/
structure HodgeDatum where
  /-- The Hodge pieces `H^{p,q}`. -/
  H : ℕ → ℕ → ModuleCat.{0} ℂ
  fin : ∀ p q, FiniteDimensional ℂ (H p q)
  /-- `H^{p,q} = 0` for `p + q > top` (`top = 2 dim X(ℂ)`). -/
  top : ℕ
  vanish : ∀ p q, top < p + q → finrank ℂ (H p q) = 0
  /-- `F_∞ : H^{p,q} → H^{q,p}`. -/
  Finf : ∀ p q, H p q ≃ₗ[ℂ] H q p
  Finf_Finf : ∀ p q (x : H p q), Finf q p (Finf p q x) = x

namespace HodgeDatum

variable (D : HodgeDatum)

instance (p q : ℕ) : FiniteDimensional ℂ (D.H p q) := D.fin p q

/-- `F_∞` on the middle piece `H^{p,p}`, as an endomorphism. -/
def FinfEnd (p : ℕ) : D.H p p →ₗ[ℂ] D.H p p := (D.Finf p p).toLinearMap

/-- The Hodge number `h^{p,q} = dim H^{p,q}`. -/
def h (p q : ℕ) : ℕ := finrank ℂ (D.H p q)

/-- `h^{p,+} = dim (H^{p,p})^{F_∞ = (-1)^p}` (FM p. 521). -/
def hplus (p : ℕ) : ℕ := finrank ℂ (eigenSub (D.FinfEnd p) ((-1) ^ p))

/-- `h^{p,-} = dim (H^{p,p})^{F_∞ = -(-1)^p}` (FM p. 521). -/
def hminus (p : ℕ) : ℕ := finrank ℂ (eigenSub (D.FinfEnd p) (-(-1) ^ p))

/-- Hodge symmetry `h^{p,q} = h^{q,p}`, from `F_∞ : H^{p,q} ≃ H^{q,p}`. -/
lemma h_symm (p q : ℕ) : D.h p q = D.h q p := (D.Finf p q).finrank_eq

/-- `h^{p,+} + h^{p,-} = h^{p,p}`. -/
lemma hplus_add_hminus (p : ℕ) : D.hplus p + D.hminus p = D.h p p := by
  have hT : ∀ x, D.FinfEnd p (D.FinfEnd p x) = x := fun x => D.Finf_Finf p p x
  show finrank ℂ (eigenSub (D.FinfEnd p) ((-1) ^ p)) +
      finrank ℂ (eigenSub (D.FinfEnd p) (-(-1) ^ p)) = finrank ℂ (D.H p p)
  rcases neg_one_pow_eq_or ℂ p with h | h
  · rw [h]; exact involution_finrank_add (D.FinfEnd p) hT
  · rw [h, neg_neg, add_comm]; exact involution_finrank_add (D.FinfEnd p) hT

/-- FM's archimedean factor, formula (1), p. 521:
`L_∞(h^i, s) = ∏_{p<q, p+q=i} Γ_ℂ(s-p)^{h^{p,q}} · [i even] Γ_ℝ(s-i/2)^{h^{i/2,+}} Γ_ℝ(s-i/2+1)^{h^{i/2,-}}`. -/
def LInfty (i : ℕ) (s : ℂ) : ℂ :=
  (∏ p ∈ (Finset.range (i + 1)).filter (fun p => 2 * p < i),
      GammaCFM (s - p) ^ D.h p (i - p)) *
    if Even i then GammaRFM (s - (i / 2 : ℕ)) ^ D.hplus (i / 2) *
        GammaRFM (s - (i / 2 : ℕ) + 1) ^ D.hminus (i / 2)
    else 1

/-- FM's `ζ(X_∞, s) = ∏_i L_∞(h^i, s)^{(-1)^i}` (p. 521). -/
def zetaInfty (s : ℂ) : ℂ := ∏ i ∈ Finset.range (D.top + 1), D.LInfty i s ^ ((-1 : ℤ) ^ i)

/-- In degree `0`, `L_∞(h^0, s) = Γ_ℝ(s)^{h^{0,+}} Γ_ℝ(s+1)^{h^{0,-}}`. -/
lemma LInfty_zero (s : ℂ) :
    D.LInfty 0 s = GammaRFM s ^ D.hplus 0 * GammaRFM (s + 1) ^ D.hminus 0 := by
  simp [LInfty]

end HodgeDatum

/-! ### The Hodge datum of `X̄_K` -/

namespace Xbar

variable (K : Type) [Field K] [NumberField K]

/-- `F_∞` on `H^0(X(ℂ), ℂ) = ℂ^{Hom(K,ℂ)}`: pullback along complex conjugation of embeddings. -/
def conjPullback : ((K →+* ℂ) → ℂ) →ₗ[ℂ] ((K →+* ℂ) → ℂ) where
  toFun f := f ∘ ComplexEmbedding.conjugate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField K] in
lemma conjPullback_conjPullback (f : (K →+* ℂ) → ℂ) : conjPullback K (conjPullback K f) = f := by
  funext φ
  show f (ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ)) = f φ
  congr 1; ext x; simp

/-- `conjPullback` as a linear equivalence (it is an involution). -/
def conjEquiv : ((K →+* ℂ) → ℂ) ≃ₗ[ℂ] ((K →+* ℂ) → ℂ) :=
  { conjPullback K with
    invFun := conjPullback K
    left_inv := conjPullback_conjPullback K
    right_inv := conjPullback_conjPullback K }

/-- The Hodge pieces of `X̄_K`: `H^{0,0} = ℂ^{Hom(K,ℂ)}`, all others `0`. -/
def hodgeH : ℕ → ℕ → ModuleCat.{0} ℂ
  | 0, 0 => ModuleCat.of ℂ ((K →+* ℂ) → ℂ)
  | _, _ => ModuleCat.of ℂ PUnit

/-- `F_∞` on the Hodge pieces of `X̄_K`. -/
def hodgeFinf : ∀ p q, hodgeH K p q ≃ₗ[ℂ] hodgeH K q p
  | 0, 0 => conjEquiv K
  | 0, _ + 1 => LinearEquiv.refl ℂ PUnit
  | _ + 1, 0 => LinearEquiv.refl ℂ PUnit
  | _ + 1, _ + 1 => LinearEquiv.refl ℂ PUnit

/-- **The Hodge datum of `X̄_K`** (`X(ℂ) = Hom(K,ℂ)` finite, so `H^* = H^0 = H^{0,0}`). -/
def hodge : HodgeDatum where
  H := hodgeH K
  fin p q := by
    match p, q with
    | 0, 0 => exact inferInstanceAs (FiniteDimensional ℂ ((K →+* ℂ) → ℂ))
    | 0, _ + 1 => exact inferInstanceAs (FiniteDimensional ℂ PUnit)
    | _ + 1, 0 => exact inferInstanceAs (FiniteDimensional ℂ PUnit)
    | _ + 1, _ + 1 => exact inferInstanceAs (FiniteDimensional ℂ PUnit)
  top := 0
  vanish p q h := by
    match p, q with
    | 0, 0 => exact absurd h (lt_irrefl 0)
    | 0, _ + 1 => exact finrank_zero_of_subsingleton (M := PUnit)
    | _ + 1, 0 => exact finrank_zero_of_subsingleton (M := PUnit)
    | _ + 1, _ + 1 => exact finrank_zero_of_subsingleton (M := PUnit)
  Finf := hodgeFinf K
  Finf_Finf p q x := by
    match p, q with
    | 0, 0 => exact conjPullback_conjPullback K x
    | 0, _ + 1 => rfl
    | _ + 1, 0 => rfl
    | _ + 1, _ + 1 => rfl

/-- Pullback of functions on the infinite places along `φ ↦ place φ`. -/
def placePullback : (InfinitePlace K → ℂ) →ₗ[ℂ] ((K →+* ℂ) → ℂ) where
  toFun g φ := g (InfinitePlace.mk φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField K] in
lemma placePullback_injective : Function.Injective (placePullback K) := by
  intro g g' h
  funext w
  have := congrFun h w.embedding
  simpa [placePullback, InfinitePlace.mk_embedding] using this

omit [NumberField K] in
/-- The `F_∞`-invariant functions on `Hom(K, ℂ)` are exactly those factoring through the
infinite places. -/
lemma range_placePullback :
    LinearMap.range (placePullback K) = eigenSub (conjPullback K) 1 := by
  ext f
  rw [mem_eigenSub, one_smul, LinearMap.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    funext φ; simp [placePullback, conjPullback, InfinitePlace.mk_conjugate_eq]
  · intro hf
    refine ⟨fun w => f w.embedding, ?_⟩
    funext φ
    simp only [placePullback, LinearMap.coe_mk, AddHom.coe_mk]
    rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk φ)) with h | h
    · rw [h]
    · conv_rhs => rw [← h]
      exact (congrFun hf _).symm

/-- **`h^{0,+} = r₁ + r₂`** for `X̄_K`: the `F_∞`-invariants of `ℂ^{Hom(K,ℂ)}`. -/
theorem finrank_invariants :
    finrank ℂ (eigenSub (conjPullback K) 1) = nrRealPlaces K + nrComplexPlaces K := by
  rw [← range_placePullback, LinearMap.finrank_range_of_inj (placePullback_injective K),
    finrank_fintype_fun_eq_card, card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- **`h^{0,-} = r₂`** for `X̄_K`: the `F_∞`-anti-invariants of `ℂ^{Hom(K,ℂ)}`. -/
theorem finrank_antiinvariants :
    finrank ℂ (eigenSub (conjPullback K) (-1)) = nrComplexPlaces K := by
  have h := involution_finrank_add (conjPullback K) (conjPullback_conjPullback K)
  rw [finrank_invariants, finrank_fintype_fun_eq_card, Embeddings.card,
    ← card_add_two_mul_card_eq_rank] at h
  omega

lemma hplus_zero : (hodge K).hplus 0 = nrRealPlaces K + nrComplexPlaces K := by
  show finrank ℂ (eigenSub (conjPullback K) ((-1) ^ 0)) = _
  rw [pow_zero]; exact finrank_invariants K

lemma hminus_zero : (hodge K).hminus 0 = nrComplexPlaces K := by
  show finrank ℂ (eigenSub (conjPullback K) (-(-1) ^ 0)) = _
  rw [pow_zero]; exact finrank_antiinvariants K

/-- **FM's `ζ(X_∞, s)` computed from the Hodge datum of `X̄_K` is round 50's `zetaInftyFM`.** -/
theorem zetaInfty_hodge (s : ℂ) : (hodge K).zetaInfty s = zetaInftyFM K s := by
  have htop : (hodge K).top = 0 := rfl
  rw [HodgeDatum.zetaInfty, htop, Finset.prod_range_one, pow_zero, zpow_one,
    HodgeDatum.LInfty_zero, hplus_zero, hminus_zero, zetaInftyFM]

/-- Nonvacuity: `H^{0,0}(X̄_K)` is nonzero, of dimension `[K : ℚ]`. -/
lemma h_zero_zero : (hodge K).h 0 0 = finrank ℚ K := by
  show finrank ℂ ((K →+* ℂ) → ℂ) = _
  rw [finrank_fintype_fun_eq_card, Embeddings.card]

/-- On `ℂ^{X_∞}` with `X_∞ = X̄_K(ℂ)`, pullback along the scheme-theoretic `F_∞` corresponds to
`conjPullback` under `pointsEquiv`. -/
theorem pointsPullback_Finf (f : (K →+* ℂ) → ℂ) (x : points (S K)) :
    (f ∘ pointsEquiv K) (Finf x) = (conjPullback K f ∘ pointsEquiv K) x := by
  simp [conjPullback, pointsEquiv_Finf]

end Xbar

end WeilRH.Arakelov
