import Mathlib
import WeilRH.CompactifiedZero

/-!
# `X̄_K` at negative twists `n < 0` (round 60)

Round 60 of `lean/ROADMAP-arakelov.md`, on the Flach–Morin path (decision D8). Source:
Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020),
checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:

* §3.1 (p. 523): "For `n < 0`, we have by definition `RΓ(X, R(n)) = 0` and `R(n)_D = (2iπ)^n R`,
  hence `RΓ_c(X, R(n)) = RΓ(G_R, X(C), (2iπ)^n R)[−1]`."
* §3.2 (p. 523): `RΓ(X̄, ℝ(n))` is the fibre of `RΓ(X, ℝ(n)) → τ_{<2n} RΓ_D`.
* Prop. 4.14 (p. 534), (i) and (iii).

## The groups

For `X = Spec 𝒪_K`, `X(ℂ) = Hom(K, ℂ)` is finite and `G_ℝ = ⟨conj⟩` has no higher cohomology
with real coefficients, so `H^*_D(X/ℝ, ℝ(n)) = H^0(G_ℝ, ((2πi)^n ℝ)^{X(ℂ)})`, in degree `0`.
Complex conjugation acts on `(2πi)^n ℝ ⊂ ℂ` by `(-1)^n`; identifying `(2πi)^n ℝ ≅ ℝ`, the
invariants are the functions `f : Hom(K, ℂ) → ℝ` with `f(σ̄) = (-1)^n f(σ)` (`twistInv K n`).
This is the parity subtlety: at a real place `σ = σ̄`, so `f(σ)` is free for `n` even and forced to
be `0` for `n` odd. Hence (`finrank_twistInv`)

  `dim H^0_D(X_K/ℝ, ℝ(n)) = r₁ + r₂` (`n` even), `= r₂` (`n` odd).

With `RΓ(X_K, ℝ(n)) = 0`, the fibre triangle gives `H^1_c(X_K, ℝ(n)) ≅ H^0_D`, all other `H^*_c`
zero (`negDatum`). Since `2n < 0`, `τ_{<2n} RΓ_D = 0`, the retraction is zero, and
`RΓ(X̄_K, ℝ(n))` is the fibre of `0 → 0`: **every `H^i(X̄_K, ℝ(n))` and every Weil–Arakelov group
`H^i_ar(X̄_K, ℝ̃(n))` vanishes** (`compactNeg`, `harNeg_subsingleton`).

## Comparison with FM Prop. 4.14 at `n < 0`: agreement

FM's (i) holds trivially (all `H^i_ar` vanish), and (iii) predicts
`ord_{s=n} ζ(X̄_K, s) = -dim CH^n(X̄_K) = 0`. We prove `ord_{s=n} ζ(X̄_K, s) = 0`
(`meromorphicOrderAt_zetaFMCont_neg`) from `ξ_K(n) = ξ_K(1-n)` and `ξ_K ≠ 0` on `Re s > 1`. The
latter is the Euler product of `ζ_K`, which Mathlib v4.34.1 lacks for `dedekindZeta`, so for
general `K` it is a hypothesis (`NonvanishingRight`); for `K = ℚ` it is proved
(`nonvanishingRight_rat`, from `riemannZeta_ne_zero_of_one_lt_re`). `fm414_neg` packages (i), (iii).

**The parity lives in the non-compact object.** The completed `ζ(X̄_K, s)` has order `0` at every
`n < 0`, matching `H^*(X̄_K) = 0`. The parity-dependent dimension `r₁[n even] + r₂` appears in
`H^1_c(X_K, ℝ(n))` (`finrank_negDatum_Hc_one`): it is the classical order of the *uncompleted*
`ζ_K(s)` at `s = n < 0` (the trivial zeros, from the poles of `Γ_ℝ(s)^{r₁}Γ_ℂ(s)^{r₂}`). That
order equation for `ζ_K` is **not** formalized here (it needs the orders of `1/Γ` at negative
integers); it is recorded as a consistency observation, not a theorem. There is no discrepancy
with FM, whose Prop. 4.14 concerns the compactified `X̄`.

## Status of the `X̄_K` part of the FM path

With rounds 54–60 the `X̄_K` part of FM §3 and Prop. 4.14 is complete for every integer twist:
`n ≥ 2` has all groups of `RΓ(X_K, ℝ(n))` outside our model (Borel's `K_{2n-1}` regulators; not
formalized), `n = 1` (rounds 55–58), `n = 0` (round 59), `n < 0` (this file). For `X(ℂ)` finite
the retraction is always forced; the next steps of the FM path need analytic input for
`dim X(ℂ) > 0` (e.g. `ℙⁿ_{𝒪_K}`), which Mathlib lacks.

## Fidelity

* Modelled by definition: `H^*(X_K, ℝ(n)) = 0` (FM's "by definition" for `n < 0`) and
  `H^0_D = ` the `G_ℝ`-invariants, with `(2πi)^n ℝ` identified with `ℝ` (so `conj` acts by
  `(-1)^n`); `G_ℝ`-cohomology in positive degree with real coefficients vanishes (standard,
  not formalized). Computed: `dim H^0_D`, exactness, `H^*_c`, `H^*(X̄_K)`, `H^*_ar`, and the order
  of `ζ(X̄_K, s)` at `s = n`.
* `ξ_K ≠ 0` on `Re s > 1` is a hypothesis except for `K = ℚ`.
* Cohomology groups only, as in rounds 54–59.
-/

set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.InfinitePlace Complex Topology Filter Module

noncomputable section

namespace WeilRH.Arakelov

namespace TwistNeg

variable (K : Type*) [Field K] [NumberField K]

/-! ## `H^0_D(X_K/ℝ, ℝ(n))`: the `G_ℝ`-invariants of `((2πi)^n ℝ)^{X(ℂ)}` -/

/-- The sign `(-1)^n` by which complex conjugation acts on `(2πi)^n ℝ`. -/
def sgn (n : ℤ) : ℝ := (-1) ^ n.natAbs

lemma sgn_of_even {n : ℤ} (h : Even n) : sgn n = 1 :=
  (Int.natAbs_even.2 h).neg_one_pow

lemma sgn_of_odd {n : ℤ} (h : ¬ Even n) : sgn n = -1 :=
  (Nat.not_even_iff_odd.1 (fun h' => h (Int.natAbs_even.1 h'))).neg_one_pow

/-- Pullback along complex conjugation of embeddings, on real-valued functions. -/
def conjR : ((K →+* ℂ) → ℝ) →ₗ[ℝ] ((K →+* ℂ) → ℝ) where
  toFun f := f ∘ ComplexEmbedding.conjugate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField K] in
lemma conjR_conjR (f : (K →+* ℂ) → ℝ) : conjR K (conjR K f) = f := by
  funext φ
  show f (ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ)) = f φ
  congr 1; ext x; simp

/-- The eigenspace `{f | f ∘ conj = c f}` of `conjR`. -/
def eig (c : ℝ) : Submodule ℝ ((K →+* ℂ) → ℝ) := LinearMap.ker (conjR K - c • LinearMap.id)

omit [NumberField K] in
lemma mem_eig {c : ℝ} {f : (K →+* ℂ) → ℝ} : f ∈ eig K c ↔ conjR K f = c • f := by
  simp [eig, sub_eq_zero]

/-- **`H^0_D(X_K/ℝ, ℝ(n))`** (FM §3.1): the functions `f : Hom(K, ℂ) → ℝ` with
`f(σ̄) = (-1)^n f(σ)`, i.e. the `G_ℝ`-invariants of `((2πi)^n ℝ)^{X(ℂ)}`. -/
abbrev twistInv (n : ℤ) : Submodule ℝ ((K →+* ℂ) → ℝ) := eig K (sgn n)

/-- `dim V^{T=1} + dim V^{T=-1} = dim V` for the involution `conjR`. -/
lemma finrank_eig_add :
    finrank ℝ (eig K 1) + finrank ℝ (eig K (-1)) = finrank ℝ ((K →+* ℂ) → ℝ) := by
  set T := conjR K
  have hT := conjR_conjR K
  have hsup : eig K 1 ⊔ eig K (-1) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have h1 : (2⁻¹ : ℝ) • (x + T x) ∈ eig K 1 := by
      rw [mem_eig, map_smul, map_add, hT, one_smul, add_comm]
    have h2 : (2⁻¹ : ℝ) • (x - T x) ∈ eig K (-1) := by
      rw [mem_eig, map_smul, map_sub, hT, neg_one_smul, ← smul_neg, neg_sub]
    have hx : x = (2⁻¹ : ℝ) • (x + T x) + (2⁻¹ : ℝ) • (x - T x) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ x, smul_smul, inv_mul_cancel₀ two_ne_zero,
        one_smul]
    rw [hx]; exact Submodule.add_mem_sup h1 h2
  have hinf : eig K 1 ⊓ eig K (-1) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
    rw [mem_eig, one_smul] at h1
    rw [mem_eig, h1, neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul ℝ x] at h2
    exact (Submodule.mem_bot ℝ).2 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)
  have := Submodule.finrank_sup_add_finrank_inf_eq (eig K 1) (eig K (-1))
  rw [hsup, hinf, finrank_bot, add_zero, finrank_top] at this
  exact this.symm

/-- Pullback of real functions on the infinite places along `φ ↦ place φ`. -/
def placePullbackR : (InfinitePlace K → ℝ) →ₗ[ℝ] ((K →+* ℂ) → ℝ) where
  toFun g φ := g (InfinitePlace.mk φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField K] in
lemma placePullbackR_injective : Function.Injective (placePullbackR K) := by
  intro g g' h
  funext w
  have := congrFun h w.embedding
  simpa [placePullbackR, InfinitePlace.mk_embedding] using this

omit [NumberField K] in
/-- The conjugation-invariant real functions on `Hom(K, ℂ)` are those factoring through the
infinite places. -/
lemma range_placePullbackR : LinearMap.range (placePullbackR K) = eig K 1 := by
  ext f
  rw [mem_eig, one_smul, LinearMap.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    funext φ; simp [placePullbackR, conjR, InfinitePlace.mk_conjugate_eq]
  · intro hf
    refine ⟨fun w => f w.embedding, ?_⟩
    funext φ
    simp only [placePullbackR, LinearMap.coe_mk, AddHom.coe_mk]
    rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk φ)) with h | h
    · rw [h]
    · conv_rhs => rw [← h]
      exact (congrFun hf _).symm

lemma finrank_eig_one : finrank ℝ (eig K 1) = nrRealPlaces K + nrComplexPlaces K := by
  rw [← range_placePullbackR, LinearMap.finrank_range_of_inj (placePullbackR_injective K),
    finrank_fintype_fun_eq_card, card_eq_nrRealPlaces_add_nrComplexPlaces]

lemma finrank_eig_neg_one : finrank ℝ (eig K (-1)) = nrComplexPlaces K := by
  have h := finrank_eig_add K
  rw [finrank_eig_one, finrank_fintype_fun_eq_card, Embeddings.card,
    ← card_add_two_mul_card_eq_rank] at h
  omega

/-- **The parity of the twist** (FM §3.1): `dim H^0_D(X_K/ℝ, ℝ(n)) = r₁ + r₂` for `n` even and
`r₂` for `n` odd. -/
theorem finrank_twistInv (n : ℤ) :
    finrank ℝ (twistInv K n) =
      if Even n then nrRealPlaces K + nrComplexPlaces K else nrComplexPlaces K := by
  by_cases h : Even n
  · simp only [h, ↓reduceIte]
    have e : twistInv K n = eig K 1 := by rw [twistInv, sgn_of_even h]
    exact (LinearEquiv.ofEq _ _ e).finrank_eq.trans (finrank_eig_one K)
  · simp only [h, ↓reduceIte]
    have e : twistInv K n = eig K (-1) := by rw [twistInv, sgn_of_odd h]
    exact (LinearEquiv.ofEq _ _ e).finrank_eq.trans (finrank_eig_neg_one K)

/-! ## The Deligne datum and the compactification at `n < 0` -/

variable (n : ℤ)

/-- **The `n < 0` Deligne datum of `X_K`** (FM §3.1): `H^*(X_K, ℝ(n)) = 0`,
`H^0_D = twistInv K n` in degree `0`, and `H^1_c = H^0_D` via the connecting map; all else `0`. -/
def negDatum :
    DeligneDatum ℝ (fun _ => PUnit) (fun i => degSub (twistInv K n) 0 i)
      (fun i => degSub (twistInv K n) 1 i) where
  reg _ := 0
  toMot _ := 0
  conn i := degMap LinearMap.id 0 1 i (i + 1) (fun h => by omega)
  exact_toMot _ := Subsingleton.elim _ _
  exact_reg i := by
    rw [LinearMap.range_zero]
    symm
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (by simpa using congrArg Subtype.val hx)
  exact_conn i := by
    rw [LinearMap.ker_zero, LinearMap.range_eq_top]
    intro z
    by_cases hi : i = 0
    · subst hi
      exact ⟨⟨z, mem_degSub_self 0 _⟩, rfl⟩
    · have hz : (z : twistInv K n) = 0 := eq_zero_of_mem_degSub (by omega) z.2
      exact ⟨0, Subtype.ext (by simp [hz])⟩

/-- `dim H^1_c(X_K, ℝ(n)) = r₁[n even] + r₂` — the parity-dependent group (non-compact). -/
theorem finrank_negDatum_Hc_one :
    finrank ℝ (degSub (twistInv K n) 1 1) =
      if Even n then nrRealPlaces K + nrComplexPlaces K else nrComplexPlaces K := by
  rw [LinearEquiv.finrank_eq ((LinearEquiv.ofEq _ _ (degSub_self _ 1)).trans
    Submodule.topEquiv), finrank_twistInv]

/-- **FM §3.2 at `n < 0` for `X̄_K`.** `2n < 0`, so `τ_{<2n} RΓ_D = 0`, the retraction is zero, and
`RΓ(X̄_K, ℝ(n))` is the fibre of `0 → 0`: all `H^i(X̄_K, ℝ(n))` vanish. -/
def compactNeg (hn : n < 0) :
    CompactifiedDatum ℝ (fun _ => PUnit) (fun i => degSub (twistInv K n) 0 i)
      (fun i => degSub (twistInv K n) 1 i) (fun _ => PUnit) (fun _ => PUnit) where
  toDeligneDatum := negDatum K n
  n := n
  adj _ := 0
  ret _ := 0
  ret_adj _ := Subsingleton.elim _ _
  adj_bijective i hi := by
    have : Subsingleton (degSub (twistInv K n) 0 i) := degSub_subsingleton _ (by omega)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩
  trunc_trivial _ _ := inferInstance
  toMotBar _ := 0
  connBar _ := 0
  exact_toMotBar _ := Subsingleton.elim _ _
  exact_regBar _ := Subsingleton.elim _ _
  exact_connBar _ := Subsingleton.elim _ _

omit [NumberField K] in
/-- The retraction at `n < 0` is zero. -/
theorem compactNeg_ret (hn : n < 0) (i : ℤ) : (compactNeg K n hn).ret i = 0 := rfl

/-- **The truncation is nontrivial at even `n < 0`**: `H^0_D ≠ 0` (it contains the constants on a
place), but `τ_{<2n}` kills it, so the adjunction is not surjective in degree `0`. -/
theorem compactNeg_adj_not_surjective (hn : n < 0) (he : Even n) :
    ¬ Function.Surjective ((compactNeg K n hn).adj 0) := by
  intro h
  have hpos : 0 < finrank ℝ (twistInv K n) := by
    simp only [finrank_twistInv, he, ↓reduceIte]
    have := card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  obtain ⟨w, hx⟩ := h ⟨v, mem_degSub_self 0 v⟩
  apply hv
  have h0 : ((⟨v, mem_degSub_self 0 v⟩ : degSub (twistInv K n) 0 0) : twistInv K n) = 0 := by
    rw [← hx]; rfl
  exact h0

/-! ## Weil–Arakelov groups at `n < 0` -/

/-- `H^i(X̄_K, ℝ(n))` for `n < 0`: zero in every degree. -/
abbrev hBarNeg : ℤ → Type := fun _ => PUnit

/-- **FM (2) at `n < 0`.** `H^i_ar(X̄_K, ℝ̃(n)) = H^i(X̄_K, ℝ(n)) ⊕ H^{i-1}(X̄_K, ℝ(n)) = 0`. -/
abbrev harNeg (i : ℤ) := WeilArakelov.Har hBarNeg i

theorem harNeg_subsingleton (i : ℤ) : Subsingleton (harNeg i) := instSubsingletonProd

theorem finrank_harNeg (i : ℤ) : finrank ℝ (harNeg i) = 0 := finrank_zero_of_subsingleton

end TwistNeg

/-! ## The order of `ζ(X̄_K, s)` at `s = n < 0` -/

namespace ZetaOrder

variable {K : Type*} [Field K] [NumberField K] {C : DedekindContinuation K}

/-- `ξ_K ≠ 0` on `Re s > 1` (from the Euler product of `ζ_K`; not in Mathlib v4.34.1 for
`dedekindZeta`). -/
def NonvanishingRight (P : C.SimplePoles) : Prop := ∀ s : ℂ, 1 < s.re → P.ξ s ≠ 0

/-- The analytic factor away from `0, 1`: `e^{a+bs} ξ_K(s) / (s (s - 1))`. -/
def gx (P : C.SimplePoles) (s : ℂ) : ℂ := exp (fmA K + fmB K * s) * P.ξ s / (s * (s - 1))

lemma analyticAt_gx (P : C.SimplePoles) {x : ℂ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    AnalyticAt ℂ (gx P) x := by
  have he : AnalyticAt ℂ (fun s => exp (fmA K + fmB K * s)) x := by
    have : Differentiable ℂ (fun s => exp (fmA K + fmB K * s)) := by fun_prop
    exact this.analyticAt x
  exact (he.mul (P.differentiable.analyticAt x)).div (analyticAt_id.mul (analyticAt_id.sub
    analyticAt_const)) (mul_ne_zero h0 (sub_ne_zero.2 h1))

/-- **`ord_{s=x} ζ(X̄_K, s) = 0`** for `x ≠ 0, 1` with `ξ_K(x) ≠ 0`. -/
theorem meromorphicOrderAt_zetaFMCont_of_ne (P : C.SimplePoles) {x : ℂ} (h0 : x ≠ 0)
    (h1 : x ≠ 1) (hx : P.ξ x ≠ 0) : meromorphicOrderAt (zetaFMCont K C) x = (0 : ℤ) := by
  have hev : ∀ᶠ s in 𝓝[≠] x, zetaFMCont K C s = (s - x) ^ (0 : ℤ) • gx P s := by
    have hn0 : ∀ᶠ s in 𝓝[≠] x, s ≠ 0 := nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)
    have hn1 : ∀ᶠ s in 𝓝[≠] x, s ≠ 1 := nhdsWithin_le_nhds (isOpen_ne.mem_nhds h1)
    filter_upwards [hn0, hn1] with s hs0 hs1
    rw [zetaFMCont_eq P s hs0 hs1, zpow_zero, one_smul, gx]
  have hmero : MeromorphicAt (fun s => (s - x) ^ (0 : ℤ) • gx P s) x :=
    ((MeromorphicAt.id x).sub (MeromorphicAt.const x x)).zpow 0 |>.smul
      (analyticAt_gx P h0 h1).meromorphicAt
  rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_eq_int_iff hmero]
  refine ⟨gx P, analyticAt_gx P h0 h1, ?_, Eventually.of_forall fun _ => rfl⟩
  have hs : x * (x - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  simp [gx, exp_ne_zero, hx, hs]

/-- **`ord_{s=n} ζ(X̄_K, s) = 0` for every integer `n < 0`**, from `ξ_K(n) = ξ_K(1 - n)` and
nonvanishing on `Re s > 1`. -/
theorem meromorphicOrderAt_zetaFMCont_neg (P : C.SimplePoles) (H : NonvanishingRight P)
    {n : ℤ} (hn : n < 0) : meromorphicOrderAt (zetaFMCont K C) (n : ℂ) = (0 : ℤ) := by
  have h0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne
  have h1 : (n : ℂ) ≠ 1 := by exact_mod_cast (by omega : n ≠ 1)
  refine meromorphicOrderAt_zetaFMCont_of_ne P h0 h1 ?_
  rw [← P.one_sub]
  apply H
  have : ((1 : ℂ) - n).re = 1 - n := by simp
  rw [this]
  have : (n : ℝ) < 0 := by exact_mod_cast hn
  linarith

/-- **For `K = ℚ` the nonvanishing is a theorem**: `ξ_ℚ = 2 completedXi`, and `ζ(s) ≠ 0` for
`Re s > 1`. -/
theorem nonvanishingRight_rat (C : DedekindContinuation ℚ) :
    NonvanishingRight (DedekindContinuation.SimplePoles.ofRat C) := by
  intro s hs h
  have h2 : completedXi s = 0 := by
    have : (2 : ℂ) * completedXi s = 0 := h
    simpa using this
  rw [completedXi_eq_zero_iff] at h2
  exact riemannZeta_ne_zero_of_one_lt_re hs h2.1

end ZetaOrder

namespace TwistNeg

variable {K : Type*} [Field K] [NumberField K]

/-- **FM Prop. 4.14 (i), (iii) at `n < 0` for `X̄_K`**: every `H^i_ar(X̄_K, ℝ̃(n))` vanishes, and
`ord_{s=n} ζ(X̄_K, s) = 0 = -dim H^{2n}_ar(X̄_K, ℝ̃(n))`. Assumes simple poles and `ξ_K ≠ 0` on
`Re s > 1`. -/
theorem fm414_neg {C : DedekindContinuation K} (P : C.SimplePoles)
    (H : ZetaOrder.NonvanishingRight P) {n : ℤ} (hn : n < 0) :
    (∀ i : ℤ, finrank ℝ (harNeg i) = 0) ∧
      meromorphicOrderAt (zetaFMCont K C) (n : ℂ) = (-(finrank ℝ (harNeg (2 * n)) : ℤ) : ℤ) := by
  refine ⟨finrank_harNeg, ?_⟩
  rw [ZetaOrder.meromorphicOrderAt_zetaFMCont_neg P H hn, finrank_harNeg]
  simp

/-- **`K = ℚ`, unconditional (beyond the continuation)**: FM Prop. 4.14 (iii) at every `n < 0`. -/
theorem fm414_neg_rat (C : DedekindContinuation ℚ) {n : ℤ} (hn : n < 0) :
    meromorphicOrderAt (zetaFMCont ℚ C) (n : ℂ) = (-(finrank ℝ (harNeg (2 * n)) : ℤ) : ℤ) :=
  (fm414_neg (DedekindContinuation.SimplePoles.ofRat C)
    (ZetaOrder.nonvanishingRight_rat C) hn).2

end TwistNeg

end WeilRH.Arakelov
