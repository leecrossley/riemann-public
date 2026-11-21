import WeilRH.HodgeInfty

/-!
# Hodge data of `ℙⁿ` over `𝓞_K` and Flach–Morin's `ζ(X_∞, s)` in all degrees (FM path, step 2)

Round 53 of `lean/ROADMAP-arakelov.md` (Flach–Morin path, decision D8). Source: Flach–Morin,
*Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020), pp. 520–521,
checked in the local PDF `refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:
the Hodge numbers `h^{p,q}`, `h^{p,±} = dim (H^{p,p})^{F_∞ = ±(-1)^p}`,
`ζ(X_∞, s) = ∏_i L_∞(h^i(X_ℚ), s)^{(-1)^i}` and formula (1) for `L_∞(h^i, s)`.

For `X = ℙⁿ_{𝓞_K}`, `X(ℂ) = ⊔_{σ : K → ℂ} ℙⁿ(ℂ)`, so `H^{2k}(X(ℂ), ℂ) = H^{k,k} = ℂ^{Hom(K,ℂ)}`
for `0 ≤ k ≤ n` and all other `H^{p,q}` vanish. Complex conjugation exchanges the copies
`σ ↔ σ̄` and acts on `H^{2k}(ℙⁿ(ℂ))` by `(-1)^k` (it reverses the orientation of `ℙ¹(ℂ)`), so
`F_∞ = (-1)^k · (f ↦ f ∘ conj)` on `H^{k,k}`. This sign is the standard topological fact used
in the proof of Theorem D of `ai/2026-10-31-conditional-dynamical-cohomology/report.md`; it is
**modelled**, not derived from an analytification of `ℙⁿ` (Mathlib has none).

## Main results

* `ProjSpace.hodge K n : HodgeDatum` — the Hodge datum of `ℙⁿ_{𝓞_K}`; pieces
  `W p q = ⊤ ⊂ ℂ^{Hom(K,ℂ)}` if `p = q ≤ n`, else `⊥`.
* `ProjSpace.h_diag` (`h^{k,k} = [K:ℚ]` for `k ≤ n`), `h_offdiag` (`h^{p,q} = 0`, `p ≠ q`),
  `hplus_eq` (`h^{k,+} = r₁ + r₂`), `hminus_eq` (`h^{k,-} = r₂`) for `k ≤ n` — **computed** from
  the `F_∞`-action: the sign `(-1)^k` in `F_∞` cancels the sign in FM's definition of `h^{k,±}`,
  so these are independent of the parity of `k`; `hplus_gt`, `hminus_gt`: both `0` for `k > n`.
* `ProjSpace.LInfty_eq`: `L_∞(h^i, s) = Γ_ℝ(s-k)^{r₁} Γ_ℂ(s-k)^{r₂}` if `i = 2k`, `k ≤ n`,
  and `1` otherwise (FM normalization; `GammaRFM_mul_add_one`).
* `ProjSpace.zetaInfty_eq`: **`ζ(X_∞, s) = ∏_{k=0}^n Γ_ℝ(s-k)^{r₁} Γ_ℂ(s-k)^{r₂}`**.
* `ProjSpace.zetaInfty_zero`: for `n = 0` this is round 50's `zetaInftyFM` (the `X̄_K` case).
* `ProjSpace.zetaFM_eq`: with `ζ(ℙⁿ_{𝓞_K}, s) := ∏_{k=0}^n ζ_K(s-k)` (**definitional**, see below),
  FM's `ζ(ℙ̄ⁿ, s) = ∏_{k=0}^n e^{a + b(s-k)} Λ_K(s-k)` for `Re s > n + 1`.

## Definitional / not formalized

* `zetaPn K n s := ∏_{k=0}^n dedekindZeta K (s - k)` is a **definition** of FM's
  `ζ(ℙⁿ_{𝓞_K}, s)`: the identity `ζ(ℙⁿ_{𝓞_K}, s) = ∏_k ζ_K(s-k)` comes from counting points of
  `ℙⁿ(𝔽_𝔭)`, and Mathlib v4.34.1 has neither Serre's `ζ(X, s)` for schemes nor the Euler
  product of `dedekindZeta`. Nothing is faked: the theorem is stated for this definition.
* The Hodge datum is an interface instance (see `HodgeInfty.lean`): the pieces and the sign of
  `F_∞` are modelled, not computed from `ℙⁿ(ℂ)`.
-/

open NumberField NumberField.InfinitePlace Complex Module

noncomputable section

namespace WeilRH.Arakelov

namespace ProjSpace

variable (K : Type) [Field K] [NumberField K] (n : ℕ)

/-- `ℂ^{Hom(K,ℂ)}`, the space carrying each `H^{k,k}` of `ℙⁿ_{𝓞_K}`. -/
abbrev Fun := (K →+* ℂ) → ℂ

/-- The Hodge piece `H^{p,q}` of `ℙⁿ_{𝓞_K}` inside `ℂ^{Hom(K,ℂ)}`: everything if `p = q ≤ n`,
zero otherwise. -/
def W (p q : ℕ) : Submodule ℂ (Fun K) := if p = q ∧ p ≤ n then ⊤ else ⊥

omit [NumberField K] in
lemma W_symm (p q : ℕ) : W K n p q = W K n q p := by
  unfold W
  by_cases h : p = q
  · subst h; rfl
  · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right (fun h' => h h'.1.symm)]

omit [NumberField K] in
lemma W_diag {k : ℕ} (hk : k ≤ n) : W K n k k = ⊤ := ite_eq_left ⟨rfl, hk⟩

omit [NumberField K] in
lemma W_offdiag {p q : ℕ} (h : p ≠ q) : W K n p q = ⊥ := ite_eq_right (fun h' => h h'.1)

omit [NumberField K] in
lemma W_gt {k : ℕ} (hk : n < k) : W K n k k = ⊥ := ite_eq_right (fun h' => by omega)

/-- `F_∞` on `H^{p,p}` before restriction: `(-1)^p · (f ↦ f ∘ conj)`. -/
def S (p : ℕ) : Fun K →ₗ[ℂ] Fun K := ((-1 : ℂ) ^ p) • Xbar.conjPullback K

omit [NumberField K] in
lemma S_apply (p : ℕ) (x : Fun K) : S K p x = ((-1 : ℂ) ^ p) • Xbar.conjPullback K x := rfl

omit [NumberField K] in
lemma S_mem {p q : ℕ} (x : Fun K) (hx : x ∈ W K n p q) : S K p x ∈ W K n q p := by
  rw [W_symm K n q p]
  unfold W at hx ⊢
  split_ifs at hx ⊢
  · exact Submodule.mem_top
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

/-- `F_∞ : H^{p,q} → H^{q,p}`. -/
def F (p q : ℕ) : W K n p q →ₗ[ℂ] W K n q p := (S K p).restrict (S_mem K n)

omit [NumberField K] in
lemma neg_one_pow_mul_self (p : ℕ) : ((-1 : ℂ) ^ p) * (-1) ^ p = 1 := by
  rw [← mul_pow]; norm_num

omit [NumberField K] in
lemma F_F (p q : ℕ) (x : W K n p q) : F K n q p (F K n p q x) = x := by
  apply Subtype.ext
  change S K q (S K p x) = x
  by_cases h : p = q
  · subst h
    rw [S_apply, S_apply, map_smul, Xbar.conjPullback_conjPullback, smul_smul,
      neg_one_pow_mul_self, one_smul]
  · have hx : (x : Fun K) = 0 :=
      (Submodule.mem_bot ℂ).1 ((W_offdiag K n h).le x.2)
    rw [hx, map_zero, map_zero]

/-- `F_∞ : H^{p,q} ≃ H^{q,p}`, an involution. -/
def Finf (p q : ℕ) : W K n p q ≃ₗ[ℂ] W K n q p :=
  { F K n p q with
    invFun := F K n q p
    left_inv := F_F K n p q
    right_inv := F_F K n q p }

/-- **The Hodge datum of `ℙⁿ_{𝓞_K}`**: `H^{k,k} = ℂ^{Hom(K,ℂ)}` (`0 ≤ k ≤ n`), other pieces `0`,
`F_∞ = (-1)^k (f ↦ f ∘ conj)`. -/
def hodge : HodgeDatum where
  H p q := ModuleCat.of ℂ (W K n p q)
  fin p q := inferInstanceAs (FiniteDimensional ℂ (W K n p q))
  top := 2 * n
  vanish p q h := by
    have hne : ¬ (p = q ∧ p ≤ n) := fun h' => by omega
    show finrank ℂ (W K n p q) = 0
    rw [W, ite_eq_right hne]
    exact finrank_bot ℂ _
  Finf := Finf K n
  Finf_Finf := F_F K n

/-! ### Hodge numbers -/

omit [NumberField K] in
/-- Eigenspaces of a restriction, transported to the ambient space. -/
lemma map_subtype_eigenSub {W' : Submodule ℂ (Fun K)} (T : W' →ₗ[ℂ] W')
    (S' : Fun K →ₗ[ℂ] Fun K) (hT : ∀ x, (T x : Fun K) = S' x) (c : ℂ) :
    (eigenSub T c).map W'.subtype = W' ⊓ eigenSub S' c := by
  ext x
  simp only [Submodule.mem_map, Submodule.subtype_apply, Submodule.mem_inf, mem_eigenSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [← hT, hy, Submodule.coe_smul]
  · rintro ⟨hxW, hx⟩
    refine ⟨⟨x, hxW⟩, Subtype.ext ?_, rfl⟩
    rw [hT, hx, Submodule.coe_smul]

omit [NumberField K] in
lemma finrank_eigenSub_restrict {W' : Submodule ℂ (Fun K)} (T : W' →ₗ[ℂ] W')
    (S' : Fun K →ₗ[ℂ] Fun K) (hT : ∀ x, (T x : Fun K) = S' x) (c : ℂ) :
    finrank ℂ (eigenSub T c) = finrank ℂ ↥(W' ⊓ eigenSub S' c) := by
  rw [← map_subtype_eigenSub K T S' hT c]
  exact ((eigenSub T c).equivMapOfInjective _ W'.injective_subtype).finrank_eq

omit [NumberField K] in
lemma eigenSub_S_plus (k : ℕ) : eigenSub (S K k) ((-1) ^ k) = eigenSub (Xbar.conjPullback K) 1 := by
  ext x
  rw [mem_eigenSub, mem_eigenSub, S_apply, one_smul,
    smul_right_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))]

omit [NumberField K] in
lemma eigenSub_S_minus (k : ℕ) :
    eigenSub (S K k) (-(-1) ^ k) = eigenSub (Xbar.conjPullback K) (-1) := by
  ext x
  rw [mem_eigenSub, mem_eigenSub, S_apply, show -(-1 : ℂ) ^ k = (-1) ^ k * (-1) by ring, mul_smul,
    smul_right_inj (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))]

lemma hplus_finrank (k : ℕ) :
    (hodge K n).hplus k = finrank ℂ ↥(W K n k k ⊓ eigenSub (S K k) ((-1) ^ k)) :=
  finrank_eigenSub_restrict K ((Finf K n k k).toLinearMap) (S K k) (fun _ => rfl) _

lemma hminus_finrank (k : ℕ) :
    (hodge K n).hminus k = finrank ℂ ↥(W K n k k ⊓ eigenSub (S K k) (-(-1) ^ k)) :=
  finrank_eigenSub_restrict K ((Finf K n k k).toLinearMap) (S K k) (fun _ => rfl) _

/-- `h^{k,+} = r₁ + r₂` for `k ≤ n`: the sign `(-1)^k` of `F_∞` cancels FM's `±(-1)^k`. -/
theorem hplus_eq {k : ℕ} (hk : k ≤ n) :
    (hodge K n).hplus k = nrRealPlaces K + nrComplexPlaces K := by
  rw [hplus_finrank, W_diag K n hk, top_inf_eq, eigenSub_S_plus]
  exact Xbar.finrank_invariants K

/-- `h^{k,-} = r₂` for `k ≤ n`. -/
theorem hminus_eq {k : ℕ} (hk : k ≤ n) : (hodge K n).hminus k = nrComplexPlaces K := by
  rw [hminus_finrank, W_diag K n hk, top_inf_eq, eigenSub_S_minus]
  exact Xbar.finrank_antiinvariants K

lemma hplus_gt {k : ℕ} (hk : n < k) : (hodge K n).hplus k = 0 := by
  rw [hplus_finrank, W_gt K n hk, bot_inf_eq]; exact finrank_bot ℂ _

lemma hminus_gt {k : ℕ} (hk : n < k) : (hodge K n).hminus k = 0 := by
  rw [hminus_finrank, W_gt K n hk, bot_inf_eq]; exact finrank_bot ℂ _

/-- `h^{p,q} = 0` for `p ≠ q`. -/
lemma h_offdiag {p q : ℕ} (h : p ≠ q) : (hodge K n).h p q = 0 := by
  show finrank ℂ (W K n p q) = 0
  rw [W_offdiag K n h]; exact finrank_bot ℂ _

/-- Nonvacuity: `h^{k,k} = [K : ℚ] > 0` for `k ≤ n`. -/
lemma h_diag {k : ℕ} (hk : k ≤ n) : (hodge K n).h k k = finrank ℚ K := by
  show finrank ℂ (W K n k k) = _
  rw [W_diag K n hk, finrank_top, finrank_fintype_fun_eq_card, Embeddings.card]

/-! ### The archimedean factors -/

/-- **FM's `L_∞(h^i, s)` for `ℙⁿ_{𝓞_K}`**: `Γ_ℝ(s-k)^{r₁+r₂} Γ_ℝ(s-k+1)^{r₂} = Γ_ℝ(s-k)^{r₁} Γ_ℂ(s-k)^{r₂}`
(`= zetaInftyFM K (s - k)`) if `i = 2k` with `k ≤ n`, and `1` otherwise. -/
theorem LInfty_eq (i : ℕ) (s : ℂ) :
    (hodge K n).LInfty i s =
      if Even i ∧ i / 2 ≤ n then zetaInftyFM K (s - (i / 2 : ℕ)) else 1 := by
  have hprod : (∏ p ∈ (Finset.range (i + 1)).filter (fun p => 2 * p < i),
      GammaCFM (s - p) ^ (hodge K n).h p (i - p)) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).2
    rw [h_offdiag K n (by omega), pow_zero]
  rw [HodgeDatum.LInfty, hprod, one_mul]
  by_cases he : Even i
  · by_cases hk : i / 2 ≤ n
    · rw [ite_eq_left he, ite_eq_left ⟨he, hk⟩, hplus_eq K n hk, hminus_eq K n hk, zetaInftyFM]
    · rw [ite_eq_left he, ite_eq_right (fun h => hk h.2), hplus_gt K n (by omega), hminus_gt K n (by omega),
        pow_zero, pow_zero, mul_one]
  · rw [ite_eq_right he, ite_eq_right (fun h => he h.1)]

/-- `L_∞(h^{2k}, s) = Γ_ℝ(s-k)^{r₁} Γ_ℂ(s-k)^{r₂}` for `k ≤ n` (FM normalization). -/
theorem LInfty_two_mul {k : ℕ} (hk : k ≤ n) (s : ℂ) :
    (hodge K n).LInfty (2 * k) s =
      GammaRFM (s - k) ^ nrRealPlaces K * GammaCFM (s - k) ^ nrComplexPlaces K := by
  rw [LInfty_eq, ite_eq_left ⟨even_two_mul k, by omega⟩, Nat.mul_div_cancel_left k two_pos,
    zetaInftyFM_eq]

/-- **FM's `ζ(X_∞, s)` for `ℙⁿ_{𝓞_K}`**: `∏_{k=0}^n Γ_ℝ(s-k)^{r₁} Γ_ℂ(s-k)^{r₂}`. -/
theorem zetaInfty_eq (s : ℂ) :
    (hodge K n).zetaInfty s = ∏ k ∈ Finset.range (n + 1), zetaInftyFM K (s - k) := by
  have key : ∀ m ≤ n, ∏ i ∈ Finset.range (2 * m + 1), (hodge K n).LInfty i s ^ ((-1 : ℤ) ^ i) =
      ∏ k ∈ Finset.range (m + 1), zetaInftyFM K (s - k) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Finset.prod_range_one, Finset.prod_range_one, pow_zero, zpow_one, LInfty_eq,
        ite_eq_left ⟨⟨0, rfl⟩, Nat.zero_le _⟩]
    | succ m ih =>
      intro hm
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.prod_range_succ,
        Finset.prod_range_succ, ih (by omega), LInfty_eq, LInfty_eq,
        ite_eq_right (fun h => (Nat.not_even_two_mul_add_one m) h.1),
        ite_eq_left ⟨⟨m + 1, by ring⟩, by omega⟩,
        show (2 * m + 1 + 1) / 2 = m + 1 by omega,
        Odd.neg_one_pow ⟨m, rfl⟩, Even.neg_one_pow ⟨m + 1, by ring⟩, one_zpow, mul_one, zpow_one,
        Finset.prod_range_succ _ (m + 1)]
  rw [HodgeDatum.zetaInfty, show (hodge K n).top = 2 * n from rfl]
  exact key n le_rfl

/-- For `n = 0`, `ℙ⁰_{𝓞_K} = Spec 𝓞_K` and `ζ(X_∞, s)` is round 50's `zetaInftyFM`. -/
theorem zetaInfty_zero (s : ℂ) : (hodge K 0).zetaInfty s = zetaInftyFM K s := by
  rw [zetaInfty_eq, Finset.prod_range_one, Nat.cast_zero, sub_zero]

/-! ### FM's completed zeta of `ℙⁿ_{𝓞_K}` -/

/-- **Definitional**: `ζ(ℙⁿ_{𝓞_K}, s) := ∏_{k=0}^n ζ_K(s - k)` (point counts of `ℙⁿ(𝔽_𝔭)`; not
derived — Mathlib has no `ζ(X, s)` for schemes nor the Euler product of `dedekindZeta`). -/
def zetaPn (s : ℂ) : ℂ := ∏ k ∈ Finset.range (n + 1), dedekindZeta K (s - k)

/-- FM's `ζ(ℙ̄ⁿ, s) = ζ(ℙⁿ_{𝓞_K}, s) · ζ(X_∞, s)` (FM p. 520), with `ζ(ℙⁿ_{𝓞_K}, s) = zetaPn`. -/
def zetaFMPn (s : ℂ) : ℂ := zetaPn K n s * (hodge K n).zetaInfty s

/-- `ζ(ℙ̄ⁿ, s) = ∏_{k=0}^n ζ(X̄_K, s - k)` (round 50's `zetaFM`). -/
lemma zetaFMPn_eq_prod (s : ℂ) :
    zetaFMPn K n s = ∏ k ∈ Finset.range (n + 1), zetaFM K (s - k) := by
  rw [zetaFMPn, zetaInfty_eq, zetaPn, ← Finset.prod_mul_distrib]
  rfl

/-- **FM's completed zeta of `ℙⁿ_{𝓞_K}`**: for `Re s > n + 1`,
`ζ(ℙ̄ⁿ, s) = ∏_{k=0}^n e^{a + b(s-k)} Λ_K(s-k)` (cf. the proof of Theorem D in
`ai/2026-10-31-conditional-dynamical-cohomology/report.md`). -/
theorem zetaFM_eq (C : DedekindContinuation K) {s : ℂ} (hs : (n : ℝ) + 1 < s.re) :
    zetaFMPn K n s =
      ∏ k ∈ Finset.range (n + 1), exp (fmA K + fmB K * (s - k)) * C.Λ (s - k) := by
  rw [zetaFMPn_eq_prod]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  refine WeilRH.Arakelov.zetaFM_eq K C ?_
  rw [sub_re, natCast_re]
  linarith

end ProjSpace

end WeilRH.Arakelov

end
