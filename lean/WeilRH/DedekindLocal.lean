import Mathlib
import WeilRH.DedekindEuler

/-!
# The local Euler factors of `ζ_K` and `ζ_K ≠ 0` on `Re s > 1`

Round 63 groundwork, finishing `WeilRH.DedekindEuler`.

* `piProdP_all`: for a finite type `α` and absolutely summable `g a : ℕ → ℂ`,
  `∑_{k : α → ℕ} ∏_a g a (k a) = ∏_a ∑_n g a n` (the product of finitely many absolutely
  convergent series).
* `primesAbove K p`: the prime ideals of `𝓞_K` over `p`, as the support of the factorization of
  `(p)`; `absNorm_eq_pow`: `N 𝔭 = p^{f_𝔭}`.
* `toSigma_bijective`: `k ↦ ∏_𝔭 𝔭^{k_𝔭}` is a bijection from exponent vectors on the primes over
  `p` onto the ideals of `p`-power norm (unique factorization of ideals).
* `localFactor_eq_prod`: for `Re s > 1`,
  `∑_e a_K(p^e) p^{-e s} = ∏_{𝔭 ∣ p} (1 - N𝔭^{-s})⁻¹`.
* `dedekindZeta_ne_zero`: `ζ_K(s) ≠ 0` on `Re s > 1`, unconditionally;
  `nonvanishingRight`: the `NonvanishingRight` hypothesis of rounds 50 and 60 holds for every `K`;
  `fm414_neg'`: FM Prop. 4.14 at every `n < 0`, assuming only Hecke's simple poles.
-/

namespace WeilRH.DedekindLocal

open Finset
universe u

def PiProdP (α : Type u) [Fintype α] : Prop :=
  ∀ g : α → ℕ → ℂ, (∀ a, Summable fun n => ‖g a n‖) →
      (Summable fun k : α → ℕ => ‖∏ a, g a (k a)‖) ∧
        ∑' k : α → ℕ, ∏ a, g a (k a) = ∏ a, ∑' n, g a n

lemma piProdP_equiv (α β : Type u) [Fintype α] [Fintype β] (e : α ≃ β) (h : PiProdP α) : PiProdP β := by
  intro g hg
  obtain ⟨h1, h2⟩ := h (fun a => g (e a)) (fun a => hg (e a))
  let E : (β → ℕ) ≃ (α → ℕ) := e.symm.arrowCongr (Equiv.refl ℕ)
  have hE : ∀ (k : β → ℕ) (a : α), E k a = k (e a) := fun k a => by simp [E, Equiv.arrowCongr]
  have hprod : ∀ k : β → ℕ, ∏ b, g b (k b) = ∏ a, g (e a) ((E k) a) := fun k =>
    by
      rw [← Fintype.prod_equiv e (fun a => g (e a) (k (e a))) _ (fun _ => rfl)]; simp only [hE]
  have hp2 : ∏ b, ∑' n, g b n = ∏ a, ∑' n, g (e a) n :=
    (Fintype.prod_equiv e (fun a => ∑' n, g (e a) n) _ (fun _ => rfl)).symm
  constructor
  · rw [← E.summable_iff] at h1
    exact h1.congr fun k => by simp only [Function.comp_apply, hprod]
  · rw [hp2, ← h2, ← E.tsum_eq]
    exact tsum_congr fun k => hprod k

lemma piProdP_empty : PiProdP PEmpty.{u+1} := by
  intro g _
  simp only [Finset.univ_eq_empty, Finset.prod_empty]
  exact ⟨summable_of_hasFiniteSupport (Set.toFinite _), by rw [tsum_fintype]; simp⟩

lemma piProdP_option (α : Type u) [Fintype α] (ih : PiProdP α) : PiProdP (Option α) := by
  intro g hg
  obtain ⟨ih1, ih2⟩ := ih (fun a => g (some a)) (fun a => hg (some a))
  let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd (β := fun _ => ℕ)
  have key : ∀ k : Option α → ℕ, ∏ a, g a (k a) = g none (E k).1 * ∏ a, g (some a) ((E k).2 a) :=
    fun k => Fintype.prod_option _
  constructor
  · rw [← E.symm.summable_iff]
    have hn := summable_mul_of_summable_norm (R := ℝ) (f := fun n => ‖g none n‖)
          (g := fun k : α → ℕ => ‖∏ a, g (some a) (k a)‖) (by simpa using hg none) (by simpa using ih1)
    refine hn.congr fun x => ?_
    simp only [Function.comp_apply, key, Equiv.apply_symm_apply, norm_mul]
  · rw [← E.symm.tsum_eq, Fintype.prod_option, ← ih2, tsum_mul_tsum_of_summable_norm (hg none) ih1]
    exact tsum_congr fun x => by simp only [key, Equiv.apply_symm_apply]

theorem piProdP_all (α : Type u) [Fintype α] : PiProdP α :=
  Fintype.induction_empty_option (P := fun α _ => PiProdP α)
    (fun α β _ e h => @piProdP_equiv α β (Fintype.ofEquiv β e.symm) _ e h)
    piProdP_empty (fun α _ ih => piProdP_option α ih) α

open NumberField Ideal UniqueFactorizationMonoid
open WeilRH WeilRH.DedekindZetaConv WeilRH.DedekindEuler

variable {K : Type*} [Field K] [NumberField K]
local notation "R" K => 𝓞 K

/-- The prime ideals over `p`, as the support of the factorization of `(p)`. -/
noncomputable def primesAbove (K : Type*) [Field K] [NumberField K] (p : ℕ) : Finset (Ideal (R K)) :=
  (normalizedFactors (span {(p : R K)})).toFinset

lemma span_natCast_ne_bot {p : ℕ} (hp : p ≠ 0) : span {(p : R K)} ≠ ⊥ := by
  rw [Ne, span_singleton_eq_bot]; exact_mod_cast hp

lemma mem_primesAbove {p : ℕ} (hp : p ≠ 0) {P : Ideal (R K)} :
    P ∈ primesAbove K p ↔ P.IsPrime ∧ (p : R K) ∈ P := by
  rw [primesAbove, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hp),
    span_singleton_le_iff_mem]

lemma prime_of_mem_primesAbove {p : ℕ} {P : Ideal (R K)} (h : P ∈ primesAbove K p) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp h)

lemma ne_bot_of_mem_primesAbove {p : ℕ} {P : Ideal (R K)} (h : P ∈ primesAbove K p) : P ≠ ⊥ :=
  ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp h)

lemma two_le_absNorm {p : ℕ} {P : Ideal (R K)} (h : P ∈ primesAbove K p) : 2 ≤ absNorm P := by
  have h0 : absNorm P ≠ 0 := by rw [Ne, absNorm_eq_zero_iff]; exact ne_bot_of_mem_primesAbove h
  have h1 : absNorm P ≠ 1 := by
    rw [Ne, absNorm_eq_one_iff, ← Ideal.one_eq_top]; exact (prime_of_mem_primesAbove h).ne_one
  omega

/-- The exponent `f_𝔭` with `N 𝔭 = p ^ f_𝔭`. -/
noncomputable def fdeg (p : ℕ) (P : Ideal (R K)) : ℕ := (absNorm P).factorization p

lemma absNorm_eq_pow {p : ℕ} (hp : p.Prime) {P : Ideal (R K)} (h : P ∈ primesAbove K p) :
    absNorm P = p ^ fdeg p P := by
  have hmem := ((mem_primesAbove hp.ne_zero).mp h).2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (absNorm_dvd_pow_of_mem hmem)
  rw [fdeg, hi, hp.factorization_pow, Finsupp.single_eq_same]

/-- The ideal `∏_𝔭 𝔭^{k_𝔭}`. -/
noncomputable def idealOf (p : ℕ) (k : primesAbove K p → ℕ) : Ideal (R K) :=
  ∏ P : primesAbove K p, (P : Ideal (R K)) ^ k P

noncomputable def msOf (p : ℕ) (k : primesAbove K p → ℕ) : Multiset (Ideal (R K)) :=
  ∑ P : primesAbove K p, k P • ({(P : Ideal (R K))} : Multiset _)

lemma idealOf_eq_prod (p : ℕ) (k : primesAbove K p → ℕ) : idealOf p k = (msOf p k).prod := by
  simp [idealOf, msOf, Multiset.prod_sum, Multiset.prod_nsmul]

lemma mem_msOf {p : ℕ} {k : primesAbove K p → ℕ} {Q : Ideal (R K)} (h : Q ∈ msOf p k) :
    Q ∈ primesAbove K p := by
  simp only [msOf, Multiset.mem_sum, Finset.mem_univ, true_and] at h
  obtain ⟨P, hP⟩ := h
  rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hP
  rw [hP.2]; exact P.2

lemma count_msOf {p : ℕ} (k : primesAbove K p → ℕ) (Q : primesAbove K p) :
    (msOf p k).count (Q : Ideal (R K)) = k Q := by
  classical
  simp only [msOf, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
  rw [Finset.sum_eq_single Q]
  · simp
  · intro P _ hPQ
    have : (Q : Ideal (R K)) ≠ P := fun h => hPQ (Subtype.ext h.symm)
    simp [this]
  · simp

lemma normalizedFactors_idealOf (p : ℕ) (k : primesAbove K p → ℕ) :
    normalizedFactors (idealOf p k) = msOf p k := by
  rw [idealOf_eq_prod]
  exact normalizedFactors_prod_of_prime fun Q hQ => prime_of_mem_primesAbove (mem_msOf hQ)

lemma idealOf_injective (p : ℕ) : Function.Injective (idealOf (K := K) p) := by
  intro k k' h
  funext Q
  have := congrArg (fun I => (normalizedFactors I).count (Q : Ideal (R K))) h
  simpa [normalizedFactors_idealOf, count_msOf] using this

lemma absNorm_idealOf {p : ℕ} (hp : p.Prime) (k : primesAbove K p → ℕ) :
    absNorm (idealOf p k) = p ^ ∑ P : primesAbove K p, fdeg p (P : Ideal (R K)) * k P := by
  simp only [idealOf, map_prod, map_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [absNorm_eq_pow hp P.2, ← pow_mul]

lemma exists_idealOf {p : ℕ} (hp : p.Prime) {I : Ideal (R K)} {e : ℕ} (hI : absNorm I = p ^ e) :
    ∃ k, idealOf p k = I := by
  classical
  have hI0 : I ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at hI; exact (pow_ne_zero e hp.ne_zero) hI.symm
  have hsub : ∀ Q ∈ normalizedFactors I, Q ∈ primesAbove K p := by
    intro Q hQ
    obtain ⟨hQp, hIQ⟩ := (Ideal.mem_normalizedFactors_iff hI0).mp hQ
    have : ((p ^ e : ℕ) : R K) ∈ Q := hIQ (natCast_absNorm_mem I hI)
    push_cast at this
    exact (mem_primesAbove hp.ne_zero).mpr ⟨hQp, hQp.mem_of_pow_mem e this⟩
  refine ⟨fun Q => (normalizedFactors I).count (Q : Ideal (R K)), ?_⟩
  rw [idealOf_eq_prod]
  conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
  congr 1
  rw [msOf, Finset.sum_coe_sort (primesAbove K p)
    (fun Q => (normalizedFactors I).count Q • ({Q} : Multiset (Ideal (R K))))]
  conv_rhs => rw [← Multiset.toFinset_sum_count_nsmul_eq (normalizedFactors I)]
  symm
  refine Finset.sum_subset (fun Q hQ => hsub Q (Multiset.mem_toFinset.mp hQ)) fun Q _ hQ => ?_
  rw [Multiset.count_eq_zero_of_notMem (fun h => hQ (Multiset.mem_toFinset.mpr h)), zero_smul]


/-! ### The local factor as a finite product -/

lemma natCast_pow_cpow (n k : ℕ) (s : ℂ) : (((n ^ k : ℕ) : ℂ)) ^ s = ((n : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

lemma natCast_prod_cpow {ι : Type*} (t : Finset ι) (n : ι → ℕ) (s : ℂ) :
    (((∏ i ∈ t, n i : ℕ)) : ℂ) ^ s = ∏ i ∈ t, ((n i : ℂ) ^ s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/-- The weight `N 𝔭^{-s}`. -/
noncomputable def wt (s : ℂ) (P : Ideal (R K)) : ℂ := (((absNorm P : ℕ) : ℂ) ^ s)⁻¹

lemma norm_wt_lt_one {p : ℕ} {s : ℂ} (hs : 0 < s.re) {P : Ideal (R K)} (h : P ∈ primesAbove K p) :
    ‖wt s P‖ < 1 := by
  have h2 := two_le_absNorm h
  have hpos : 0 < absNorm P := by omega
  rw [wt, norm_inv, Complex.norm_natCast_cpow_of_pos hpos]
  apply inv_lt_one_of_one_lt₀
  exact Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < absNorm P)) hs

/-- The bijection `k ↦ (∑ f k, ∏ 𝔭^k)` onto ideals of `p`-power norm, graded by the exponent. -/
noncomputable def toSigma {p : ℕ} (hp : p.Prime) (k : primesAbove K p → ℕ) :
    Σ e : ℕ, {I : Ideal (R K) // absNorm I = p ^ e} :=
  ⟨∑ P : primesAbove K p, fdeg p (P : Ideal (R K)) * k P, idealOf p k, absNorm_idealOf hp k⟩

lemma toSigma_bijective {p : ℕ} (hp : p.Prime) : Function.Bijective (toSigma (K := K) hp) := by
  constructor
  · intro k k' h
    exact idealOf_injective p (congrArg (fun σ => (σ.2 : Ideal (R K))) h)
  · rintro ⟨e, I, hI⟩
    obtain ⟨k, hk⟩ := exists_idealOf hp hI
    refine ⟨k, Sigma.subtype_ext ?_ hk⟩
    have h1 := absNorm_idealOf hp k
    rw [hk, hI] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm

lemma finite_fiber (n : ℕ) : Finite {I : Ideal (R K) // absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-- **Local Euler factor.** For a rational prime `p` and `Re s > 1`,
`∑_e a_K(p^e) p^{-e s} = ∏_{𝔭 ∣ p} (1 - N𝔭^{-s})⁻¹`. -/
theorem localFactor_eq_prod {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ∑' e : ℕ, summand K s (p ^ e) = ∏ P : primesAbove K p, (1 - wt s (P : Ideal (R K)))⁻¹ := by
  classical
  have hs0 : 0 < s.re := by linarith
  let E := Equiv.ofBijective _ (toSigma_bijective (K := K) hp)
  let h : (Σ e : ℕ, {I : Ideal (R K) // absNorm I = p ^ e}) → ℂ :=
    fun σ => (((p ^ σ.1 : ℕ) : ℂ) ^ s)⁻¹
  have hwt : ∀ P : primesAbove K p, ‖wt s (P : Ideal (R K))‖ < 1 := fun P => norm_wt_lt_one hs0 P.2
  -- `h ∘ E` is the product of geometric terms
  have hE : ∀ k, h (E k) = ∏ P : primesAbove K p, wt s (P : Ideal (R K)) ^ k P := by
    intro k
    show (((p ^ (∑ P : primesAbove K p, fdeg p (P : Ideal (R K)) * k P) : ℕ) : ℂ) ^ s)⁻¹ = _
    rw [← absNorm_idealOf hp k, idealOf, map_prod]
    simp only [map_pow]
    rw [natCast_prod_cpow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [natCast_pow_cpow, wt, inv_pow]
  obtain ⟨hpi1, hpi2⟩ := piProdP_all (primesAbove K p) (fun P n => wt s (P : Ideal (R K)) ^ n)
    (fun P => by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hwt P))
  have hsumE : Summable (h ∘ E) := by
    refine Summable.of_norm (hpi1.congr fun k => ?_)
    simp [Function.comp_apply, hE]
  have hsum : Summable h := (E.summable_iff).mp hsumE
  have hfib : ∀ e : ℕ, Summable fun I : {I : Ideal (R K) // absNorm I = p ^ e} => h ⟨e, I⟩ := by
    intro e; have := finite_fiber (K := K) (p ^ e); exact Summable.of_finite
  have step1 : ∀ e : ℕ, summand K s (p ^ e) =
      ∑' I : {I : Ideal (R K) // absNorm I = p ^ e}, h ⟨e, I⟩ := by
    intro e
    have := finite_fiber (K := K) (p ^ e)
    simp only [h, tsum_const, nsmul_eq_mul]
    rw [summand, LSeries.term_of_ne_zero (pow_ne_zero e hp.ne_zero), coeff, div_eq_mul_inv]
    push_cast; rfl
  rw [tsum_congr step1, ← hsum.tsum_sigma' hfib, ← E.tsum_eq, tsum_congr hE, hpi2]
  exact Finset.prod_congr rfl fun P _ => tsum_geometric_of_norm_lt_one (hwt P)

/-- Every local factor is nonzero on `Re s > 1`. -/
theorem localFactor_ne_zero {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ∑' e : ℕ, summand K s ((p : ℕ) ^ e) ≠ 0 := by
  rw [localFactor_eq_prod p.2 hs]
  refine Finset.prod_ne_zero_iff.mpr fun P _ => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  have := norm_wt_lt_one (K := K) (by linarith : 0 < s.re) P.2
  rw [← h, norm_one] at this; exact lt_irrefl _ this

/-- **`ζ_K(s) ≠ 0` on `Re s > 1`**, unconditionally, for every number field. -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 :=
  dedekindZeta_ne_zero_of_localFactor_ne_zero hs (localFactor_ne_zero hs)

/-- The `NonvanishingRight` hypothesis of rounds 50 and 60 holds for every `K`. -/
theorem nonvanishingRight {C : DedekindContinuation K} (P : C.SimplePoles) :
    WeilRH.Arakelov.ZetaOrder.NonvanishingRight P :=
  nonvanishingRight_of_localFactor_ne_zero P fun _ hs => localFactor_ne_zero hs

/-- **FM Prop. 4.14 at every `n < 0`**, now assuming only Hecke's simple poles. -/
theorem fm414_neg' {C : DedekindContinuation K} (P : C.SimplePoles) {n : ℤ} (hn : n < 0) :
    (∀ i : ℤ, Module.finrank ℝ (WeilRH.Arakelov.TwistNeg.harNeg i) = 0) ∧
      meromorphicOrderAt (WeilRH.Arakelov.zetaFMCont K C) (n : ℂ) =
        (-(Module.finrank ℝ (WeilRH.Arakelov.TwistNeg.harNeg (2 * n)) : ℤ) : ℤ) :=
  WeilRH.Arakelov.TwistNeg.fm414_neg P (nonvanishingRight P) hn

end WeilRH.DedekindLocal
