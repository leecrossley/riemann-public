import Mathlib
import WeilRH.ArakelovZeta
import WeilRH.ArakelovChowReal

/-!
# Order of `ζ(X̄_K, s)` at `s = 1` and `s = 0` (Flach–Morin Prop. 4.14 (iii), `n = 1`)

Round 58 of the Flach–Morin path (`lean/ROADMAP-arakelov.md`, decision D8).

Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020),
Prop. 4.14 (p. 534): for `X̄ → Spec ℤ` projective regular of pure dimension `d`, assuming
Conjecture 4.1, (iii) `ord_{s=n} ζ(X̄, s) = -dim_ℂ CH^n(X̄)_ℂ`. Its proof (p. 535) cites
[13, Prop. 2.11] for the identification `CH^n(X̄)_ℝ ≅ H^{2n}(X̄, ℝ(n))`.

For `X̄ = X̄_K` and `n = 1` we prove the statement *unconditionally* in our model, with
`ζ(X̄_K, s)` FM's zeta continued through a continuation `C` of `Λ_K` (round 50's `zetaFMCont`),
assuming only simple poles (`DedekindContinuation.SimplePoles`, Hecke):

* `meromorphicOrderAt_zetaFMCont_one`: `ord_{s=1} ζ(X̄_K, s) = -1`;
* `meromorphicOrderAt_zetaFMCont_zero`: `ord_{s=0} ζ(X̄_K, s) = -1`;
* `fm414_iii`: `ord_{s=1} ζ(X̄_K, s) = -dim_ℝ ĈH¹(X̄_K)_ℝ = -dim_ℝ H²(X̄_K, ℝ(1))`, combining
  round 57's `chowDegreeREquiv` and round 56's `finrank_hBar_two`.

Fidelity: FM state (iii) with `dim_ℂ CH^n(X̄)_ℂ`; we use the real-coefficient Arakelov Chow group
`ĈH¹(X̄_K)_ℝ` of round 57 (FM Notation 4.13) and its real dimension, which agrees after `⊗_ℝ ℂ`.
The order is Mathlib's `meromorphicOrderAt`, which ignores the junk value of `Λ_K` at the pole.
FM's Conjecture 4.1 is not used: in this model the statement is a theorem.
-/

open NumberField Complex Topology Filter Module

noncomputable section

namespace WeilRH.Arakelov

variable (K : Type*) [Field K] [NumberField K]

namespace ZetaOrder

variable {K} {C : DedekindContinuation K} (P : C.SimplePoles)

/-- Off the poles, `ζ(X̄_K, s) = e^{a+bs} ξ_K(s) / (s (s - 1))`. -/
lemma zetaFMCont_eq (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    zetaFMCont K C s = exp (fmA K + fmB K * s) * P.ξ s / (s * (s - 1)) := by
  have hs : s * (s - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1)
  rw [P.eq_xiK s h0 h1, xiK, zetaFMCont]
  field_simp

/-- The analytic factor at `s = 1`: `e^{a+bs} ξ_K(s) / s`. -/
def g1 (s : ℂ) : ℂ := exp (fmA K + fmB K * s) * P.ξ s / s

/-- The analytic factor at `s = 0`: `e^{a+bs} ξ_K(s) / (s - 1)`. -/
def g0 (s : ℂ) : ℂ := exp (fmA K + fmB K * s) * P.ξ s / (s - 1)

lemma analyticAt_g1 : AnalyticAt ℂ (g1 P) 1 := by
  have he : AnalyticAt ℂ (fun s => exp (fmA K + fmB K * s)) 1 := by
    have : Differentiable ℂ (fun s => exp (fmA K + fmB K * s)) := by fun_prop
    exact this.analyticAt 1
  exact (he.mul (P.differentiable.analyticAt 1)).div analyticAt_id (by norm_num)

lemma analyticAt_g0 : AnalyticAt ℂ (g0 P) 0 := by
  have he : AnalyticAt ℂ (fun s => exp (fmA K + fmB K * s)) 0 := by
    have : Differentiable ℂ (fun s => exp (fmA K + fmB K * s)) := by fun_prop
    exact this.analyticAt 0
  exact (he.mul (P.differentiable.analyticAt 0)).div (analyticAt_id.sub analyticAt_const)
    (by norm_num)

lemma g1_one_ne_zero : g1 P 1 ≠ 0 := by
  simp [g1, exp_ne_zero, P.xi_one_ne_zero]

lemma g0_zero_ne_zero : g0 P 0 ≠ 0 := by
  simp [g0, exp_ne_zero, P.xi_zero_ne_zero]

/-- Near `1` (punctured), `ζ(X̄_K, s) = (s - 1)⁻¹ g₁(s)`. -/
lemma eventually_eq_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), zetaFMCont K C s = (s - 1) ^ (-1 : ℤ) • g1 P s := by
  have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaFMCont_eq P s hs0 hs1, g1, smul_eq_mul, zpow_neg_one]
  field_simp

/-- Near `0` (punctured), `ζ(X̄_K, s) = s⁻¹ g₀(s)`. -/
lemma eventually_eq_zero :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), zetaFMCont K C s = (s - 0) ^ (-1 : ℤ) • g0 P s := by
  have h1 : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 1 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
  filter_upwards [h1, self_mem_nhdsWithin] with s hs1 hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [zetaFMCont_eq P s hs0 hs1, g0, smul_eq_mul, sub_zero, zpow_neg_one]
  field_simp

lemma meromorphicAt_model {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    MeromorphicAt (fun s => (s - x) ^ (-1 : ℤ) • g s) x :=
  ((MeromorphicAt.id x).sub (MeromorphicAt.const x x)).zpow (-1) |>.smul hg.meromorphicAt

/-- **`ord_{s=1} ζ(X̄_K, s) = -1`** (simple pole), from `ξ_K(1) ≠ 0`. -/
theorem meromorphicOrderAt_zetaFMCont_one (P : C.SimplePoles) :
    meromorphicOrderAt (zetaFMCont K C) 1 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_congr (eventually_eq_one P),
    meromorphicOrderAt_eq_int_iff (meromorphicAt_model (analyticAt_g1 P))]
  exact ⟨g1 P, analyticAt_g1 P, g1_one_ne_zero P, Eventually.of_forall fun _ => rfl⟩

/-- **`ord_{s=0} ζ(X̄_K, s) = -1`** (simple pole), from `ξ_K(0) ≠ 0`. -/
theorem meromorphicOrderAt_zetaFMCont_zero (P : C.SimplePoles) :
    meromorphicOrderAt (zetaFMCont K C) 0 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_congr (eventually_eq_zero P),
    meromorphicOrderAt_eq_int_iff (meromorphicAt_model (analyticAt_g0 P))]
  exact ⟨g0 P, analyticAt_g0 P, g0_zero_ne_zero P, Eventually.of_forall fun _ => rfl⟩

end ZetaOrder

namespace ZetaOrder

variable (K : Type) [Field K] [NumberField K]

/-- `dim_ℝ ĈH¹(X̄_K)_ℝ = 1` (round 57's degree isomorphism). -/
lemma finrank_chowR : finrank ℝ (ArithChowReal.ChowR K) = 1 := by
  rw [LinearEquiv.finrank_eq (ArithChowReal.chowDegreeREquiv K), Module.finrank_self]

/-- **FM Prop. 4.14 (iii) for `X̄_K`, `n = 1`**:
`ord_{s=1} ζ(X̄_K, s) = -dim_ℝ ĈH¹(X̄_K)_ℝ = -dim_ℝ H²(X̄_K, ℝ(1))`. -/
theorem fm414_iii {C : DedekindContinuation K} (P : C.SimplePoles) :
    meromorphicOrderAt (zetaFMCont K C) 1 = (-(finrank ℝ (ArithChowReal.ChowR K) : ℤ) : ℤ) ∧
    meromorphicOrderAt (zetaFMCont K C) 1 = (-(finrank ℝ (hBar 2) : ℤ) : ℤ) := by
  rw [meromorphicOrderAt_zetaFMCont_one P, finrank_chowR K, finrank_hBar_two]
  simp

end ZetaOrder

end WeilRH.Arakelov
