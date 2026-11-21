import WeilRH.Dedekind

/-!
# `ξ_K` for number fields (roadmap D3, started)

Round 49 of `lean/ROADMAP-arakelov.md`. Source: `latex/notes.tex`, `def:zeta`
(`Λ_K(s) = |D_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)`, `ξ_K(s) = s (s - 1) Λ_K(s)`) and
`prop:xiK`. Hecke's continuation and functional equation (`thm:imp-hecke`) are not in Mathlib;
following roadmap decision D4 they are the hypothesis `DedekindContinuation K`
(`WeilRH/Dedekind.lean`), which already records `Λ_K` with the notes' normalization
(`dedekindGammaFactor`).

## Main results

* `xiK C s := s (s - 1) Λ_K(s)`.
* `xiK_one_sub`: `ξ_K(1 - s) = ξ_K(s)` off `{0, 1}` (part of `prop:xiK`).
* `xiK_eqOn`: `ξ_K` does not depend on the chosen continuation (off `{0, 1}`).
* `xiK_rat`: for `K = ℚ`, `ξ_ℚ(s) = 2 ξ(s)` with Mathlib/`Completed.lean`'s `completedXi`
  (the notes' remark after `prop:xiK`: "`ξ_ℚ = 2ξ`").
* `xiK_eq_zero_iff_rat`: for `K = ℚ` and `s ≠ 0, 1`, `ξ_ℚ(s) = 0` iff `s` is a nontrivial zero
  of `ζ` (the `K = ℚ` case of the last clause of `prop:xiK`).

## Round 50: simple poles (`prop:xiK`, entire part)

Hecke's theorem also says that the poles of `Λ_K` at `0, 1` are simple. Mathlib does not have
it, so it is the separate hypothesis `DedekindContinuation.SimplePoles C`: `s (s - 1) Λ_K(s)`
extends to an entire function `P.ξ` (kept separate so that existing continuations, e.g.
`DedekindContinuation.rat`, need no change). From it:

* `SimplePoles.one_sub`: `ξ_K(1 - s) = ξ_K(s)` for **all** `s` (continuity + density).
* `SimplePoles.xi_one`: `ξ_K(1) = |d_K|^{1/2} Γ_ℝ(1)^{r₁} Γ_ℂ(1)^{r₂} · Res_{s=1} ζ_K`, from
  Mathlib's class number formula `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (not assumed).
* `SimplePoles.xi_one_ne_zero`, `xi_zero_ne_zero`: `ξ_K(0) ξ_K(1) ≠ 0` (notes `prop:xiK`),
  using `dedekindZeta_residue_ne_zero`. So only *simplicity* of the poles is assumed; the
  nonvanishing of the residues is proved.
* `SimplePoles.xi_eq_zero_iff`: the zeros of `ξ_K` are exactly the nontrivial zeros
  (`Λ_K ρ = 0`, `ρ ≠ 0, 1`) of `dedekindDatum`.
* `SimplePoles.ofRat`: the hypothesis holds for `ℚ` (`ξ = 2 completedXi`, Mathlib), so it is
  satisfiable.

## Not formalized (recorded in `lean/README.md`)

* Simplicity of the poles of `Λ_K` for general `K` (the `SimplePoles` hypothesis; Hecke).
* Nonvanishing of `ξ_K` for `Re s > 1` (and hence `Re s < 0`): this needs the Euler product of
  `ζ_K`, which Mathlib v4.34.1 does not provide for `dedekindZeta`.
* The order comparison `ord_s ξ_K = ord_s ζ_K` on `0 ≤ Re s ≤ 1` needs the continuation of
  `ζ_K` itself, not only of `Λ_K`.
-/

open NumberField Filter Topology Complex

noncomputable section

namespace WeilRH

variable {K : Type*} [Field K] [NumberField K]

/-- `ξ_K(s) = s (s - 1) Λ_K(s)` (notes `def:zeta`), for a chosen continuation of `Λ_K`. -/
def xiK (C : DedekindContinuation K) (s : ℂ) : ℂ := s * (s - 1) * C.Λ s

/-- `ξ_K(1 - s) = ξ_K(s)` for `s ≠ 0, 1` (notes `prop:xiK`). -/
theorem xiK_one_sub (C : DedekindContinuation K) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiK C (1 - s) = xiK C s := by
  simp only [xiK, C.one_sub s h0 h1]
  ring

/-- `ξ_K` does not depend on the continuation (off `{0, 1}`). -/
theorem xiK_eqOn (C C' : DedekindContinuation K) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiK C s = xiK C' s := by
  have hs : s ∈ ({0, 1}ᶜ : Set ℂ) := by simp [h0, h1]
  simp only [xiK, C.eqOn C' hs]

/-- For `K = ℚ`: `ξ_ℚ(s) = 2 ξ(s)` with `completedXi` (`ξ(s) = ½ s (s - 1) Λ(s)`), for any
continuation and `s ≠ 0, 1` (notes, remark after `prop:xiK`). -/
theorem xiK_rat (C : DedekindContinuation ℚ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiK C s = 2 * completedXi s := by
  rw [xiK_eqOn C DedekindContinuation.rat h0 h1, completedXi_eq h0 h1]
  simp only [xiK, DedekindContinuation.rat]
  ring

/-- For `K = ℚ` and `s ≠ 0, 1`: `ξ_ℚ(s) = 0` iff `s` is a nontrivial zero of `ζ`. -/
theorem xiK_eq_zero_iff_rat (C : DedekindContinuation ℚ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiK C s = 0 ↔ IsNontrivialZetaZero s := by
  rw [xiK_rat C h0 h1, mul_eq_zero, completedXi_eq_zero_iff]
  simp

/-! ### Simple poles (round 50) -/

/-- **Simple poles of `Λ_K`** (part of Hecke's theorem, notes `thm:imp-hecke`; not in Mathlib
v4.34.1): `s (s - 1) Λ_K(s)` extends to an entire function. This is the extra hypothesis that the
entire part of `prop:xiK` needs. -/
structure DedekindContinuation.SimplePoles (C : DedekindContinuation K) where
  /-- The entire extension of `ξ_K(s) = s (s - 1) Λ_K(s)`. -/
  ξ : ℂ → ℂ
  /-- `ξ_K` is entire. -/
  differentiable : Differentiable ℂ ξ
  /-- It agrees with `s (s - 1) Λ_K(s)` off the poles. -/
  eq_xiK : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = xiK C s

/-- The archimedean and conductor factor is nonzero at `s = 1`. -/
lemma dedekindGammaFactor_one_ne_zero : dedekindGammaFactor K 1 ≠ 0 := by
  unfold dedekindGammaFactor
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos (by simp))))
    (pow_ne_zero _ (by rw [Gammaℂ_one]; simp [Real.pi_ne_zero]))
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hd h.1

/-- The archimedean and conductor factor is continuous at `s = 1`. -/
lemma continuousAt_dedekindGammaFactor_one : ContinuousAt (dedekindGammaFactor K) 1 := by
  have hd : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (discr_ne_zero K)
  have h1 : ContinuousAt (fun s : ℂ => ((|discr K| : ℤ) : ℂ) ^ (s / 2)) 1 :=
    (continuousAt_const_cpow hd).comp (continuous_id.div_const 2).continuousAt
  have hR : ContinuousAt Gammaℝ 1 := by
    have := (differentiable_Gammaℝ_inv.continuous.continuousAt (x := 1)).inv₀
      (by simp [Gammaℝ_one])
    convert this using 1
    funext s; simp
  have hC : ContinuousAt Gammaℂ 1 := by
    have := (differentiable_Gammaℂ_inv.continuous.continuousAt (x := 1)).inv₀
      (by simp [Gammaℂ_one, Real.pi_ne_zero])
    convert this using 1
    funext s; simp
  exact (h1.mul (hR.pow _)).mul (hC.pow _)

namespace DedekindContinuation.SimplePoles

variable {C : DedekindContinuation K} (P : C.SimplePoles)

lemma dense_compl_zero_one : Dense ({0, 1}ᶜ : Set ℂ) :=
  (Set.toFinite ({0, 1} : Set ℂ)).countable.dense_compl ℂ

/-- `ξ_K(1 - s) = ξ_K(s)` for every `s` (notes `prop:xiK`). -/
theorem one_sub (s : ℂ) : P.ξ (1 - s) = P.ξ s := by
  have h : (fun z => P.ξ (1 - z)) = P.ξ := by
    refine Continuous.ext_on dense_compl_zero_one
      (P.differentiable.continuous.comp (continuous_const.sub continuous_id))
      P.differentiable.continuous (fun z hz => ?_)
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    obtain ⟨h0, h1⟩ := hz
    have h0' : (1 - z) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h1' : (1 - z) ≠ 1 := fun h => h0 (by linear_combination -h)
    show P.ξ (1 - z) = P.ξ z
    rw [P.eq_xiK _ h0' h1', P.eq_xiK _ h0 h1, xiK_one_sub C h0 h1]
  exact congrFun h s

/-- **`ξ_K(1)` from the class number formula**: `ξ_K(1) = |d_K|^{1/2} Γ_ℝ(1)^{r₁} Γ_ℂ(1)^{r₂} ·
Res_{s=1} ζ_K`, by Mathlib's `tendsto_sub_one_mul_dedekindZeta_nhdsGT`. -/
theorem xi_one : P.ξ 1 = dedekindGammaFactor K 1 * (dedekindZeta_residue K : ℂ) := by
  have hreal : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  have hf : Tendsto (fun t : ℝ => P.ξ t) (𝓝[>] 1) (𝓝 (P.ξ 1)) :=
    (P.differentiable.continuous.tendsto 1).comp hreal
  have hg : Tendsto (fun t : ℝ => (t : ℂ) * dedekindGammaFactor K t *
      (((t : ℂ) - 1) * dedekindZeta K t)) (𝓝[>] 1)
      (𝓝 (1 * dedekindGammaFactor K 1 * (dedekindZeta_residue K : ℂ))) := by
    refine (hreal.mul ((continuousAt_dedekindGammaFactor_one).tendsto.comp hreal)).mul ?_
    simpa using tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have heq : (fun t : ℝ => P.ξ t) =ᶠ[𝓝[>] 1] (fun t : ℝ => (t : ℂ) * dedekindGammaFactor K t *
      (((t : ℂ) - 1) * dedekindZeta K t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (1 : ℝ) < t := ht
    have h0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
    have h1 : (t : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt ht')
    rw [P.eq_xiK _ h0 h1, xiK, C.eq_of_one_lt_re _ (by simpa using ht')]
    ring
  have := tendsto_nhds_unique (hf.congr' heq) hg
  simpa using this

/-- `ξ_K(1) ≠ 0` (notes `prop:xiK`). -/
theorem xi_one_ne_zero : P.ξ 1 ≠ 0 := by
  rw [P.xi_one]
  exact mul_ne_zero dedekindGammaFactor_one_ne_zero
    (by exact_mod_cast dedekindZeta_residue_ne_zero K)

/-- `ξ_K(0) ≠ 0` (notes `prop:xiK`). -/
theorem xi_zero_ne_zero : P.ξ 0 ≠ 0 := by
  have h := P.one_sub 1
  rw [sub_self] at h
  rw [h]
  exact P.xi_one_ne_zero

/-- The zeros of the entire `ξ_K` are exactly the nontrivial zeros of `dedekindDatum`:
`Λ_K(ρ) = 0` with `ρ ≠ 0, 1`. -/
theorem xi_eq_zero_iff (ρ : ℂ) : P.ξ ρ = 0 ↔ C.Λ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1 := by
  by_cases h0 : ρ = 0
  · subst h0; simp [P.xi_zero_ne_zero]
  by_cases h1 : ρ = 1
  · subst h1; simp [P.xi_one_ne_zero]
  have h1' : ρ - 1 ≠ 0 := sub_ne_zero.2 h1
  rw [P.eq_xiK _ h0 h1, xiK]
  simp [h0, h1, h1']

/-- **The hypothesis is satisfiable**: for `K = ℚ`, `ξ = 2 completedXi` (Mathlib). -/
def ofRat (C : DedekindContinuation ℚ) : C.SimplePoles where
  ξ s := 2 * completedXi s
  differentiable := (differentiable_const _).mul differentiable_completedXi
  eq_xiK _ h0 h1 := (xiK_rat C h0 h1).symm

end DedekindContinuation.SimplePoles

end WeilRH

end
