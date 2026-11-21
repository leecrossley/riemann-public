/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ProjectiveLineScheme
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The formal zeta series in `prop:N-lines`

`zetaSeries c` is the formal exponential of `∑_{n≥1} cₙ tⁿ/n` over `ℂ`.
The product identity in `latex/notes.tex`, `prop:N-lines` (i), holds as an equality
of formal power series. No analytic convergence hypothesis is needed. A scheme
product version uses the geometric point-count theorem from `NLinesGeometry`.
The concrete `ℙ¹` version still requires its scheme-point equivalence with
Mathlib's projectivization.
-/

open AlgebraicGeometry CategoryTheory Limits PowerSeries
open scoped LinearAlgebra.Projectivization

namespace WeilRH.NLinesFormal

private theorem eq_zero_of_derivative_eq_mul (d a : ℂ⟦X⟧)
    (h0 : constantCoeff d = 0)
    (hd : derivative d = d * a) : d = 0 := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [coeff_zero_eq_constantCoeff_apply] using h0
    | succ m =>
      have heq := congrArg (coeff m) hd
      rw [coeff_derivative, coeff_mul] at heq
      have hsum : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
          coeff x.1 d * coeff x.2 a) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxle : x.1 < m + 1 := by
          have hmem := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          omega
        simp [ih x.1 hxle]
      rw [hsum] at heq
      have hm : (m : ℂ) + 1 ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (show ((m + 1 : ℕ) : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero m)
      simpa using (mul_eq_zero.mp heq).resolve_right hm

/-- Formal exponential by substitution into `PowerSeries.exp`. -/
noncomputable def formalExp (f : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  (PowerSeries.exp ℂ).subst f

private theorem constantCoeff_formalExp {f : ℂ⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (formalExp f) = 1 := by
  change MvPowerSeries.constantCoeff ((exp ℂ).subst f) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero hf]
  simp

private theorem derivative_formalExp {f : ℂ⟦X⟧} (hf : constantCoeff f = 0) :
    derivative (formalExp f) = formalExp f * derivative f := by
  rw [formalExp, derivative_subst (HasSubst.of_constantCoeff_zero' hf), derivative_exp]

/-- Exponentials of zero-constant formal series turn addition into multiplication. -/
theorem formalExp_add {f g : ℂ⟦X⟧}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    formalExp (f + g) = formalExp f * formalExp g := by
  have hfg : constantCoeff (f + g) = 0 := by simp [hf, hg]
  have hderiv : derivative (formalExp (f + g) - formalExp f * formalExp g) =
      (formalExp (f + g) - formalExp f * formalExp g) * (derivative f + derivative g) := by
    rw [map_sub, derivative_formalExp hfg, map_add, derivative.leibniz,
      derivative_formalExp hf, derivative_formalExp hg]
    simp only [smul_eq_mul]
    ring
  have hconst : constantCoeff (formalExp (f + g) - formalExp f * formalExp g) = 0 := by
    simp [constantCoeff_formalExp, hfg, hf, hg]
  exact sub_eq_zero.mp (eq_zero_of_derivative_eq_mul _ _ hconst hderiv)

/-- Formal exponential commutes with replacing `t` by `qt`. -/
theorem formalExp_rescale (q : ℂ) {f : ℂ⟦X⟧} (hf : constantCoeff f = 0) :
    formalExp (rescale q f) = rescale q (formalExp f) := by
  unfold formalExp
  rw [rescale_eq_subst q ((exp ℂ).subst f), rescale_eq_subst q f]
  rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hf)
    (HasSubst.smul_X' q) (exp ℂ)]

/-- The formal logarithm input `∑_{n≥1} cₙ tⁿ/n`; degree zero is zero. -/
noncomputable def logCountSeries (c : ℕ → ℂ) : ℂ⟦X⟧ :=
  mk (fun n => c n / n)

theorem constantCoeff_logCountSeries (c : ℕ → ℂ) :
    constantCoeff (logCountSeries c) = 0 := by
  simp [logCountSeries, ← coeff_zero_eq_constantCoeff_apply]

/-- `Z(t)=exp(∑_{n≥1} cₙ tⁿ/n)` from `def:hasse-weil-zeta` (a). -/
noncomputable def zetaSeries (c : ℕ → ℂ) : ℂ⟦X⟧ :=
  formalExp (logCountSeries c)

theorem logCountSeries_product (q : ℂ) (cE cX : ℕ → ℂ)
    (hX : ∀ n, 0 < n → cX n = cE n + q ^ n * cE n) :
    logCountSeries cX = logCountSeries cE + rescale q (logCountSeries cE) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [logCountSeries, coeff_mk, map_add, coeff_rescale, pow_zero,
      one_mul, Nat.cast_zero, div_zero, zero_add]
  · simp only [logCountSeries, coeff_mk, map_add, coeff_rescale]
    rw [hX n (Nat.pos_of_ne_zero hn)]
    ring

/-- `prop:N-lines` (i) as a formal power series identity. -/
theorem zetaSeries_product (q : ℂ) (cE cX : ℕ → ℂ)
    (hX : ∀ n, 0 < n → cX n = cE n + q ^ n * cE n) :
    zetaSeries cX = zetaSeries cE * rescale q (zetaSeries cE) := by
  have hrescale : constantCoeff (rescale q (logCountSeries cE)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [constantCoeff_logCountSeries, coeff_zero_eq_constantCoeff_apply]
  unfold zetaSeries
  rw [logCountSeries_product q cE cX hX,
    formalExp_add (constantCoeff_logCountSeries cE) hrescale,
    formalExp_rescale q (constantCoeff_logCountSeries cE)]

section Scheme

open WeilRH.NLinesGeometry

universe u
variable {k : Type u} [Field k]

/-- The formal zeta product follows from point counts of a scheme pullback. -/
theorem zetaSeries_product_of_geometry {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (K : ℕ → Type u) [∀ n, Field (K n)] [∀ n, Algebra k (K n)]
    (q : ℕ) (hP : ∀ n, 0 < n → pointCount g (K n) = q ^ n + 1) :
    zetaSeries (countSequence (pullback.fst f g ≫ f) K) =
      zetaSeries (countSequence f K) *
        rescale (q : ℂ) (zetaSeries (countSequence f K)) := by
  apply zetaSeries_product (q : ℂ) (countSequence f K)
  intro n hn
  simp only [countSequence]
  rw [pointCount_pullback, hP n hn]
  norm_cast
  ring

end Scheme

section FiniteExtensions

open WeilRH.NLinesGeometry

variable (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- `prop:N-lines` (i) over actual finite extensions, conditional on the projective-line
scheme-point equivalence. -/
theorem zetaSeries_product_finiteExtensions {X Y : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F)) (g : Y ⟶ Spec (CommRingCat.of F))
    (e : ∀ n, 0 < n → KPoints g (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n)) :
    zetaSeries (countSequence (pullback.fst f g ≫ f) (finiteExtensionFamily F p)) =
      zetaSeries (countSequence f (finiteExtensionFamily F p)) *
        rescale (Nat.card F : ℂ) (zetaSeries (countSequence f (finiteExtensionFamily F p))) := by
  apply zetaSeries_product_of_geometry f g (finiteExtensionFamily F p) (Nat.card F)
  intro n hn
  rw [pointCount_projectiveLine_of_equiv g (finiteExtensionFamily F p n) (e n hn),
    card_finiteExtensionFamily F p n hn]

/-- The literal formal series identity for `E ×_F ℙ¹_F`, with the concrete `Proj` scheme. -/
theorem zetaSeries_projectiveLineScheme_product {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F))
    (e : ∀ n, 0 < n → KPoints (projectiveLineToSpec F) (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n)) :
    zetaSeries
        (countSequence (pullback.fst f (projectiveLineToSpec F) ≫ f)
          (finiteExtensionFamily F p)) =
      zetaSeries (countSequence f (finiteExtensionFamily F p)) *
        rescale (Nat.card F : ℂ) (zetaSeries (countSequence f (finiteExtensionFamily F p))) :=
  zetaSeries_product_finiteExtensions F p f (projectiveLineToSpec F) e

end FiniteExtensions

end WeilRH.NLinesFormal
