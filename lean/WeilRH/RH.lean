/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Purity

/-!
# Degree-one Deninger data for `X̄_ℚ` implies RH (claims C-RH and C-GRH scaffold)

Source: `ai/2026-09-19-arithmetic-weil-cohomology/report.md`, §4.3 (AW1–AW6) and §5
(Proposition 1, identity (1)).

## Terminology

The structures `ArithmeticWeilCohomologyQ` and `ArithmeticWeilCohomology D` below are the
degree-one slice of a polarized Deninger structure satisfying AW2: a positive form satisfying (P)
plus the AW2 spectrum (notes `thm:rh`; `def:deninger-structure`, `def:polarizable`; the axioms
AW1–AW4 sit under `def:weil-cohomology`, "Deninger axioms"; a functor to such structures is a
Deninger cohomology theory, `def:deninger-theory`). The names are historical (from the Sept-19
report, which spoke of an "arithmetic Weil cohomology"); they are kept so that declarations are
stable.

## Design (lean-design-definitions)

Proposition 1 for `X̄_ℚ` uses exactly two inputs:

1. **AW4 in degree one, via (P) with `j = 1`**: a positive definite Hermitian form `h₁` on the
   degree-one spectral core `V¹` with `h₁(Θ₁u, v) + h₁(u, Θ₁v) = h₁(u, v)`.
2. **AW2 in degree one, divisor form (AW-div)**: the spectral divisor of `Θ₁` (eigenvalues with
   multiplicities) equals the zero divisor of `ξ`, i.e. the nontrivial zeros of `ζ` with their
   orders. This is the only consequence of (AW-det) and identity (1) that is used; it does not
   depend on any normalization of the regularized determinant `D₁`. (The zeta-regularized value
   is `D₁ = 2^{-1/2} ξ/2π²`, Deninger 1998 p. 168; identity (1) of the Sept-19 record,
   `D₁ = ξ/2π²`, holds only up to this constant and is superseded by its erratum, ruling R-1.)

We model the degree-one spectral core `V¹` as an arbitrary complex inner product space (no
completeness is assumed; the AW1 "algebraic direct sum of finite-dimensional flow-stable
blocks" is recorded by the field `locallyFinite`). Mathlib's inner product is conjugate-linear
in the first slot, so (P) is stated with the report-convention form `WeilRH.hForm`
(`hForm u v = ⟪v, u⟫`). The nontrivial-zero predicate is transcribed from Mathlib's
`RiemannHypothesis` (`ζ ρ = 0`, `ρ` not of the form `-2(n+1)`, `ρ ≠ 1`).

AW2 is encoded **only through its divisor consequence without multiplicities**:
`zero_isEigenvalue` (every nontrivial zero is an eigenvalue) and `isEigenvalue_zero` (every
eigenvalue is a nontrivial zero). The regularized determinant `det_∞`, zeta-regularization, the
identity (AW-det) itself, the determinant normalization and the local order condition
`m₁(ρ) = dim V¹_{Θ ∼ ρ}` are **not** encoded; neither are AW3 (duality/functional equation),
the star `*₁` of AW4 (only the form `h₁` it induces), AW5 (Hilbert completion and Stone
generator), AW6, cup products, functoriality, or any arithmetic construction. The proof of
`riemannHypothesis` uses only `P` and `zero_isEigenvalue`.
-/

open scoped InnerProductSpace ComplexConjugate

namespace WeilRH

/-- `ρ` is a nontrivial zero of `ζ` in exactly the sense of Mathlib's `RiemannHypothesis`. -/
def IsNontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

/-- The degree-one slice of a polarized Deninger structure on the Arakelov compactification
`X̄_ℚ` satisfying AW2 (notes `thm:rh`; `def:deninger-structure`, `def:polarizable`), as needed
for Proposition 1 of the report (see the module docstring for what is and is not encoded). The
name is historical. -/
structure ArithmeticWeilCohomologyQ where
  /-- The degree-one spectral core `V¹(X̄_ℚ)`. -/
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  /-- The positive definite Hermitian form `h₁` of AW4, as an inner product. -/
  [instInnerProductSpace : InnerProductSpace ℂ V]
  /-- The flow generator `Θ₁` (AW1). -/
  Θ : Module.End ℂ V
  /-- AW1: the spectral core is an algebraic direct sum of finite-dimensional `Θ₁`-stable
  blocks: every vector lies in a finite-dimensional `Θ₁`-invariant subspace. -/
  locallyFinite : ∀ v : V, ∃ W : Submodule ℂ V,
    v ∈ W ∧ FiniteDimensional ℂ W ∧ W ∈ Module.End.invtSubmodule Θ
  /-- AW4 ⇒ identity (P) in degree `j = 1`: `h₁(Θu, v) + h₁(u, Θv) = h₁(u, v)`. -/
  P : ∀ u v : V, hForm (Θ u) v + hForm u (Θ v) = hForm u v
  /-- AW2 + (1), zeros ⊆ spectrum: every nontrivial zero of `ζ` is an eigenvalue of `Θ₁`. -/
  zero_isEigenvalue : ∀ ρ : ℂ, IsNontrivialZetaZero ρ → Module.End.HasEigenvalue Θ ρ
  /-- AW2 + (1), spectrum ⊆ zeros: every eigenvalue of `Θ₁` is a nontrivial zero of `ζ`. -/
  isEigenvalue_zero : ∀ ρ : ℂ, Module.End.HasEigenvalue Θ ρ → IsNontrivialZetaZero ρ

attribute [instance] ArithmeticWeilCohomologyQ.instNormedAddCommGroup
  ArithmeticWeilCohomologyQ.instInnerProductSpace

namespace ArithmeticWeilCohomologyQ

variable (H : ArithmeticWeilCohomologyQ)

/-- Proposition 1 (degree one): every eigenvalue of `Θ₁` has real part `1/2`. -/
theorem re_eq_half_of_hasEigenvalue {ρ : ℂ} (hρ : Module.End.HasEigenvalue H.Θ ρ) :
    ρ.re = 1 / 2 :=
  WeilRH.re_eq_half_of_hasEigenvalue H.Θ 1 (fun u v => by simpa using H.P u v) hρ

/-- **C-RH (Proposition 1 for `X̄_ℚ`).** Degree-one data of a polarized Deninger structure on
`X̄_ℚ` satisfying AW2, in the sense of `ArithmeticWeilCohomologyQ` (notes `thm:rh`), imply
Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis (H : ArithmeticWeilCohomologyQ) : RiemannHypothesis := by
  intro s hs htriv hs1
  exact H.re_eq_half_of_hasEigenvalue (H.zero_isEigenvalue s ⟨hs, htriv, hs1⟩)

/-- Semisimplicity on blocks: `Θ₁` restricted to any finite-dimensional invariant subspace is
semisimple (no Jordan blocks), as in Proposition 1. -/
theorem isSemisimple_restrict {W : Submodule ℂ H.V} [FiniteDimensional ℂ W]
    (hW : W ∈ Module.End.invtSubmodule H.Θ) :
    Module.End.IsSemisimple (H.Θ.restrict (p := W) (q := W) (fun _ hx => hW hx)) := by
  apply WeilRH.isSemisimple_of_additive _ 1
  intro u v
  have := H.P u v
  simpa [hForm, Submodule.coe_inner] using this

end ArithmeticWeilCohomologyQ

/-- Conditional theorem, packaged: existence of an `ArithmeticWeilCohomologyQ` (degree-one slice
of a polarized Deninger structure satisfying AW2, notes `thm:rh`) implies RH. -/
theorem riemannHypothesis_of_nonempty (h : Nonempty ArithmeticWeilCohomologyQ) :
    RiemannHypothesis :=
  h.some.riemannHypothesis

/-! ## C-GRH scaffold: an abstract class of L-functions -/

/-- An abstract (completed) L-function datum: the function, the cohomological degree `j` whose
critical line is `Re s = j / 2`, and a predicate singling out its nontrivial zeros. For a pure
motive of motivic weight `w`, the report's indexing is `j = w + 1`. -/
structure LFunctionDatum where
  /-- The (completed or uncompleted) L-function. -/
  L : ℂ → ℂ
  /-- Cohomological degree: the critical line is `Re s = weight / 2`. -/
  weight : ℝ
  /-- Which zeros count as nontrivial. -/
  IsNontrivialZero : ℂ → Prop
  /-- Nontrivial zeros are zeros. -/
  isZero_of_isNontrivialZero : ∀ s, IsNontrivialZero s → L s = 0

namespace LFunctionDatum

/-- The generalized Riemann hypothesis for one datum. -/
def GRH (D : LFunctionDatum) : Prop := ∀ s, D.IsNontrivialZero s → s.re = D.weight / 2

/-- The Riemann zeta function as an `LFunctionDatum` of degree one. -/
noncomputable def riemannZeta : LFunctionDatum where
  L := _root_.riemannZeta
  weight := 1
  IsNontrivialZero := IsNontrivialZetaZero
  isZero_of_isNontrivialZero _ h := h.1

/-- GRH for the zeta datum is exactly Mathlib's `RiemannHypothesis`. -/
theorem grh_riemannZeta_iff : riemannZeta.GRH ↔ RiemannHypothesis := by
  constructor
  · intro h s hs htriv hs1
    simpa [riemannZeta] using h s ⟨hs, htriv, hs1⟩
  · intro h s hs
    simpa [riemannZeta] using h s hs.1 hs.2.1 hs.2.2

end LFunctionDatum

/-- The degree-`j` slice (`j = D.weight`) of a polarized Deninger structure satisfying AW2 on the
object attached to an abstract L-function datum `D` (notes `def:deninger-structure`,
`def:polarizable`), with the same encoding choices as `ArithmeticWeilCohomologyQ`. The name is
historical. -/
structure ArithmeticWeilCohomology (D : LFunctionDatum) where
  /-- The degree-`j` spectral core. -/
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  /-- The positive definite Hermitian form `h_j`. -/
  [instInnerProductSpace : InnerProductSpace ℂ V]
  /-- The flow generator `Θ_j`. -/
  Θ : Module.End ℂ V
  /-- Algebraic direct sum of finite-dimensional `Θ`-stable blocks. -/
  locallyFinite : ∀ v : V, ∃ W : Submodule ℂ V,
    v ∈ W ∧ FiniteDimensional ℂ W ∧ W ∈ Module.End.invtSubmodule Θ
  /-- Identity (P) in degree `j = D.weight`. -/
  P : ∀ u v : V, hForm (Θ u) v + hForm u (Θ v) = (D.weight : ℂ) * hForm u v
  /-- Nontrivial zeros ⊆ spectrum. -/
  zero_isEigenvalue : ∀ ρ : ℂ, D.IsNontrivialZero ρ → Module.End.HasEigenvalue Θ ρ
  /-- Spectrum ⊆ nontrivial zeros. -/
  isEigenvalue_zero : ∀ ρ : ℂ, Module.End.HasEigenvalue Θ ρ → D.IsNontrivialZero ρ

attribute [instance] ArithmeticWeilCohomology.instNormedAddCommGroup
  ArithmeticWeilCohomology.instInnerProductSpace

/-- **C-GRH scaffold.** Degree-`j` Deninger data for `D` (an `ArithmeticWeilCohomology D`, the
name being historical) imply GRH for `D`. -/
theorem ArithmeticWeilCohomology.grh {D : LFunctionDatum} (H : ArithmeticWeilCohomology D) :
    D.GRH := fun s hs =>
  WeilRH.re_eq_half_of_hasEigenvalue H.Θ D.weight H.P (H.zero_isEigenvalue s hs)

/-- A class `𝒞` of L-function data (to be fixed by the Q1 research agent). -/
abbrev LFunctionClass := Set LFunctionDatum

/-- **C-GRH scaffold (Theorem A shape).** If every member of `𝒞` admits an arithmetic Weil
cohomology, then GRH holds for every member of `𝒞`. -/
theorem grh_of_forall_mem {𝒞 : LFunctionClass}
    (h : ∀ D ∈ 𝒞, Nonempty (ArithmeticWeilCohomology D)) : ∀ D ∈ 𝒞, D.GRH :=
  fun D hD => (h D hD).some.grh

/-- The `X̄_ℚ` structure is the zeta instance of the general one. -/
def ArithmeticWeilCohomologyQ.toArithmeticWeilCohomology (H : ArithmeticWeilCohomologyQ) :
    ArithmeticWeilCohomology LFunctionDatum.riemannZeta where
  V := H.V
  Θ := H.Θ
  locallyFinite := H.locallyFinite
  P u v := by simpa [LFunctionDatum.riemannZeta] using H.P u v
  zero_isEigenvalue := H.zero_isEigenvalue
  isEigenvalue_zero := H.isEigenvalue_zero

/-- Conversely, a general structure for the zeta datum is an `ArithmeticWeilCohomologyQ`. -/
def ArithmeticWeilCohomologyQ.ofArithmeticWeilCohomology
    (H : ArithmeticWeilCohomology LFunctionDatum.riemannZeta) : ArithmeticWeilCohomologyQ where
  V := H.V
  Θ := H.Θ
  locallyFinite := H.locallyFinite
  P u v := by simpa [LFunctionDatum.riemannZeta] using H.P u v
  zero_isEigenvalue := H.zero_isEigenvalue
  isEigenvalue_zero := H.isEigenvalue_zero

/-- Consistency: the special case `𝒞 = {ζ}` of the scaffold recovers C-RH. -/
theorem riemannHypothesis_of_grh_scaffold
    (h : Nonempty (ArithmeticWeilCohomology LFunctionDatum.riemannZeta)) : RiemannHypothesis :=
  LFunctionDatum.grh_riemannZeta_iff.1 h.some.grh

end WeilRH
