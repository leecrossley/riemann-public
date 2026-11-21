/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import WeilRH.XiK

/-!
# Black boxes (round 68)

Four published theorems that Mathlib (at this project's pin, Lean v4.34.1, Mathlib v4.34.1) does
not contain, each stated as a `Prop`. **None is an `axiom`.** A result that uses a box takes it as an
explicit hypothesis (`(hB : HeckePackage K)`, `(hW : WeilConjectures)`, …), so its type shows the
dependence and `#print axioms` stays within `propext`, `Classical.choice`, `Quot.sound`. Such
results are CONDITIONAL on the named box.

Each box is satisfiable: a Lean proof of it exists in a public repository at another Lean/Mathlib
pin. The checks are recorded in `ai/2026-11-20-notes-lean-finish/checks/report.md`:

| Box | Proved by | Check |
|---|---|---|
| `HeckePackage K` | AxiomMath/RiemannJensen@99f4e82 | kernel-checked at source pin, standard axioms |
| `WeilConjectures` | AxiomMath/Weil@27cdb20 | statement only; **not** kernel-checked here |
| `HadamardOrderOne` | AxiomMath fork of PrimeNumberTheoremAnd@d71f7b4 | kernel-checked at source pin, standard axioms |
| `StirlingBox` | AxiomMath/RiemannJensen@99f4e82 | kernel-checked at source pin, standard axioms |

The boxes were selected (Taylor, 2026-11-20) after a search of Mathlib, Tau Ceti, AxiomMath,
lana-agents and Palomar (`ai/2026-11-20-notes-lean-finish/blackboxes.md`).
-/

open Complex NumberField

namespace WeilRH

/-- **B1. Hecke's theorem for the completed Dedekind zeta function `Λ_K`, with order one and
nonvanishing `ξ_K(0) ξ_K(1)`.** (E. Hecke, *Über die Zetafunktion beliebiger algebraischer
Zahlkörper*, Gött. Nachr. 1917; J. Neukirch, *Algebraic Number Theory*, Ch. VII §5.)
`Λ_K(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} ζ_K(s)` for `Re s > 1` extends holomorphically to
`ℂ ∖ {0, 1}` with `Λ_K(1 - s) = Λ_K(s)`; `ξ_K(s) = s(s-1)Λ_K(s)` extends to an entire function of
order at most one; and `ξ_K(0), ξ_K(1) ≠ 0`.

*Source.* Verbatim the conclusion of `NumberField.exists_completedDedekindZeta_package_core`,
AxiomMath/RiemannJensen@99f4e82 (`RiemannJensen/Dedekind/ZetaStripBounds.lean`), stated there for
`K : Type`. *Status.* Kernel-checked at the source pin (Lean v4.36.0) with standard axioms only.

It replaces the hypotheses `DedekindContinuation K` and `DedekindContinuation.SimplePoles` through
`HeckePackage.continuation` and `HeckePackage.simplePoles`. -/
def HeckePackage (K : Type) [Field K] [NumberField K] : Prop :=
  ∃ Λ : ℂ → ℂ,
    DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
    (∀ s : ℂ, 1 < s.re → Λ s =
      (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
        * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
        * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
        * NumberField.dedekindZeta K s) ∧
    (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
      ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
    (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0)

/-- B1 yields the project's hypothesis `DedekindContinuation K`. -/
noncomputable def HeckePackage.continuation {K : Type} [Field K] [NumberField K]
    (h : HeckePackage K) : DedekindContinuation K where
  Λ := h.choose
  differentiableOn := h.choose_spec.1
  eq_of_one_lt_re s hs := by rw [h.choose_spec.2.2.1 s hs]; rfl
  one_sub := h.choose_spec.2.1

/-- B1 yields `SimplePoles` for that continuation. -/
noncomputable def HeckePackage.simplePoles {K : Type} [Field K] [NumberField K]
    (h : HeckePackage K) : h.continuation.SimplePoles where
  ξ := h.choose_spec.2.2.2.1.choose
  differentiable := h.choose_spec.2.2.2.1.choose_spec.1
  eq_xiK s h0 h1 := h.choose_spec.2.2.2.1.choose_spec.2.1 s h0 h1

/-- The order-one growth bound of B1 for the entire `ξ_K` of `HeckePackage.simplePoles`. -/
theorem HeckePackage.growth {K : Type} [Field K] [NumberField K] (h : HeckePackage K) :
    ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ →
      Real.log ‖h.simplePoles.ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖ :=
  h.choose_spec.2.2.2.1.choose_spec.2.2

open CategoryTheory AlgebraicGeometry in
/-- **B2'. The Weil conjectures.** (P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43
(1974), for smooth *projective* `X`; the *proper* case, as stated here, is P. Deligne, *La conjecture
de Weil. II*, Publ. Math. IHÉS 52 (1980), 137–252, (3.3.9) — pinpoint corroborated by a secondary
source (A. Cadoret, *Ultraproduct Weil II for curves and integral models in compatible families of
ℓ-adic local systems*, which cites [D80, (3.3.9)] for integrality of the characteristic polynomial
of Frobenius on `H^i` of a smooth proper `X₀`); the original text was not consulted in round 71.
Rationality and functional equation: Dwork, Grothendieck.) For a smooth, proper,
geometrically irreducible `X` of dimension `d` over a finite field `F` there are multisets `A i`
(the Frobenius eigenvalues on `H^i`) with `A 0 = {1}`, Poincaré duality `A (2d - i) = q^d / A i`,
stability under every field automorphism of `ℂ`, integrality, purity `‖α‖ = q^{i/2}`, and the
Lefschetz point count `#X(E) = Σ_i (-1)^i Σ_{α ∈ A i} α^{[E:F]}` for every finite extension `E/F`.

*Source.* Verbatim the LeanEval problem `weil_conjectures` (leanprover/lean-eval@7c03706,
`LeanEval/AlgebraicGeometry/WeilConjectures.lean`), specialized to `F E : Type` (source:
`Type*`). Proved as `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures` in
AxiomMath/Weil@27cdb20 (Lean v4.34.0-rc2).

*Status.* **NOT kernel-checked in this project's check**: the Weil + Stacks build did not fit on
disk. The statement was compared textually with the source; a scan of the source found no
`sorry`, `admit`, `native_decide` or `axiom` declaration; its axiom set is the source README's
claim only. -/
def WeilConjectures : Prop :=
  ∀ (F : Type) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom],
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (Over.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum

/-- **B3. Hadamard factorization in genus at most one.** (J. Hadamard, *Étude sur les propriétés
des fonctions entières*, J. Math. Pures Appl. 1893; E. C. Titchmarsh, *The Theory of Functions*,
Ch. VIII.) An entire `f ≢ 0` with `log ‖f z‖ ≤ C ‖z‖^{3/2}` for `‖z‖ ≥ 2`, whose nonzero zeros
are listed with multiplicity by `ρ : ι → ℂ`, has `∑ ‖ρ_i‖^{-2} < ∞` and
`f(s) = e^{a+bs} s^{m} ∏ (1 - s/ρ_i) e^{s/ρ_i}`, the product converging unconditionally.

*Source.* Derived (about 150 lines) from `Complex.Hadamard.hadamard_factorization_of_growth`,
AxiomMath fork of PrimeNumberTheoremAnd@d71f7b4. *Status.* Kernel-checked at the source pin
(Lean v4.35.0-rc2) with standard axioms only. The derivation, not the source, fixes this
statement. -/
def HadamardOrderOne : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (∃ z, f z ≠ 0) →
    (∃ C : ℝ, ∀ z : ℂ, 2 ≤ ‖z‖ → Real.log ‖f z‖ ≤ C * ‖z‖ ^ (1 + (1 : ℝ) / 2)) →
    ∀ {ι : Type} (ρ : ι → ℂ), (∀ i, ρ i ≠ 0) →
      (∀ z, z ≠ 0 → (f z = 0 ↔ ∃ i, ρ i = z)) →
      (∀ z, z ≠ 0 → Nat.card {i // ρ i = z} = analyticOrderNatAt f z) →
      Summable (fun i => ‖ρ i‖⁻¹ ^ 2) ∧
      ∃ (a b : ℂ) (g : ℂ → ℂ), ∀ s : ℂ,
        HasProd (fun i => (1 - s / ρ i) * Complex.exp (s / ρ i)) (g s) ∧
        f s = Complex.exp (a + b * s) * s ^ analyticOrderNatAt f 0 * g s

/-- **B4. Complex Stirling formula with explicit error.** (E. T. Whittaker and G. N. Watson,
*A Course of Modern Analysis*, Ch. XII.) For `Re s ≥ 0` and `‖s‖ ≥ 2`,
`Γ(s) = √(2π) s^{s-1/2} e^{-s} e^{R}` with `‖R‖ ≤ 7/(2‖s‖)`.

*Source.* Verbatim the conclusion of `StirlingScratch.Gamma_stirling_exp_form`,
AxiomMath/RiemannJensen@99f4e82 (`RiemannJensen/Analysis/StirlingNative.lean`), quantified over
`s`. *Status.* Kernel-checked at the source pin (Lean v4.36.0) with standard axioms only. -/
def StirlingBox : Prop :=
  ∀ s : ℂ, 0 ≤ s.re → 2 ≤ ‖s‖ →
    ∃ R : ℂ, Complex.Gamma s =
        (Real.sqrt (2 * Real.pi) : ℂ) * s ^ (s - 1 / 2) * Complex.exp (-s) * Complex.exp R ∧
      ‖R‖ ≤ 7 / 2 / ‖s‖

end WeilRH
