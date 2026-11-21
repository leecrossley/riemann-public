/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import WeilRH.BlackBoxes

/-!
# Second black-box set (round 74)

Three further classical theorems, each stated as a `Prop` and used only as an explicit
hypothesis. Taylor chose these three from the second survey
(`ai/2026-11-20-notes-lean-finish/blackboxes-2.md`); the Weil explicit formula (B5) was declined.
Each statement was kernel-checked at its source pin with standard axioms only
(`ai/2026-11-20-notes-lean-finish/checks2/report.md`).

* B3' `HadamardOrderOneLU` supersedes B3 (`HadamardOrderOne`) via `hadamardOrderOne_of_LU`.
* B4' `LogGammaStirling` supersedes B4 (`StirlingBox`), which has no consumers.
* B6 `RiemannVonMangoldt`.

Citation pinpoints are chapter/section level as given by the sources and were not re-verified
against the printed books.
-/

open Complex Set Filter Topology

namespace WeilRH

/-- **B3'. Hadamard factorization in genus at most one, locally uniform.** (J. Hadamard 1893;
E. C. Titchmarsh, *The Theory of Functions*, Ch. VIII.) Strengthens B3: the genus-one product
converges locally uniformly on `ℂ`, and `(log g)' = ∑ (1/(s-ρ_i) + 1/ρ_i)` off the zeros.

*Source.* Derived from `Complex.Hadamard.hadamard_factorization_of_growth`,
`hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ`,
`summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq` and
`logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne` in the AxiomMath fork of
PrimeNumberTheoremAnd@d71f7b41560c1487cc6b9fbbe6914b55fd8aac13 (Lean v4.35.0-rc2).
*Status.* Kernel-checked at the source pin, standard axioms only (`checks2/PNTBoxCheck2.lean`). -/
def HadamardOrderOneLU : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (∃ z, f z ≠ 0) →
    (∃ C : ℝ, ∀ z : ℂ, 2 ≤ ‖z‖ → Real.log ‖f z‖ ≤ C * ‖z‖ ^ (1 + (1 : ℝ) / 2)) →
    ∀ {ι : Type} (ρ : ι → ℂ), (∀ i, ρ i ≠ 0) →
      (∀ z, z ≠ 0 → (f z = 0 ↔ ∃ i, ρ i = z)) →
      (∀ z, z ≠ 0 → Nat.card {i // ρ i = z} = analyticOrderNatAt f z) →
      Summable (fun i => ‖ρ i‖⁻¹ ^ 2) ∧
      ∃ (a b : ℂ) (g : ℂ → ℂ),
        HasProdLocallyUniformlyOn (fun i s => (1 - s / ρ i) * Complex.exp (s / ρ i)) g univ ∧
        (∀ s : ℂ, f s = Complex.exp (a + b * s) * s ^ analyticOrderNatAt f 0 * g s) ∧
        ∀ s : ℂ, (∀ i, s ≠ ρ i) →
          HasSum (fun i => 1 / (s - ρ i) + 1 / ρ i) (logDeriv g s)

/-- B3' implies B3: a locally uniform product is a pointwise one. Every result stated under B3
holds under B3'. -/
theorem hadamardOrderOne_of_LU (h : HadamardOrderOneLU) : HadamardOrderOne := by
  intro f hf hnot hC ι ρ hρ0 hzeros hmult
  obtain ⟨hs, a, b, g, hLU, hfac, -⟩ := h f hf hnot hC ρ hρ0 hzeros hmult
  exact ⟨hs, a, b, g, fun s => ⟨hLU.hasProd (mem_univ s), hfac s⟩⟩

/-- **B4'. Holomorphic `log Γ` with Stirling's formula on sectors.** (E. T. Whittaker and
G. N. Watson, *A Course of Modern Analysis*, Ch. XII (chapter level, unverified); NIST DLMF
(5.11.1), Stirling's series for `Ln Γ(z)` on `|ph z| ≤ π − δ`, with error bounds in §5.11(ii)
(verified at dlmf.nist.gov/5.11, 2026-11-20).) There is a holomorphic `L` on the slit plane with `exp ∘ L = Γ`, `L 2 = 0`,
and for each `0 < δ < π` an `O(1/‖s‖)` Stirling remainder on `|arg s| ≤ π − δ`. The remainder is
holomorphic on the slit plane, as Cauchy estimates require; B4 gave only a pointwise remainder.

*Source.* Assembled from `logGamma`, `differentiableOn_logGamma`, `exp_logGamma`, `logGamma_two`
and `exists_norm_logGamma_sub_stirling_le`, TauCeti@8794ab329bb60340fa690a2902cf995f0571721b
(Lean v4.37.0-rc1, `TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic`).
*Status.* Kernel-checked at the source pin, standard axioms only (`checks2/TauCetiBoxCheck.lean`).
Supersedes B4. -/
def LogGammaStirling : Prop :=
  ∃ L : ℂ → ℂ, DifferentiableOn ℂ L slitPlane ∧
    EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane ∧ L 2 = 0 ∧
    ∀ δ : ℝ, 0 < δ → δ < Real.pi → ∃ C : ℝ, ∀ s : ℂ, |s.arg| ≤ Real.pi - δ → s ≠ 0 →
      ‖L s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * Real.pi) / 2 : ℝ))‖ ≤ C / ‖s‖

namespace RvM

/-- Zeros of `ζ` in the open critical strip with `0 < Im ρ ≤ T`. Verbatim
`ZetaZeros.nontrivialZeros` (AxiomMath/ZetaZerosV2@1d7edeb). -/
def nontrivialZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- `N(T)`, zeros counted with multiplicity. Definitionally the source's `ZetaZeros.zeroCount`. -/
noncomputable def zeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ nontrivialZeros T, analyticOrderNatAt riemannZeta ρ

/-- `M(T) = (T/2π) log(T/2π) − T/2π`. Verbatim `ZetaZeros.mainTerm`. -/
noncomputable def mainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi)

end RvM

/-- **B6. Riemann–von Mangoldt formula.** (H. von Mangoldt 1905; E. C. Titchmarsh, *The Theory
of the Riemann Zeta-Function*, Ch. IX.) `N(T) = M(T) + O(log T)` for `T ≥ 4`.

*Source.* Verbatim `ZetaZeros.RiemannVonMangoldt`, proved as `ZetaZeros.riemannVonMangoldt`
(AxiomMath/ZetaZerosV2@1d7edeb4e67096f9da1b37cd4b763e8b73886655, Lean v4.34.0-rc2).
*Status.* Kernel-checked at the source pin, standard axioms only
(`checks2/ZetaZerosBoxCheck.lean`). -/
def RiemannVonMangoldt : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T → |(RvM.zeroCount T : ℝ) - RvM.mainTerm T| ≤ C * Real.log T

end WeilRH
