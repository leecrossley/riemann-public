/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.Hermitian
import WeilRH.Spectral

/-!
# AW3 + AW4 in faithful form: the derivation law (Q1 Lemma 4.2)

Source: `ai/2026-09-25-zeta-class-axioms/report.md`, §3 (AW1, AW3, AW4 of type `(d, w)`) and
Lemma 4.2 ("AW3 and AW4 imply (P)"); Theorem 0 for the purity conclusion.

## Design (lean-design-definitions)

Q1's weighted package of type `(d, w)` in degree `j` involves three graded pieces
`V = V^j`, `W = V^{2d-j}`, `T = V^{2d}` with flow generators `Θ_j`, `Θ_{2d-j}`, `Θ_{2d}`, and

* (AW1) a cup product `∪ : V^j × V^{2d-j} → V^{2d}` for which `Θ` is a derivation:
  `Θ_{2d}(u ∪ v) = Θ_j u ∪ v + u ∪ Θ_{2d-j} v`;
* (AW3) a flow-equivariant trace `tr : V^{2d} → ℂ(-d-w)`; since `ℂ(-n)` is `ℂ` with `Θ = n`,
  equivariance reads `tr(Θ_{2d} x) = (d + w) tr(x)`. The duality pairing is `B(u,v) = tr(u ∪ v)`;
* (AW4) an **antilinear** star `*_j : V^j → V^{2d-j}` with
  `Θ_{2d-j} ∘ *_j = *_j ∘ Θ_j + (d - j) *_j`, such that `h_j(u, v) = tr(u ∪ *_j v)` is a positive
  definite Hermitian form on `V^j`.

We encode exactly this: `cup : V →ₗ[ℂ] W →ₗ[ℂ] T` (bilinear), `tr : T →ₗ[ℂ] ℂ`, and
`star : V →ₗ⋆[ℂ] W` (a `starRingEnd ℂ`-semilinear map, i.e. antilinear). `d w j : ℕ` (Q1:
`w ∈ ℤ_{≥0}`, `0 ≤ j ≤ 2d`); the shift `d - j` is taken in `ℂ`, so `j > d` is allowed. The
case `V^j = V^{2d-j}` (`j = d`) is the instance `W := V`.

**Not encoded (not needed for Lemma 4.2):** perfectness of `B` on `V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼d+w-ρ}`,
graded commutativity, the other degrees, functoriality, AW2. Positivity of `h` is a separate
hypothesis (`WeightedStarDatum.IsPositive`), because Lemma 4.2 itself does not use it
(Cor. 5.2: AW1–AW3 plus a flow-compatible *indefinite* form do not force purity; see
`WeilRH.R2.counterexample`).

## Main results

* `WeightedStarDatum.derivation_law` (**Q1 Lemma 4.2**): `h(Θu, v) + h(u, Θv) = (w + j) h(u, v)`,
  with no positivity assumption.
* `WeightedStarDatum.re_eq_of_hasEigenvalue` (**Q1 Theorem 0 via Lemma 4.2**): if `h` is positive
  definite Hermitian, every eigenvalue `ρ` of `Θ_j` has `Re ρ = (w + j)/2`.
* `WeightedStarDatum.isSemisimple`: in finite dimension `Θ_j` is semisimple.
* `WeightedStarDatum.lineModel`, `lineModel_isPositive`: the hypotheses are satisfiable (a
  one-dimensional positive model with eigenvalue `1/2 + iτ`, Q1 Prop. 5.1). For the other half of
  Q1 Cor. 5.2 (AW1–AW3 with a flow-compatible **indefinite** form and off-line spectrum) see
  `WeilRH.R2.counterexample` (`WeilRH/Negative.lean`).
-/

open scoped ComplexConjugate

namespace WeilRH

/-- The degree-`j` slice of a weighted arithmetic Weil datum of type `(d, w)` (Q1 §3): the pieces
`V = V^j`, `W = V^{2d-j}`, `T = V^{2d}` with flows, a cup product for which the flow is a
derivation (AW1), a flow-equivariant trace to `ℂ(-d-w)` (AW3) and an antilinear star
intertwining the flows up to the shift `d - j` (AW4). -/
structure WeightedStarDatum (d w j : ℕ) (V W T : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup T] [Module ℂ T] where
  /-- The flow generator `Θ_j` on `V^j`. -/
  ΘV : Module.End ℂ V
  /-- The flow generator `Θ_{2d-j}` on `V^{2d-j}`. -/
  ΘW : Module.End ℂ W
  /-- The flow generator `Θ_{2d}` on `V^{2d}`. -/
  ΘT : Module.End ℂ T
  /-- The cup product `V^j × V^{2d-j} → V^{2d}` (bilinear). -/
  cup : V →ₗ[ℂ] W →ₗ[ℂ] T
  /-- AW1: `Θ` is a derivation for `∪`. -/
  cup_derivation : ∀ u v, ΘT (cup u v) = cup (ΘV u) v + cup u (ΘW v)
  /-- AW3: the trace `V^{2d} → ℂ(-d-w)`. -/
  tr : T →ₗ[ℂ] ℂ
  /-- AW3: the trace is flow-equivariant, `ℂ(-d-w)` carrying `Θ = d + w`. -/
  tr_equivariant : ∀ x, tr (ΘT x) = ((d + w : ℕ) : ℂ) * tr x
  /-- AW4: the antilinear star `*_j : V^j → V^{2d-j}`. -/
  star : V →ₗ⋆[ℂ] W
  /-- AW4: `Θ_{2d-j} ∘ *_j = *_j ∘ Θ_j + (d - j) *_j`. -/
  star_comm : ∀ v, ΘW (star v) = star (ΘV v) + ((d : ℂ) - j) • star v

/-- **`prop:B-support`**, with exactly the manuscript's hypotheses. If `Θ` is a derivation for the
cup product `V^j × V^{2d-j} → V^{2d}` (AW1) and the trace `V^{2d} → ℂ` satisfies
`tr(Θ_{2d} x) = n·tr(x)` (AW3, `n = d` in type `(d, 0)`), then `B(u, v) = tr(u ∪ v)` vanishes on
`V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼σ}` unless `ρ + σ = n`. -/
theorem cupTrace_eq_zero_of_mem_maxGenEigenspace {V W T : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup T] [Module ℂ T] (ΘV : Module.End ℂ V)
    (ΘW : Module.End ℂ W) (ΘT : Module.End ℂ T) (cup : V →ₗ[ℂ] W →ₗ[ℂ] T) (tr : T →ₗ[ℂ] ℂ)
    (hcup : ∀ u v, ΘT (cup u v) = cup (ΘV u) v + cup u (ΘW v)) {n : ℂ}
    (htr : ∀ x, tr (ΘT x) = n * tr x) {ρ σ : ℂ} (hρσ : ρ + σ ≠ n) {u : V} {v : W}
    (hu : u ∈ ΘV.maxGenEigenspace ρ) (hv : v ∈ ΘW.maxGenEigenspace σ) : tr (cup u v) = 0 :=
  Spectral.pairing_eq_zero_of_mem_maxGenEigenspace (cup.compr₂ tr) ΘV ΘW n
    (fun u v => by simp only [LinearMap.compr₂_apply, ← map_add, ← hcup, htr]) hρσ hu hv

namespace WeightedStarDatum

variable {d w j : ℕ} {V W T : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup T] [Module ℂ T]
  (D : WeightedStarDatum d w j V W T)

/-- The duality pairing `B(u, v) = tr(u ∪ v)` of AW3. -/
def B (u : V) (v : W) : ℂ := D.tr (D.cup u v)

/-- The form `h_j(u, v) = tr(u ∪ *_j v)` of AW4. -/
def h (u v : V) : ℂ := D.B u (D.star v)

/-- AW3 in eigenvalue form: `B(Θ_j u, v) + B(u, Θ_{2d-j} v) = (d + w) B(u, v)`. -/
theorem B_equivariant (u : V) (v : W) :
    D.B (D.ΘV u) v + D.B u (D.ΘW v) = ((d + w : ℕ) : ℂ) * D.B u v := by
  simp only [B, ← map_add, ← D.cup_derivation, D.tr_equivariant]

/-- **`prop:B-support`** (from AW1 and AW3). For a Weil datum of type `(d, w)` satisfying the
derivation rule of AW1 and the trace equivariance of AW3, `B_j` vanishes on
`V^j_{Θ∼ρ} × V^{2d-j}_{Θ∼σ}` unless `ρ + σ = d + w`. The manuscript's statement is the case
`w = 0`; the star of AW4 is part of the structure but is not used (for the version without it
see `WeilRH.cupTrace_eq_zero_of_mem_maxGenEigenspace`). -/
theorem B_eq_zero_of_mem_maxGenEigenspace {ρ σ : ℂ} (hρσ : ρ + σ ≠ ((d + w : ℕ) : ℂ)) {u : V}
    {v : W} (hu : u ∈ D.ΘV.maxGenEigenspace ρ) (hv : v ∈ D.ΘW.maxGenEigenspace σ) :
    D.B u v = 0 :=
  cupTrace_eq_zero_of_mem_maxGenEigenspace D.ΘV D.ΘW D.ΘT D.cup D.tr D.cup_derivation
    D.tr_equivariant hρσ hu hv

lemma h_add_left (u u' v : V) : D.h (u + u') v = D.h u v + D.h u' v := by
  simp [h, B]

lemma h_smul_left (c : ℂ) (u v : V) : D.h (c • u) v = c * D.h u v := by
  simp [h, B]

lemma h_add_right (u v v' : V) : D.h u (v + v') = D.h u v + D.h u v' := by
  simp [h, B]

/-- `h` is conjugate-linear in its second argument because `*_j` is antilinear. -/
lemma h_smul_right (c : ℂ) (u v : V) : D.h u (c • v) = conj c * D.h u v := by
  simp [h, B]

/-- **Q1 Lemma 4.2 (derivation law).** AW1 (derivation), AW3 (equivariant trace) and AW4 (star
law) give `h_j(Θ_j u, v) + h_j(u, Θ_j v) = (w + j) h_j(u, v)`. No positivity is used. -/
theorem derivation_law (u v : V) :
    D.h (D.ΘV u) v + D.h u (D.ΘV v) = ((w + j : ℕ) : ℂ) * D.h u v := by
  have key := D.B_equivariant u (D.star v)
  rw [D.star_comm] at key
  simp only [h, B, map_add, map_smul, smul_eq_mul] at key ⊢
  push_cast at key ⊢
  linear_combination key

/-- **`prop:polarization-identity`** as the manuscript states it, for a Weil datum of type
`(d, 0)` (`def:aw`): `h_j(Θ_j u, v) + h_j(u, Θ_j v) = j h_j(u, v)`. The `w = 0` case of
`derivation_law`. -/
theorem polarization_identity (D : WeightedStarDatum d 0 j V W T) (u v : V) :
    D.h (D.ΘV u) v + D.h u (D.ΘV v) = (j : ℂ) * D.h u v := by
  simpa using D.derivation_law u v

/-- AW4 positivity: `h_j` is Hermitian and positive definite. -/
structure IsPositive : Prop where
  /-- Hermitian symmetry of `h_j`. -/
  conj_symm : ∀ u v, conj (D.h u v) = D.h v u
  /-- Positive definiteness of `h_j`. -/
  re_pos : ∀ u, u ≠ 0 → 0 < (D.h u u).re

/-- Under AW4 positivity, `h_j` as a `PosHermForm`. -/
def toPosHermForm (hD : D.IsPositive) : PosHermForm V where
  toFun := D.h
  add_left := D.h_add_left
  smul_left := D.h_smul_left
  conj_symm := hD.conj_symm
  re_pos := hD.re_pos

/-- **Q1 Lemma 4.2 + Theorem 0.** If AW1, AW3, AW4 hold in degree `j` for a datum of type
`(d, w)`, every eigenvalue `ρ` of `Θ_j` satisfies `Re ρ = (w + j) / 2`. -/
theorem re_eq_of_hasEigenvalue (hD : D.IsPositive) {ρ : ℂ} (hρ : D.ΘV.HasEigenvalue ρ) :
    ρ.re = ((w + j : ℕ) : ℝ) / 2 :=
  (D.toPosHermForm hD).re_eq_half D.ΘV ((w + j : ℕ) : ℝ)
    (fun u v => by simpa [toPosHermForm] using D.derivation_law u v) hρ

/-- **Q1 Theorem 0, semisimplicity.** In finite dimension, `Θ_j` is semisimple. -/
theorem isSemisimple [FiniteDimensional ℂ V] (hD : D.IsPositive) : D.ΘV.IsSemisimple :=
  (D.toPosHermForm hD).isSemisimple D.ΘV ((w + j : ℕ) : ℝ)
    (fun u v => by simpa [toPosHermForm] using D.derivation_law u v)

/-- The arithmetic curve case `X̄_K` (type `(1, 0)`, degree `j = 1`): `Re ρ = 1/2`. -/
theorem re_eq_half_of_curve {V W T : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup T] [Module ℂ T]
    (D : WeightedStarDatum 1 0 1 V W T) (hD : D.IsPositive) {ρ : ℂ}
    (hρ : D.ΘV.HasEigenvalue ρ) : ρ.re = 1 / 2 := by
  simpa using D.re_eq_of_hasEigenvalue hD hρ

/-- **Non-vacuity (Q1 Prop. 5.1 in dimension one).** For `ρ = 1/2 + iτ`, the line model
`V¹ = V^{2d-1} = V² = ℂ`, `Θ₁ = ρ` on `V^j`, `Θ = conj ρ` on `V^{2d-j}`, `Θ₂ = 1`, `u ∪ v = uv`,
`tr = id`, `*v = conj v` is a datum of type `(1, 0)` in degree `1`. -/
noncomputable def lineModel (τ : ℝ) : WeightedStarDatum 1 0 1 ℂ ℂ ℂ where
  ΘV := (1 / 2 + τ * Complex.I : ℂ) • LinearMap.id
  ΘW := (1 / 2 - τ * Complex.I : ℂ) • LinearMap.id
  ΘT := LinearMap.id
  cup := LinearMap.mul ℂ ℂ
  cup_derivation u v := by
    simp only [LinearMap.id_apply, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    ring
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := (starLinearEquiv ℂ (A := ℂ)).toLinearMap
  star_comm v := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, starLinearEquiv_apply,
      smul_eq_mul, star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    ring

/-- The line model is positive: `h(u, v) = u · conj v`. -/
theorem lineModel_isPositive (τ : ℝ) : (lineModel τ).IsPositive where
  conj_symm u v := by
    simp [h, B, lineModel, mul_comm]
  re_pos u hu := by
    simp only [h, B, lineModel, LinearMap.mul_apply', LinearMap.id_apply, LinearEquiv.coe_coe,
      starLinearEquiv_apply, Complex.star_def, Complex.mul_conj]
    simpa using Complex.normSq_pos.2 hu

/-- **Consistency for every weight.** For any type `(d, w)`, degree `j` and `τ : ℝ`, the line
`V^j = V^{2d-j} = V^{2d} = ℂ` with `Θ_j = (w + j)/2 + iτ`, `Θ_{2d-j} = conj Θ_j + (d - j)`,
`Θ_{2d} = d + w`, `u ∪ v = uv`, `tr = id` and `*v = conj v` is a datum of type `(d, w)` in degree
`j`. In particular `w ≠ 0` is allowed: the structure has no unit and no internal product, so the
positive-weight obstruction (`WeightedAlgebraDatum.eq_bot`, `eq_zero_of_unit`) does not apply. -/
noncomputable def weightedLineModel (d w j : ℕ) (τ : ℝ) : WeightedStarDatum d w j ℂ ℂ ℂ where
  ΘV := (((w + j : ℕ) : ℂ) / 2 + τ * Complex.I) • LinearMap.id
  ΘW := (((w + j : ℕ) : ℂ) / 2 - τ * Complex.I + ((d : ℂ) - j)) • LinearMap.id
  ΘT := ((d + w : ℕ) : ℂ) • LinearMap.id
  cup := LinearMap.mul ℂ ℂ
  cup_derivation u v := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.mul_apply', smul_eq_mul]
    push_cast
    ring
  tr := LinearMap.id
  tr_equivariant x := by simp
  star := (starLinearEquiv ℂ (A := ℂ)).toLinearMap
  star_comm v := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, starLinearEquiv_apply,
      smul_eq_mul, star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, map_div₀, map_ofNat, map_natCast]
    push_cast
    ring

/-- The weighted line model is positive: `h(u, v) = u · conj v`. -/
theorem weightedLineModel_isPositive (d w j : ℕ) (τ : ℝ) :
    (weightedLineModel d w j τ).IsPositive where
  conj_symm u v := by
    simp [h, B, weightedLineModel, mul_comm]
  re_pos u hu := by
    simp only [h, B, weightedLineModel, LinearMap.mul_apply', LinearMap.id_apply,
      LinearEquiv.coe_coe, starLinearEquiv_apply, Complex.star_def, Complex.mul_conj]
    simpa using Complex.normSq_pos.2 hu

/-- **No vacuity at positive weight.** For every `d w j`, a nonzero positive datum of type
`(d, w)` in degree `j` exists; its flow has the eigenvalue `(w + j)/2 + iτ`. -/
theorem exists_positive_nontrivial (d w j : ℕ) (τ : ℝ) :
    ∃ D : WeightedStarDatum d w j ℂ ℂ ℂ, D.IsPositive ∧
      D.ΘV.HasEigenvalue (((w + j : ℕ) : ℂ) / 2 + τ * Complex.I) := by
  refine ⟨weightedLineModel d w j τ, weightedLineModel_isPositive d w j τ, ?_⟩
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : ℂ)) ?_
  refine ⟨?_, one_ne_zero⟩
  simp [weightedLineModel]

end WeightedStarDatum

end WeilRH
