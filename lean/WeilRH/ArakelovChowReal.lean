import Mathlib
import WeilRH.ArithmeticChow
import WeilRH.CompactifiedDeligne

/-!
# `H²(X̄_K, ℝ(1)) ≅ ĈH¹(X̄_K)_ℝ` through the arithmetic degree (round 57)

Round 57 of `lean/ROADMAP-arakelov.md` (Flach–Morin path). Flach–Morin 2020 (local copy
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`), proof of
Prop. 4.14 (p. 535): `CH^n(X̄)_C ≃ H^{2n}(X̄, C(n))` by their 2018 paper [13, Prop. 2.11], where
`CH^n(X̄)_ℝ` is "the Arakelov–Chow group with real coefficients" (Notation 4.13, p. 534, citing
Gillet–Soulé [18, 5.1.1] and [19, 3.3.3]). This file proves the case `n = 1`, `X̄ = X̄_K`:

* `ChowR K`: the **real-coefficient** arithmetic Chow group of `Spec 𝓞_K`,
  `((Div ⊗_ℤ ℝ) × (ℝ-Green vectors)) / ℝ-span(div̂ f)`, built on round 48's `arithDiv` and
  `principal` (GS 1990 §3.4.3, p. 131).
* `degreeR`, `chowDegreeR`: the `ℝ`-linear extension of the arithmetic degree
  `(Z, g) ↦ log #Z + ½ Σ g_σ`; `chowDegreeR_comp`: it restricts to round 48's `chowDegree`.
* `chowDegreeR_surjective`, `chowDegreeR_injective`, `chowDegreeREquiv : ChowR K ≃ₗ[ℝ] ℝ`.
  Injectivity uses (i) finiteness of the class group (Mathlib `instFintypeClassGroup`), so every
  divisor is principal up to a Green vector after `⊗ ℝ`; (ii) Dirichlet's theorem in the form of
  round 55's `range_regR` (the regulator `⊗ ℝ` hits the sum-zero hyperplane), so every degree-zero
  Green vector is an `ℝ`-combination of Green vectors of units (`mem_relR_of_halfSumR_eq_zero`).
* `chowRToH2 : ChowR K ≃ₗ[ℝ] H²(X̄_K, ℝ(1))` (round 56's `compactOne_Hbar_two`), and
  `compactOne_Hbar_two_chowRToH2`: under `H² ≅ ℝ` it is the arithmetic degree.

## Canonical versus chosen

* `chowDegreeR` is canonical (GS's degree, `ℝ`-linearly extended).
* `compactOne_Hbar_two` is round 55/56's identification `H²_c = coker(reg ⊗ ℝ) ≅ ℝ` via `Σ_w`,
  which is canonical given the modelled normalization of `H¹_D = ℝ^{InfinitePlace K}` (round 55).
  So `chowRToH2` is canonical up to that normalization; it is **not** shown to be the map of
  FM [13, Prop. 2.11] (that paper is not local; its construction is not formalized).

## Refutation recorded (not formalized)

It is natural to read "`⊗ ℝ`" as `ĈH¹ ⊗_ℤ ℝ`. That is **not** `ℝ` once `r₁ + r₂ ≥ 2`: the kernel of
the degree on `ĈH¹` contains the real torus `H/Λ` (`H` the degree-zero Green vectors, `Λ` the
log-unit lattice of rank `r₁ + r₂ - 1`), a divisible group whose `⊗_ℤ ℝ` is a nonzero ℝ-space
of continuum dimension. The correct object is the real-coefficient group `ChowR`, where one
quotients by the `ℝ`-span of principal divisors. For `K = ℚ` both agree (round 49's
`chowDegreeEquivRat`).
-/

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped TensorProduct nonZeroDivisors

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace WeilRH.Arakelov.ArithChowReal

open WeilRH.Arakelov.ArithChow
section

variable (K : Type) [Field K] [NumberField K]

/-- Real `F_∞`-invariant Green vectors on `X_∞ = Hom(K, ℂ)` (the `ℝ`-span of GS 3.4.2's). -/
def greenR : Submodule ℝ ((K →+* ℂ) → ℝ) where
  carrier := {g | ∀ φ, g (ComplexEmbedding.conjugate φ) = g φ}
  add_mem' := by
    intro a b ha hb φ
    simp only [Pi.add_apply, ha φ, hb φ]
  zero_mem' := by intro φ; rfl
  smul_mem' := by
    intro c g hg φ
    simp only [Pi.smul_apply, hg φ]

/-- Divisors with real coefficients. -/
abbrev DivR := ℝ ⊗[ℤ] ArithChow.Div K

/-- Arithmetic divisors with real coefficients. -/
abbrev arithDivR := DivR K × greenR K

/-- Integral Green vectors are real Green vectors. -/
def toGreenR : greenSpace K →+ greenR K where
  toFun g := ⟨g, g.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The comparison `arithDiv K → arithDivR K`, `(Z, g) ↦ (1 ⊗ Z, g)`. -/
def inc : arithDiv K →+ arithDivR K :=
  AddMonoidHom.prod
    ((TensorProduct.mk ℤ ℝ (ArithChow.Div K) 1).toAddMonoidHom.comp (AddMonoidHom.fst _ _))
    ((toGreenR K).comp (AddMonoidHom.snd _ _))

omit [NumberField K] in
@[simp] lemma inc_apply (D : arithDiv K) :
    inc K D = ((1 : ℝ) ⊗ₜ[ℤ] D.1, toGreenR K D.2) := rfl

/-- The `ℝ`-span of the principal arithmetic divisors. -/
def relR : Submodule ℝ (arithDivR K) :=
  Submodule.span ℝ (Set.range fun x => inc K (principal K x))

/-- `ĈH¹(Spec 𝓞_K)_ℝ`, the arithmetic Chow group with real coefficients. -/
abbrev ChowR := arithDivR K ⧸ relR K

/-- `log #` on real divisors (`ℝ`-linear extension of round 48's `logNorm`). -/
def logNormR : DivR K →ₗ[ℝ] ℝ := (logNorm K).toIntLinearMap.liftBaseChange ℝ

/-- `½ Σ_σ g_σ` on real Green vectors. -/
def halfSumR : greenR K →ₗ[ℝ] ℝ where
  toFun g := (1 / 2 : ℝ) * ∑ φ, (g : (K →+* ℂ) → ℝ) φ
  map_add' g h := by
    simp only [Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c g := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

/-- The arithmetic degree on real arithmetic divisors. -/
def degreeR : arithDivR K →ₗ[ℝ] ℝ :=
  logNormR K ∘ₗ LinearMap.fst ℝ _ _ + halfSumR K ∘ₗ LinearMap.snd ℝ _ _

lemma degreeR_apply (v : arithDivR K) : degreeR K v = logNormR K v.1 + halfSumR K v.2 := rfl

lemma degreeR_inc (D : arithDiv K) : degreeR K (inc K D) = degree K D := by
  rw [degreeR_apply, inc_apply, degree_apply]
  simp only [logNormR, LinearMap.liftBaseChange_one_tmul,
    AddMonoidHom.coe_toIntLinearMap]
  rfl

lemma relR_le_ker : relR K ≤ LinearMap.ker (degreeR K) := by
  rw [relR, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, degreeR_inc, deg_principal]

/-- The degree on `ĈH¹(Spec 𝓞_K)_ℝ`. -/
def chowDegreeR : ChowR K →ₗ[ℝ] ℝ := (relR K).liftQ (degreeR K) (relR_le_ker K)

/-- The comparison `ĈH¹ → ĈH¹_ℝ`. -/
def toChowR : ChowGroup K →+ ChowR K :=
  QuotientAddGroup.lift _ ((relR K).mkQ.toAddMonoidHom.comp (inc K)) (by
    rintro _ ⟨x, rfl⟩
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩)

/-- On integral classes the real degree is round 48's `chowDegree`. -/
theorem chowDegreeR_comp (c : ChowGroup K) : chowDegreeR K (toChowR K c) = chowDegree K c := by
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    simp only [toChowR, QuotientAddGroup.lift_mk, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, chowDegreeR, Submodule.liftQ_apply,
      degreeR_inc]
    rfl

/-- The real degree is onto `ℝ`. -/
theorem chowDegreeR_surjective : Function.Surjective (chowDegreeR K) := by
  intro y
  obtain ⟨c, hc⟩ := chowDegree_surjective K y
  exact ⟨toChowR K c, by rw [chowDegreeR_comp, hc]⟩

/-! ### Injectivity -/

/-- Every divisor is, modulo `relR`, a Green vector (finiteness of the class group). -/
lemma exists_green_of_div (D : ArithChow.Div K) :
    ∃ g : greenR K, (((1 : ℝ) ⊗ₜ[ℤ] D, (0 : greenR K)) + (0, g) : arithDivR K) ∈ relR K := by
  classical
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hmk : ClassGroup.mk K ((Additive.toMul D) ^ h) = 1 := by
    rw [map_pow, hh, pow_card_eq_one]
  obtain ⟨x, hx⟩ := exists_of_classGroup_mk_eq_one K hmk
  refine ⟨(1 / (h : ℝ)) • toGreenR K (greenHom K (Additive.ofMul x)), ?_⟩
  have hmem : inc K (principal K (Additive.ofMul x)) ∈ relR K :=
    Submodule.subset_span ⟨_, rfl⟩
  have key : inc K (principal K (Additive.ofMul x)) =
      ((h : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] D), toGreenR K (greenHom K (Additive.ofMul x))) := by
    rw [inc_apply]
    congr 1
    show (1 : ℝ) ⊗ₜ[ℤ] (Additive.ofMul (toPrincipalIdeal (𝓞 K) K x) : ArithChow.Div K) = _
    rw [hx]
    have : (Additive.ofMul ((Additive.toMul D) ^ h) : ArithChow.Div K) = h • D := by
      simp [ofMul_pow]
    rw [this, TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℝ]
  have hsmul := (relR K).smul_mem (1 / (h : ℝ)) hmem
  rw [key] at hsmul
  convert hsmul using 1
  ext
  · simp only [Prod.fst_add, add_zero, Prod.smul_fst, smul_smul]
    rw [div_mul_cancel₀ 1 (by exact_mod_cast hpos.ne'), one_smul]
  · simp only [Prod.snd_add, zero_add, Prod.smul_snd]

/-- Green vectors of units lie in `relR`. -/
lemma unit_green_mem (u : (𝓞 K)ˣ) :
    ((0 : DivR K), toGreenR K (greenHom K (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) u))))
      ∈ relR K := by
  have hmem : inc K (principal K (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) u))) ∈ relR K :=
    Submodule.subset_span ⟨_, rfl⟩
  have h1 : toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u) = 1 :=
    (toPrincipalIdeal_eq_one_iff K _).mpr ⟨u, rfl⟩
  convert hmem using 1
  rw [inc_apply]
  congr 1
  show (0 : DivR K) = (1 : ℝ) ⊗ₜ[ℤ]
    (Additive.ofMul (toPrincipalIdeal (𝓞 K) K (Units.map (algebraMap (𝓞 K) K) u)) : ArithChow.Div K)
  rw [h1, ofMul_one, TensorProduct.tmul_zero]

omit [NumberField K] in
/-- A real Green vector is constant on the fibres of `X_∞ → InfinitePlace K`. -/
lemma greenR_eq_embedding (g : greenR K) (φ : K →+* ℂ) :
    (g : (K →+* ℂ) → ℝ) φ = (g : (K →+* ℂ) → ℝ) (InfinitePlace.mk φ).embedding := by
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk φ)) with h | h
  · rw [h]
  · conv_lhs => rw [← h]
    exact g.2 _

/-- `Σ_φ g_φ = Σ_w mult(w) g_{w}` for a real Green vector. -/
lemma sum_greenR (g : greenR K) :
    ∑ φ, (g : (K →+* ℂ) → ℝ) φ =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (g : (K →+* ℂ) → ℝ) w.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (fun φ hφ => by
      rw [greenR_eq_embedding K g φ, (Finset.mem_filter.mp hφ).2]),
    Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

/-- The `ℝ`-linear map `unitsR K → greenR K`, `t ↦ (φ ↦ reg(t)(mk φ) / mult(mk φ))`. -/
def greenOfUnitsR : unitsR K →ₗ[ℝ] greenR K where
  toFun t := ⟨fun φ => regR K t (InfinitePlace.mk φ) / mult (InfinitePlace.mk φ), by
    intro φ
    simp only [InfinitePlace.mk_conjugate_eq]⟩
  map_add' s t := by
    ext φ
    simp only [map_add, Pi.add_apply, add_div, Submodule.coe_add]
  map_smul' c t := by
    ext φ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply,
      Submodule.coe_smul]

lemma greenOfUnitsR_tmul (u : (𝓞 K)ˣ) :
    greenOfUnitsR K (1 ⊗ₜ unitClass K u) =
      (-(1 / 2 : ℝ)) • toGreenR K (greenHom K (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) u))) := by
  ext φ
  simp only [greenOfUnitsR, LinearMap.coe_mk, AddHom.coe_mk, regR_tmul, regulatorMap_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, toGreenR, greenHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, greenOf, toMul_ofMul]
  have hm : (mult (InfinitePlace.mk φ) : ℝ) ≠ 0 := by
    exact_mod_cast (mult_pos (w := InfinitePlace.mk φ)).ne'
  rw [mul_div_cancel_left₀ _ hm, InfinitePlace.apply, Real.log_pow]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  push_cast
  ring

lemma greenOfUnitsR_mem (t : unitsR K) : ((0 : DivR K), greenOfUnitsR K t) ∈ relR K := by
  induction t using TensorProduct.inductionOn with
  | tmul r ℓ =>
    obtain ⟨x, -, hx⟩ := ℓ.2
    have hℓ : ℓ = unitClass K (Additive.toMul x) := Subtype.ext (by
      rw [unitClass_coe, ← hx]; rfl)
    have : r ⊗ₜ[ℤ] ℓ = r • ((1 : ℝ) ⊗ₜ[ℤ] ℓ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, hℓ, greenOfUnitsR_tmul, smul_smul]
    have h0 : ((0 : DivR K),
        (r * -(1 / 2 : ℝ)) • toGreenR K (greenHom K
          (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) (Additive.toMul x))))) =
        (r * -(1 / 2 : ℝ)) • ((0 : DivR K), toGreenR K (greenHom K
          (Additive.ofMul (Units.map (algebraMap (𝓞 K) K) (Additive.toMul x))))) := by
      simp
    rw [h0]
    exact (relR K).smul_mem _ (unit_green_mem K _)
  | add s t hs ht =>
    have : ((0 : DivR K), greenOfUnitsR K (s + t)) =
        ((0 : DivR K), greenOfUnitsR K s) + ((0 : DivR K), greenOfUnitsR K t) := by
      simp
    rw [this]
    exact (relR K).add_mem hs ht

/-- **Degree-zero real Green vectors are `ℝ`-combinations of unit Green vectors** (Dirichlet,
via round 55's `range_regR`). -/
lemma mem_relR_of_halfSumR_eq_zero (g : greenR K) (hg : halfSumR K g = 0) :
    ((0 : DivR K), g) ∈ relR K := by
  set F : InfinitePlace K → ℝ := fun w => (mult w : ℝ) * (g : (K →+* ℂ) → ℝ) w.embedding
  have hF : F ∈ LinearMap.ker (sumMap K) := by
    rw [LinearMap.mem_ker]
    have h2 : ∑ φ, (g : (K →+* ℂ) → ℝ) φ = 0 := by
      have := hg
      simp only [halfSumR, LinearMap.coe_mk, AddHom.coe_mk] at this
      linarith
    rw [sum_greenR] at h2
    simpa [sumMap, F] using h2
  rw [← range_regR] at hF
  obtain ⟨t, ht⟩ := hF
  have hgt : greenOfUnitsR K t = g := by
    ext φ
    simp only [greenOfUnitsR, LinearMap.coe_mk, AddHom.coe_mk, ht, F]
    have hm : (mult (InfinitePlace.mk φ) : ℝ) ≠ 0 := by
      exact_mod_cast (mult_pos (w := InfinitePlace.mk φ)).ne'
    rw [mul_div_cancel_left₀ _ hm, ← greenR_eq_embedding]
  rw [← hgt]
  exact greenOfUnitsR_mem K t

/-- The kernel of the real degree is the span of principal divisors. -/
theorem ker_degreeR : LinearMap.ker (degreeR K) ≤ relR K := by
  intro v hv
  -- reduce the divisor part to a Green vector
  have hdiv : ∀ t : DivR K, ∃ g : greenR K, ((t, (0 : greenR K)) + (0, g) : arithDivR K) ∈ relR K := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul r D =>
      obtain ⟨g, hg⟩ := exists_green_of_div K D
      refine ⟨r • g, ?_⟩
      have := (relR K).smul_mem r hg
      convert this using 1
      ext
      · simp [TensorProduct.smul_tmul']
      · simp
    | add s t hs ht =>
      obtain ⟨g₁, h₁⟩ := hs
      obtain ⟨g₂, h₂⟩ := ht
      refine ⟨g₁ + g₂, ?_⟩
      have := (relR K).add_mem h₁ h₂
      convert this using 1
      ext <;> simp
  obtain ⟨g, hg⟩ := hdiv v.1
  -- `v = r + (0, v.2 - g)` with `r ∈ relR`
  have hdecomp : v = ((v.1, (0 : greenR K)) + (0, g)) + ((0 : DivR K), v.2 - g) := by
    ext <;> simp
  have hdeg : degreeR K ((0 : DivR K), v.2 - g) = 0 := by
    have h0 : degreeR K ((v.1, (0 : greenR K)) + (0, g)) = 0 := relR_le_ker K hg
    have hv0 : degreeR K v = 0 := hv
    rw [hdecomp, map_add, h0, zero_add] at hv0
    exact hv0
  have hgr : halfSumR K (v.2 - g) = 0 := by
    simpa [degreeR_apply] using hdeg
  rw [hdecomp]
  exact (relR K).add_mem hg (mem_relR_of_halfSumR_eq_zero K _ hgr)

/-- The real degree is injective. -/
theorem chowDegreeR_injective : Function.Injective (chowDegreeR K) := by
  rw [← LinearMap.ker_eq_bot, chowDegreeR, Submodule.ker_liftQ_eq_bot _ _ _ (ker_degreeR K)]

/-- **`ĈH¹(Spec 𝓞_K)_ℝ ≅ ℝ` via the arithmetic degree.** -/
def chowDegreeREquiv : ChowR K ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (chowDegreeR K) ⟨chowDegreeR_injective K, chowDegreeR_surjective K⟩

@[simp] lemma chowDegreeREquiv_apply (c : ChowR K) : chowDegreeREquiv K c = chowDegreeR K c := rfl

/-- **`ĈH¹(X̄_K)_ℝ ≅ H²(X̄_K, ℝ(1))`** (FM [13, Prop. 2.11] as cited on FM p. 535, case `n = 1`),
through the arithmetic degree and round 56's `H² ≅ ℝ`. -/
def chowRToH2 : ChowR K ≃ₗ[ℝ] degSub ℝ 2 2 :=
  (chowDegreeREquiv K).trans compactOne_Hbar_two.symm

/-- Under `H² ≅ ℝ`, the identification is the arithmetic degree. -/
theorem compactOne_Hbar_two_chowRToH2 (c : ChowR K) :
    compactOne_Hbar_two (chowRToH2 K c) = chowDegreeR K c := by
  simp [chowRToH2]

end

end WeilRH.Arakelov.ArithChowReal
