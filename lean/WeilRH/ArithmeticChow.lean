import Mathlib

/-!
# The arithmetic Chow group `ĈH¹(Spec 𝓞_K)` and the arithmetic degree (roadmap C1)

Round 48 of `lean/ROADMAP-arakelov.md`. Source: Gillet–Soulé, *Arithmetic intersection theory*,
Publ. Math. IHÉS 72 (1990), §3.4.3 (p. 131), checked in the local copy
`refs/arakelov/gillet-soule-1990-arithmetic-intersection-theory.pdf`.

For `A = 𝓞_K` the arithmetic variety `X = Spec 𝓞_K` has `X_∞ = Hom(K, ℂ)` (GS's `S`, the set of
complex embeddings), and GS 3.4.2–3.4.3 describe `ĈH¹(X)` by the exact sequence

  `A* → (⊕_{σ ∈ S} ℝ)^{F_∞} → ĈH¹(X) → CH¹(X) → 0`,

so an arithmetic divisor is a pair `(Z, g)`: a divisor `Z` on `Spec 𝓞_K` together with a real
number `g_σ` for each embedding, invariant under complex conjugation `F_∞`, and a principal one is
`(div f, (-log |σ(f)|²)_σ)`. GS 3.4.3 then define

  `deĝ : ĈH¹(Spec 𝓞_K) → ℝ`, `(Z, g) ↦ log #(Z) + ½ Σ_{σ ∈ S} g_σ`,

where `#(Z) = Π #(𝓞_K/𝔭_i)^{n_i}` for `Z = Σ n_i [𝔭_i]`. It is well defined by the product formula.

## Encoding

* Divisors on `Spec 𝓞_K` are encoded as invertible fractional ideals,
  `Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ` (for a Dedekind domain the divisor group is the group of
  invertible fractional ideals). `#(Z)` is Mathlib's `FractionalIdeal.absNorm`, which on an
  integral ideal is `#(𝓞_K/I)`.
* `X_∞` is encoded as `K →+* ℂ`; round 46 proved `X̄_K(ℂ) ≃ (K →+* ℂ)` with `F_∞` corresponding to
  `ComplexEmbedding.conjugate` (`CompactifiedScheme.lean`, `pointsEquiv`).
* `greenSpace K` is the group of `F_∞`-invariant real vectors on `X_∞`, i.e. the Green currents of
  the divisor part, GS 3.4.2 ("`F_∞`-invariant continuous real-valued functions on `X_∞`").

## Main results

* `principal K : Additive Kˣ →+ arithDiv K`, `f ↦ (div f, (-log ‖σ f‖²)_σ)`.
* `ChowGroup K := arithDiv K ⧸ (principal K).range`, i.e. `ĈH¹(Spec 𝓞_K)`.
* `degree K : arithDiv K →+ ℝ` and `deg_principal`: `deĝ (div̂ f) = 0` (the product formula,
  `prod_norm_embeddings`).
* `chowDegree K : ChowGroup K →+ ℝ`, the arithmetic degree of GS 3.4.3, with `chowDegree_mk`.
* `chowDegree_surjective`: `deĝ` is onto `ℝ` for every number field (so `ĈH¹ ≠ 0`, the
  nonvacuity instance), already on classes `(0, g)` with `g` constant.
* `deg_const`: `deĝ (0, c) = ½ · c · [K : ℚ]`.

Round 49 (the exact sequence of GS 3.4.3, p. 131,
`A* → (⊕_{σ ∈ S} ℝ)^{F_∞} → ĈH¹(X) → Cl(A) → 0`, and `ĈH¹(Spec ℤ) ≅ ℝ`):

* `toClass K : ChowGroup K →+ Additive (ClassGroup (𝓞 K))`, `(Z, g) ↦ [Z]`, and
  `toClass_surjective` (the `→ Cl(A) → 0` part).
* `ofGreen K : greenSpace K →+ ChowGroup K`, `g ↦ [(0, g)]`, and `toClass_eq_zero_iff`
  (exactness at `ĈH¹`: the kernel of `toClass` is the image of `ofGreen`).
* `ofGreen_eq_zero_iff` (exactness at the Green vectors: `[(0, g)] = 0` iff `g` is the Green
  vector of some `x ∈ K*` with trivial principal ideal) and `toPrincipalIdeal_eq_one_iff`
  (those `x` are exactly the units of `𝓞_K`), so the kernel is the image of `𝓞_K^* → ⊕ ℝ`.
* `chowDegree_injective_rat` and `chowDegreeEquivRat : ChowGroup ℚ ≃+ ℝ` (GS 3.4.3,
  "if `A = ℤ` then `deg : ĈH¹(Spec ℤ) → ℝ` is an isomorphism, since `ℤ* = μ(ℤ)` and
  `Cl(ℤ) = {1}`"), using Mathlib's `Rat.classNumber_eq`.

## Divergences (recorded in `lean/README.md`)

* The normalization `½ Σ g_σ` is read from GS 3.4.3. That OCR line of the local PDF is partly
  garbled, so the constant was confirmed by consistency: with `g_σ = -log |σ f|²` the degree of a
  principal divisor vanishes exactly for the factor `½` (this is `deg_principal`).
* GS work with general arithmetic rings; this file is the `A = 𝓞_K` case of 3.4.3 only, and
  `ĈH¹` is defined by the quotient of 3.4.3 rather than through Green currents on a general
  arithmetic variety (roadmap C2).
* The comparison with the idele-class description `ĈH¹ ≅ K*\J(K)/U_K` (GS 3.4.3) is not
  formalized. The kernel of `𝓞_K^* → ⊕ ℝ` (GS: `μ(K)`) is not computed; the sequence is stated
  from the Green vectors onward.
-/

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace WeilRH.Arakelov.ArithChow

variable (K : Type) [Field K] [NumberField K]

/-- `F_∞`-invariant real vectors on `X_∞ = Hom(K, ℂ)` (GS 3.4.2): the Green currents for
divisors on `Spec 𝓞_K`. -/
def greenSpace : AddSubgroup ((K →+* ℂ) → ℝ) where
  carrier := {g | ∀ φ, g (ComplexEmbedding.conjugate φ) = g φ}
  add_mem' := by
    intro a b ha hb φ
    simp only [Pi.add_apply, ha φ, hb φ]
  zero_mem' := by intro φ; rfl
  neg_mem' := by
    intro a ha φ
    simp only [Pi.neg_apply, ha φ]

/-- Divisors on `Spec 𝓞_K`, as invertible fractional ideals written additively. -/
abbrev Div := Additive (FractionalIdeal (𝓞 K)⁰ K)ˣ

/-- Arithmetic divisors `(Z, g)` on `Spec 𝓞_K` (GS 3.4.2–3.4.3). -/
abbrev arithDiv := Div K × greenSpace K

/-- The Green vector of `f`: `σ ↦ -log ‖σ f‖²` (GS 3.4.3). -/
def greenOf (x : Kˣ) : (K →+* ℂ) → ℝ := fun φ => -Real.log (‖φ (x : K)‖ ^ 2)

omit [NumberField K] in
lemma greenOf_mem (x : Kˣ) : greenOf K x ∈ greenSpace K := by
  intro φ
  simp only [greenOf, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

omit [NumberField K] in
lemma embedding_ne_zero (x : Kˣ) (φ : K →+* ℂ) : ‖φ (x : K)‖ ≠ 0 := by
  rw [norm_ne_zero_iff, map_ne_zero]
  exact x.ne_zero

omit [NumberField K] in
lemma greenOf_mul (x y : Kˣ) : greenOf K (x * y) = greenOf K x + greenOf K y := by
  funext φ
  have hx := embedding_ne_zero K x φ
  have hy := embedding_ne_zero K y φ
  simp only [greenOf, Units.val_mul, map_mul, norm_mul, mul_pow, Pi.add_apply]
  rw [Real.log_mul (pow_ne_zero 2 hx) (pow_ne_zero 2 hy)]
  ring

/-- The Green part of the principal divisor map, as a homomorphism. -/
def greenHom : Additive Kˣ →+ greenSpace K where
  toFun x := ⟨greenOf K (Additive.toMul x), greenOf_mem K _⟩
  map_zero' := by
    ext φ
    simp [greenOf]
  map_add' x y := by
    ext φ
    simp [toMul_add, greenOf_mul]

/-- The principal arithmetic divisor `div̂ f = (div f, (-log ‖σ f‖²)_σ)` (GS 3.4.3). -/
def principal : Additive Kˣ →+ arithDiv K :=
  AddMonoidHom.prod (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 K) K)) (greenHom K)

/-- `ĈH¹(Spec 𝓞_K)`: arithmetic divisors modulo principal ones (GS 3.4.3). -/
abbrev ChowGroup := arithDiv K ⧸ (principal K).range

/-- The norm of an invertible fractional ideal is a nonzero rational. -/
lemma absNorm_unit_ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact I.ne_zero

/-- `log #(Z)` as a homomorphism from divisors to `ℝ`. -/
def logNorm : Div K →+ ℝ where
  toFun I := Real.log ((FractionalIdeal.absNorm ((Additive.toMul I : (FractionalIdeal _ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)
  map_zero' := by simp
  map_add' I J := by
    simp only [toMul_add, Units.val_mul, map_mul, Rat.cast_mul]
    exact Real.log_mul (by exact_mod_cast absNorm_unit_ne_zero K _)
      (by exact_mod_cast absNorm_unit_ne_zero K _)

/-- `½ Σ_σ g_σ` as a homomorphism. -/
def halfSum : greenSpace K →+ ℝ where
  toFun g := (1 / 2 : ℝ) * ∑ φ, (g : (K →+* ℂ) → ℝ) φ
  map_zero' := by simp
  map_add' g h := by
    simp only [AddSubgroup.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    ring

/-- The arithmetic degree `deĝ (Z, g) = log #(Z) + ½ Σ_σ g_σ` on arithmetic divisors
(GS 3.4.3). -/
def degree : arithDiv K →+ ℝ :=
  (logNorm K).comp (AddMonoidHom.fst _ _) + (halfSum K).comp (AddMonoidHom.snd _ _)

lemma degree_apply (D : arithDiv K) : degree K D = logNorm K D.1 + halfSum K D.2 := rfl

/-- The infinite part of the product formula over complex embeddings:
`Π_{σ : K → ℂ} ‖σ x‖ = |N_{K/ℚ}(x)|`. -/
theorem prod_norm_embeddings (x : K) :
    ∏ φ : K →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ x‖)
      (fun f => ‖f x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply], ← h]
  simp [Complex.norm_ratCast]

/-- **Product formula for `ĈH¹`**: the degree of a principal arithmetic divisor is zero
(GS 3.4.3, "well defined by the product formula"). -/
theorem deg_principal (x : Additive Kˣ) : degree K (principal K x) = 0 := by
  set y : Kˣ := Additive.toMul x
  have hlog : logNorm K (principal K x).1 = Real.log |((Algebra.norm ℚ (y : K) : ℚ) : ℝ)| := by
    simp only [logNorm, principal, AddMonoidHom.prod_apply, MonoidHom.toAdditive_apply_apply,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, coe_toPrincipalIdeal,
      FractionalIdeal.absNorm_span_singleton, Rat.cast_abs, y]
  have hsum : halfSum K (principal K x).2 = -Real.log (∏ φ : K →+* ℂ, ‖φ (y : K)‖) := by
    simp only [halfSum, principal, AddMonoidHom.prod_apply, greenHom, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, greenOf, y]
    rw [Real.log_prod (fun φ _ => embedding_ne_zero K _ φ)]
    simp only [Real.log_pow, Finset.sum_neg_distrib]
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [degree_apply, hlog, hsum, prod_norm_embeddings]
  ring

/-- The arithmetic degree `deĝ : ĈH¹(Spec 𝓞_K) → ℝ` (GS 3.4.3). -/
def chowDegree : ChowGroup K →+ ℝ :=
  QuotientAddGroup.lift _ (degree K) (by
    rintro _ ⟨x, rfl⟩
    exact deg_principal K x)

@[simp] theorem chowDegree_mk (D : arithDiv K) :
    chowDegree K (QuotientAddGroup.mk D) = degree K D := rfl

/-- The constant Green vector `c`. -/
def constGreen (c : ℝ) : greenSpace K := ⟨fun _ => c, fun _ => rfl⟩

/-- `deĝ (0, c) = ½ · c · [K : ℚ]`. -/
theorem deg_const (c : ℝ) :
    degree K (0, constGreen K c) = (1 / 2 : ℝ) * c * (Module.finrank ℚ K : ℝ) := by
  rw [degree_apply]
  simp only [map_zero, zero_add, halfSum, constGreen, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  ring

/-- **Nonvacuity**: `deĝ : ĈH¹(Spec 𝓞_K) → ℝ` is surjective for every number field `K`
(in particular `ĈH¹(Spec 𝓞_K) ≠ 0`); `K = ℚ` gives GS's isomorphism `ĈH¹(Spec ℤ) ≅ ℝ` on
the surjectivity side. -/
theorem chowDegree_surjective : Function.Surjective (chowDegree K) := by
  intro t
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  refine ⟨QuotientAddGroup.mk (0, constGreen K (2 * t / Module.finrank ℚ K)), ?_⟩
  rw [chowDegree_mk, deg_const]
  field_simp

/-- The class map on divisors: `Z ↦ [Z] ∈ Cl(𝓞_K)`, written additively. -/
def divToClass : Div K →+ Additive (ClassGroup (𝓞 K)) :=
  MonoidHom.toAdditive (ClassGroup.mk K)

/-- A principal fractional ideal has trivial class. -/
lemma classGroup_mk_principal (x : Kˣ) : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(x : K), rfl⟩⟩

/-- An invertible fractional ideal with trivial class is principal. -/
lemma exists_of_classGroup_mk_eq_one {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = 1) : ∃ x : Kˣ, toPrincipalIdeal (𝓞 K) K x = I := by
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨x, hx⟩ := (mem_principal_ideals_iff (R := 𝓞 K) (K := K) (I := I)).mpr (by
    obtain ⟨y, hy⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ h
    refine ⟨y, ?_⟩
    apply Subtype.coe_injective
    simp only [FractionalIdeal.val_eq_coe, FractionalIdeal.coe_spanSingleton, hy])
  exact ⟨x, hx⟩

/-- The forgetful map `ĈH¹(Spec 𝓞_K) → Cl(𝓞_K)`, `(Z, g) ↦ [Z]` (GS 3.4.3, the map
`ĈH¹(X) → CH¹(X)`). -/
def toClass : ChowGroup K →+ Additive (ClassGroup (𝓞 K)) :=
  QuotientAddGroup.lift _ ((divToClass K).comp (AddMonoidHom.fst _ _)) (by
    rintro _ ⟨x, rfl⟩
    show Additive.ofMul (ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (Additive.toMul x))) = 0
    rw [classGroup_mk_principal]; rfl)

@[simp] lemma toClass_mk (D : arithDiv K) :
    toClass K (QuotientAddGroup.mk D) = Additive.ofMul (ClassGroup.mk K (Additive.toMul D.1)) :=
  rfl

/-- `ĈH¹(Spec 𝓞_K) → Cl(𝓞_K)` is surjective (GS 3.4.3, `ĈH¹(X) → CH¹(X) → 0`). -/
theorem toClass_surjective : Function.Surjective (toClass K) := by
  intro c
  have key : ∀ y : ClassGroup (𝓞 K), ∃ a, toClass K a = Additive.ofMul y := fun y =>
    ClassGroup.induction (K := K) (fun I => ⟨QuotientAddGroup.mk (Additive.ofMul I, 0), rfl⟩) y
  exact key (Additive.toMul c)

/-- The map `(F_∞-invariant Green vectors) → ĈH¹(Spec 𝓞_K)`, `g ↦ [(0, g)]` (GS 3.4.3). -/
def ofGreen : greenSpace K →+ ChowGroup K :=
  (QuotientAddGroup.mk' _).comp (AddMonoidHom.inr _ _)

/-- **Exactness at `ĈH¹`**: a class maps to `0 ∈ Cl(𝓞_K)` iff it is the class of a pure Green
vector `(0, g)` (GS 3.4.3). -/
theorem toClass_eq_zero_iff (c : ChowGroup K) :
    toClass K c = 0 ↔ ∃ g, ofGreen K g = c := by
  induction c using QuotientAddGroup.induction_on with
  | H D =>
    obtain ⟨Z, g⟩ := D
    constructor
    · intro h
      have h1 : ClassGroup.mk K (Additive.toMul Z) = 1 := by
        simpa [toClass_mk] using h
      obtain ⟨x, hx⟩ := exists_of_classGroup_mk_eq_one K h1
      refine ⟨g - greenHom K (Additive.ofMul x), ?_⟩
      show (QuotientAddGroup.mk _ : ChowGroup K) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq]
      refine ⟨Additive.ofMul x, ?_⟩
      refine Prod.ext ?_ ?_
      · show Additive.ofMul (toPrincipalIdeal (𝓞 K) K x) = -0 + Z
        rw [hx, neg_zero, zero_add]; rfl
      · simp [principal]
    · rintro ⟨g', hg⟩
      rw [← hg]
      show Additive.ofMul (ClassGroup.mk K (Additive.toMul (0 : Div K))) = 0
      simp

/-- **Kernel of the Green map**: `[(0, g)] = 0` iff `g` is the Green vector `(-log ‖σ u‖²)_σ` of
some `u ∈ K*` with trivial principal ideal, i.e. of a unit of `𝓞_K` (GS 3.4.3: `A* → ⊕ ℝ`). -/
theorem ofGreen_eq_zero_iff (g : greenSpace K) :
    ofGreen K g = 0 ↔ ∃ x : Kˣ, toPrincipalIdeal (𝓞 K) K x = 1 ∧ greenHom K (Additive.ofMul x) = g := by
  show (QuotientAddGroup.mk _ : ChowGroup K) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Additive.toMul x, ?_, ?_⟩
    · have := congr_arg Prod.fst hx
      exact this
    · have := congr_arg Prod.snd hx
      exact this
  · rintro ⟨x, h1, h2⟩
    refine ⟨Additive.ofMul x, ?_⟩
    refine Prod.ext ?_ ?_
    · show Additive.ofMul (toPrincipalIdeal (𝓞 K) K x) = 0
      rw [h1]; rfl
    · simp [principal, h2]

/-- `toPrincipalIdeal x = 1` iff `x` is a unit of `𝓞_K`. -/
lemma toPrincipalIdeal_eq_one_iff (x : Kˣ) :
    toPrincipalIdeal (𝓞 K) K x = 1 ↔ ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = x := by
  rw [toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  have hinv : ∀ z : (𝓞 K)ˣ, (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((z : 𝓞 K) : K) = 1 := by
    intro z
    have : (((z⁻¹ * z : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by simp
    simpa only [Units.val_mul, map_mul] using this
  constructor
  · rintro ⟨z, hz⟩
    have hbx : ((z : 𝓞 K) : K) * (x : K) = 1 := by
      simpa only [Units.smul_def, Algebra.smul_def] using hz
    refine ⟨z⁻¹, ?_⟩
    calc (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)
        = (((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * (((z : 𝓞 K) : K) * (x : K)) := by rw [hbx, mul_one]
      _ = ((((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) * ((z : 𝓞 K) : K)) * (x : K) := by ring
      _ = (x : K) := by rw [hinv, one_mul]
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def, ← hu]
    exact hinv u

@[simp] lemma chowDegree_ofGreen (g : greenSpace K) : chowDegree K (ofGreen K g) = halfSum K g := by
  show degree K (0, g) = _
  rw [degree_apply, map_zero, zero_add]

/-- `Cl(ℤ) = 1`: the class group of `𝓞_ℚ` is trivial (Mathlib's `Rat.classNumber_eq`). -/
instance : Subsingleton (ClassGroup (𝓞 ℚ)) := by
  have h := Rat.classNumber_eq
  unfold NumberField.classNumber at h
  exact Fintype.card_le_one_iff_subsingleton.mp h.le

/-- For `K = ℚ`, `deĝ : ĈH¹(Spec ℤ) → ℝ` is injective. -/
theorem chowDegree_injective_rat : Function.Injective (chowDegree ℚ) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  have h0 : toClass ℚ c = 0 := Subsingleton.elim (α := Additive (ClassGroup (𝓞 ℚ))) _ _
  obtain ⟨g, rfl⟩ := (toClass_eq_zero_iff ℚ c).mp h0
  rw [chowDegree_ofGreen] at hc
  have hsum : (1 / 2 : ℝ) * ((g : (ℚ →+* ℂ) → ℝ) (Rat.castHom ℂ)) = 0 := by
    simpa only [halfSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Fintype.sum_subsingleton _ (Rat.castHom ℂ)] using hc
  have hg : g = 0 := by
    ext φ
    rw [Subsingleton.elim φ (Rat.castHom ℂ)]
    simpa using hsum
  rw [hg, map_zero]

/-- **GS 3.4.3 for `Spec ℤ`**: `deĝ : ĈH¹(Spec ℤ) ≃ ℝ`. -/
def chowDegreeEquivRat : ChowGroup ℚ ≃+ ℝ :=
  AddEquiv.ofBijective (chowDegree ℚ) ⟨chowDegree_injective_rat, chowDegree_surjective ℚ⟩

@[simp] lemma chowDegreeEquivRat_apply (c : ChowGroup ℚ) :
    chowDegreeEquivRat c = chowDegree ℚ c := rfl

end WeilRH.Arakelov.ArithChow

end
