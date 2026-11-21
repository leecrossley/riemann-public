import WeilRH.ArithmeticVariety

/-!
# Complex points of an arithmetic variety (Gillet–Soulé 1990, §3.1–3.2)

Roadmap target A2 of `lean/ROADMAP-arakelov.md`, completed in round 45. Source: Gillet–Soulé,
*Arithmetic intersection theory*, Publ. Math. IHÉS 72 (1990), Definition 3.1.1 (p. 124) and
Definition 3.2.1 (p. 125); local copy `refs/arakelov/gillet-soule-1990-arithmetic-intersection-theory.pdf`.

GS 3.2.1: for `σ ∈ S` write `X_σ = X ⊗_σ ℂ`, `X_S = ⊔_{σ ∈ S} X_σ`, and `X_∞ = X_S(ℂ)`; "the
conjugate-linear automorphism `F_∞` of `ℂ^S` induces a continuous involution of `X_∞`".

* `ArithmeticRing.exists_eval`, `conj_mem`, `conjS`, `F_apply`: the involution `F_∞` of an arithmetic
  ring is forced to be `F_∞(x)_τ = conj (x_{τ̄})` with `τ̄ = conj ∘ τ`, and `S` is closed under
  complex conjugation. This is implicit in GS 3.1.1 (proved here from the axioms: every
  conjugate-linear ring endomorphism of `ℂ^S` composed with a coordinate is a conjugated coordinate,
  and `F_∞ ∘ δ = δ` identifies which one).
* `ArithmeticVariety.complexPoints V` is `X_∞` as a set: pairs `(σ, x)` with `σ ∈ S` and
  `x : Spec ℂ → X` lying over `Spec σ : Spec ℂ → Spec A`, i.e. the `ℂ`-points of `X_σ`, summed
  over `σ`. `ArithmeticVariety.Finf` is the involution induced by `F_∞`:
  `(σ, x) ↦ (σ̄, x ∘ Spec(conj))`; `Finf_Finf` proves it is an involution.
* `ArithmeticVariety.complexPointsBaseEquiv`: for `X = Spec A`, `X_∞ ≃ S` compatibly with
  `F_∞ ↦ (σ ↦ σ̄)`. `ArithmeticVariety.complexPointsSpecEquiv K`: for `X = Spec 𝓞 K`,
  `X_∞ ≃ (K →+* ℂ)`, carrying `F_∞` to `NumberField.ComplexEmbedding.conjugate`.

## Divergence from Gillet–Soulé

`X_∞` is encoded as a **set with an involution**, not as the analytic space / complex manifold
associated with `X_S` (GS 3.2.1): Mathlib has no analytification of schemes over `ℂ`. The topology,
the complex-manifold structure (GS: "since `X_F` is smooth, `X_∞` is a complex manifold") and the
forms and currents of GS 3.2.1 are Tier B of the roadmap. Continuity of `F_∞` is therefore not
stated. The base ring lives in `Type` (universe 0) so that `Spec ℂ` and `X` share a universe.
-/

open AlgebraicGeometry CategoryTheory ComplexConjugate

namespace WeilRH.Arakelov

namespace ArithmeticRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsRegularRing A] (R : ArithmeticRing A)

/-- Every coordinate of `F_∞` is the conjugate of a coordinate: for each `τ ∈ S` there is `σ ∈ S`
with `F_∞(x)_τ = conj (x_σ)` for all `x ∈ ℂ^S`. (A `ℂ`-algebra map `ℂ^S → ℂ` is an evaluation.) -/
lemma exists_eval (τ : R.S) : ∃ σ : R.S, ∀ x, R.F x τ = conj (x σ) := by
  classical
  -- `ψ = conj ∘ ev_τ ∘ F_∞` is a `ℂ`-linear ring map `ℂ^S → ℂ`.
  let ψ : (R.S → ℂ) →+* ℂ := (starRingEnd ℂ).comp ((Pi.evalRingHom _ τ).comp R.F)
  have hψ : ∀ x, ψ x = conj (R.F x τ) := fun _ => rfl
  have hconst : ∀ z : ℂ, ψ (fun _ => z) = z := by
    intro z; rw [hψ, R.F_const]; simp
  let e : R.S → (R.S → ℂ) := fun σ => Pi.single σ 1
  have hidem : ∀ σ, ψ (e σ) = 0 ∨ ψ (e σ) = 1 := by
    intro σ
    have h : ψ (e σ) * ψ (e σ) = ψ (e σ) := by
      rw [← map_mul]; congr 1; ext i; by_cases hi : i = σ <;> simp [e, Pi.single_apply, hi]
    rcases eq_or_ne (ψ (e σ)) 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (h.trans (mul_one _).symm))
  have hsum : ∑ σ, ψ (e σ) = 1 := by
    rw [← map_sum, show ∑ σ, e σ = 1 from Finset.univ_sum_single 1, map_one]
  obtain ⟨σ₀, -, hσ₀⟩ : ∃ σ ∈ (Finset.univ : Finset R.S), ψ (e σ) ≠ 0 := by
    by_contra h; push Not at h
    rw [Finset.sum_eq_zero h] at hsum; exact zero_ne_one hsum
  have hσ₀1 : ψ (e σ₀) = 1 := (hidem σ₀).resolve_left hσ₀
  have hother : ∀ σ, σ ≠ σ₀ → ψ (e σ) = 0 := by
    intro σ hσ
    have : ψ (e σ) * ψ (e σ₀) = 0 := by
      rw [← map_mul]
      have : e σ * e σ₀ = 0 := by
        ext i
        by_cases hi : i = σ <;> by_cases hj : i = σ₀ <;>
          simp [e, Pi.single_apply, hi, hj] <;> first | exact hσ | simp_all
      rw [this, map_zero]
    rwa [hσ₀1, mul_one] at this
  refine ⟨σ₀, fun x => ?_⟩
  have hx : ψ x = x σ₀ := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    have hterm : ∀ σ, ψ (Pi.single σ (x σ)) = x σ * ψ (e σ) := by
      intro σ
      have : Pi.single σ (x σ) = (fun _ => x σ) * e σ := by
        ext i; by_cases hi : i = σ <;> simp [e, Pi.single_apply, hi]
      rw [this, map_mul, hconst]
    simp_rw [hterm]
    rw [Finset.sum_eq_single σ₀ (fun σ _ hσ => by rw [hother σ hσ, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), hσ₀1, mul_one]
  rw [← hx, hψ, Complex.conj_conj]

/-- The conjugate `τ̄ = conj ∘ τ` of every `τ ∈ S` lies in `S` (implicit in GS 3.1.1). -/
lemma conj_mem (τ : R.S) : (starRingEnd ℂ).comp (τ : A →+* ℂ) ∈ R.S := by
  obtain ⟨σ, hσ⟩ := R.exists_eval τ
  have h : (starRingEnd ℂ).comp (τ : A →+* ℂ) = σ := by
    ext a
    have := hσ (R.delta a)
    rw [R.F_delta' a, delta_apply, delta_apply] at this
    simp [this]
  rw [h]; exact σ.2

/-- The conjugate embedding `τ̄ = conj ∘ τ`, as an element of `S`. -/
def conjS (τ : R.S) : R.S := ⟨(starRingEnd ℂ).comp (τ : A →+* ℂ), R.conj_mem τ⟩

@[simp] lemma conjS_apply (τ : R.S) (a : A) :
    ((R.conjS τ : R.S) : A →+* ℂ) a = conj ((τ : A →+* ℂ) a) := rfl

lemma conjS_conjS (τ : R.S) : R.conjS (R.conjS τ) = τ := by
  apply Subtype.ext; ext a; simp

/-- **`F_∞` is determined by `S`**: `F_∞(x)_τ = conj (x_{τ̄})`. -/
lemma F_apply (x : R.S → ℂ) (τ : R.S) : R.F x τ = conj (x (R.conjS τ)) := by
  obtain ⟨σ, hσ⟩ := R.exists_eval τ
  have h : σ = R.conjS τ := by
    apply Subtype.ext; ext a
    have := hσ (R.delta a)
    rw [R.F_delta' a, delta_apply, delta_apply] at this
    simp [this]
  rw [hσ, h]

end ArithmeticRing

namespace ArithmeticVariety

variable {A : Type} [CommRing A] [IsDomain A] [IsRegularRing A] {R : ArithmeticRing A}

/-- Complex conjugation, as an endomorphism of the ring `ℂ` in `CommRingCat`. -/
noncomputable abbrev conjC : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ :=
  CommRingCat.ofHom (starRingEnd ℂ)

lemma conjC_conjC : conjC ≫ conjC = 𝟙 _ := by
  ext z; simp

/-- **The complex points `X_∞ = X_S(ℂ)`** (Gillet–Soulé 3.2.1), as a set: pairs `(σ, x)` with
`σ ∈ S` and `x : Spec ℂ → X` over `Spec σ : Spec ℂ → Spec A` (the `ℂ`-points of `X_σ = X ⊗_σ ℂ`). -/
def complexPoints (V : ArithmeticVariety R) : Type :=
  {p : R.S × (Spec (CommRingCat.of ℂ) ⟶ V.X) //
    p.2 ≫ V.π = Spec.map (CommRingCat.ofHom (p.1 : A →+* ℂ))}

/-- **The involution `F_∞` of `X_∞`** (GS 3.2.1): `(σ, x) ↦ (σ̄, x ∘ Spec(conj))`. -/
noncomputable def Finf (V : ArithmeticVariety R) : V.complexPoints → V.complexPoints := fun p =>
  ⟨(R.conjS p.1.1, Spec.map conjC ≫ p.1.2), by
    rw [Category.assoc, p.2, ← Spec.map_comp]
    rfl⟩

@[simp] lemma Finf_fst (V : ArithmeticVariety R) (p : V.complexPoints) :
    (V.Finf p).1.1 = R.conjS p.1.1 := rfl

/-- `F_∞` is an involution of `X_∞`. -/
lemma Finf_Finf (V : ArithmeticVariety R) (p : V.complexPoints) : V.Finf (V.Finf p) = p := by
  apply Subtype.ext
  refine Prod.ext (R.conjS_conjS _) ?_
  show Spec.map conjC ≫ Spec.map conjC ≫ p.1.2 = p.1.2
  rw [← Category.assoc, ← Spec.map_comp, conjC_conjC, Spec.map_id, Category.id_comp]

/-- For `X = Spec A`, the complex points are the embeddings: `X_∞ ≃ S`. -/
noncomputable def complexPointsBaseEquiv (R : ArithmeticRing A) :
    (base R).complexPoints ≃ R.S where
  toFun p := p.1.1
  invFun σ := ⟨(σ, Spec.map (CommRingCat.ofHom (σ : A →+* ℂ))), Category.comp_id _⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    have h := p.2
    simp only [base, Category.comp_id] at h
    exact h.symm
  right_inv _ := rfl

/-- Under `X_∞ ≃ S` for `X = Spec A`, `F_∞` is `σ ↦ σ̄`. -/
lemma complexPointsBaseEquiv_Finf (R : ArithmeticRing A) (p : (base R).complexPoints) :
    complexPointsBaseEquiv R ((base R).Finf p) = R.conjS (complexPointsBaseEquiv R p) := rfl

/-- `X_∞` of `Spec A` is nonempty (`S ≠ ∅`). -/
instance (R : ArithmeticRing A) : Nonempty (base R).complexPoints := by
  obtain ⟨σ, hσ⟩ := R.S_nonempty
  exact ⟨(complexPointsBaseEquiv R).symm ⟨σ, hσ⟩⟩

section NumberField

open NumberField

variable (K : Type) [Field K] [NumberField K]

/-- `Hom(𝓞 K, ℂ) ≃ Hom(K, ℂ)` by restriction along `𝓞 K → K`. -/
noncomputable def embeddingsEquiv : ArithmeticRing.embeddings K ≃ (K →+* ℂ) where
  toFun σ := IsFractionRing.lift (A := 𝓞 K) (K := K)
    (ArithmeticRing.ringOfIntegers_hom_injective K (σ : 𝓞 K →+* ℂ))
  invFun φ := ⟨φ.comp (algebraMap (𝓞 K) K), ArithmeticRing.mem_embeddings K _⟩
  left_inv σ := by
    apply Subtype.ext
    ext a
    simp [IsFractionRing.lift_algebraMap]
  right_inv φ := by
    apply RingHom.ext
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    simp [IsFractionRing.lift_algebraMap]

/-- **`X_∞` of `Spec 𝓞 K`** (GS 3.2.1 with Example 3.1.2 (1)): the complex points are the
embeddings `K →+* ℂ`. -/
noncomputable def complexPointsSpecEquiv :
    (base (ArithmeticRing.ringOfIntegers K)).complexPoints ≃ (K →+* ℂ) :=
  (complexPointsBaseEquiv _).trans (embeddingsEquiv K)

/-- Under `X_∞ ≃ Hom(K, ℂ)`, `F_∞` is complex conjugation of embeddings,
`NumberField.ComplexEmbedding.conjugate`. -/
lemma complexPointsSpecEquiv_Finf (p : (base (ArithmeticRing.ringOfIntegers K)).complexPoints) :
    complexPointsSpecEquiv K ((base _).Finf p) =
      ComplexEmbedding.conjugate (complexPointsSpecEquiv K p) := by
  -- both sides restrict to `conj ∘ σ` on `𝓞 K`, and restriction is injective
  apply (embeddingsEquiv K).symm.injective
  apply Subtype.ext
  ext a
  show ((embeddingsEquiv K).symm ((embeddingsEquiv K)
      (complexPointsBaseEquiv _ ((base _).Finf p))) : 𝓞 K →+* ℂ) a =
    ((embeddingsEquiv K).symm (ComplexEmbedding.conjugate
      ((embeddingsEquiv K) (complexPointsBaseEquiv _ p))) : 𝓞 K →+* ℂ) a
  erw [Equiv.symm_apply_apply, complexPointsBaseEquiv_Finf]
  simp [embeddingsEquiv, ComplexEmbedding.conjugate_coe_eq, IsFractionRing.lift_algebraMap]

end NumberField

end ArithmeticVariety

end WeilRH.Arakelov
