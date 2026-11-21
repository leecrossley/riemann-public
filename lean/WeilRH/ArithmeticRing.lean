import Mathlib

/-!
# Arithmetic rings (Gillet–Soulé 1990, §3.1)

Roadmap target A1 of `lean/ROADMAP-arakelov.md`. The source is H. Gillet and C. Soulé,
*Arithmetic intersection theory*, Publ. Math. IHÉS 72 (1990), 93–174, §3.1 (pp. 124–125).

* `WeilRH.Arakelov.ArithmeticRing A` is Definition 3.1.1: a finite nonempty set `S` of
  monomorphisms `σ : A → ℂ` and a conjugate-linear involution of `ℂ`-algebras
  `F_∞ : ℂ^S → ℂ^S` fixing the image of the diagonal map `δ : A → ℂ^S`, `δ(a) = (σ a)_σ`.
* `WeilRH.Arakelov.ArithmeticRing.Hom` is 3.1.3 (homomorphisms of arithmetic rings).
* `WeilRH.Arakelov.ArithmeticRing.int` is ℤ with its unique embedding and complex conjugation
  (Example 3.1.2 (1) and (2), which agree for ℤ). `int_initial` is the remark of 3.1.3 that ℤ is
  an initial object: there is exactly one homomorphism from it to any arithmetic ring.
* `WeilRH.Arakelov.ArithmeticRing.ringOfIntegers K` is Example 3.1.2 (1) for `A = 𝓞 K`:
  `S = Hom(𝓞 K, ℂ)` (`mem_embeddings`) and `F_∞ x = (conj (x_{σ̄}))_σ`, the Frobenius on
  `ℂ^S ≅ ℂ ⊗_ℚ K` induced by complex conjugation.

## Divergence from Gillet–Soulé

GS require `A` to be an **excellent** regular Noetherian integral domain. Mathlib (pinned
v4.34.1) has `IsRegularRing` (Noetherian, regular at every prime; with an instance for Dedekind
domains) but no notion of excellent ring, so excellence is **not encoded**. Both instances here
(ℤ and `𝓞 K`) are Dedekind domains of characteristic zero, which are excellent; that fact is not
formalized. Regularity, the domain property and Noetherianity are encoded (`IsRegularRing`
extends `IsNoetherianRing`).
-/

open ComplexConjugate

namespace WeilRH.Arakelov

/-- **Arithmetic ring** (Gillet–Soulé 1990, Definition 3.1.1). A regular Noetherian integral
domain `A` together with a finite nonempty set `S` of ring monomorphisms `A → ℂ` and a
conjugate-linear involution `F` of the `ℂ`-algebra `ℂ^S` such that `F ∘ δ = δ`, where
`δ a = (σ a)_{σ ∈ S}`. Excellence of `A` is not encoded (see the module docstring). -/
structure ArithmeticRing (A : Type*) [CommRing A] [IsDomain A] [IsRegularRing A] where
  /-- The set `S` of complex embeddings. -/
  S : Finset (A →+* ℂ)
  S_nonempty : S.Nonempty
  /-- Each `σ ∈ S` is a monomorphism. -/
  injective : ∀ σ ∈ S, Function.Injective σ
  /-- The involution `F_∞` of `ℂ^S`, as a ring endomorphism. -/
  F : (S → ℂ) →+* (S → ℂ)
  /-- `F_∞` is conjugate-linear. -/
  F_smul : ∀ (z : ℂ) (x : S → ℂ), F (z • x) = conj z • F x
  /-- `F_∞` is an involution. -/
  F_F : ∀ x, F (F x) = x
  /-- `F_∞ ∘ δ = δ`. -/
  F_delta : ∀ a : A, F (fun σ : S => (σ : A →+* ℂ) a) = fun σ : S => (σ : A →+* ℂ) a

namespace ArithmeticRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsRegularRing A]

/-- The diagonal map `δ : A → ℂ^S`, `δ a = (σ a)_σ` (GS 3.1.1). -/
def delta (R : ArithmeticRing A) : A →+* (R.S → ℂ) := RingHom.pi fun σ => (σ : A →+* ℂ)

@[simp] lemma delta_apply (R : ArithmeticRing A) (a : A) (σ : R.S) :
    R.delta a σ = (σ : A →+* ℂ) a := rfl

lemma F_delta' (R : ArithmeticRing A) (a : A) : R.F (R.delta a) = R.delta a := R.F_delta a

/-- `δ` is injective (`S` is nonempty and its members are monomorphisms). -/
lemma delta_injective (R : ArithmeticRing A) : Function.Injective R.delta := by
  obtain ⟨σ, hσ⟩ := R.S_nonempty
  intro a b h
  exact R.injective σ hσ (congrFun h ⟨σ, hσ⟩)

/-- `F_∞` sends constants to their conjugates: `F (algebraMap z) = algebraMap (conj z)`. -/
lemma F_const (R : ArithmeticRing A) (z : ℂ) :
    R.F (fun _ => z) = fun _ => conj z := by
  have h : (fun _ : R.S => z) = z • (1 : R.S → ℂ) := by ext; simp
  rw [h, R.F_smul, map_one]; ext; simp

/-- **Homomorphism of arithmetic rings** (GS 3.1.3): a ring map `f : A → A'` and a
`ℂ`-algebra map `f_∞ : ℂ^S → ℂ^{S'}` with `δ' ∘ f = f_∞ ∘ δ` and `F'_∞ ∘ f_∞ = f_∞ ∘ F_∞`. -/
structure Hom {A' : Type*} [CommRing A'] [IsDomain A'] [IsRegularRing A']
    (R : ArithmeticRing A) (R' : ArithmeticRing A') where
  f : A →+* A'
  fInf : (R.S → ℂ) →ₐ[ℂ] (R'.S → ℂ)
  delta_comm : ∀ a, R'.delta (f a) = fInf (R.delta a)
  F_comm : ∀ x, R'.F (fInf x) = fInf (R.F x)

/-- The identity homomorphism. -/
def Hom.id (R : ArithmeticRing A) : Hom R R where
  f := RingHom.id A
  fInf := AlgHom.id ℂ _
  delta_comm _ := rfl
  F_comm _ := rfl

/-- GS remark after 3.1.3: since `δ'` is injective, the ring map `f` of a homomorphism is
injective whenever `δ` is (always, here). -/
lemma Hom.f_injective {A' : Type*} [CommRing A'] [IsDomain A'] [IsRegularRing A']
    {R : ArithmeticRing A} {R' : ArithmeticRing A'} (φ : Hom R R') :
    Function.Injective φ.f := by
  intro a b h
  by_contra hne
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  -- `δ (a - b)` is a unit of `ℂ^S` (each coordinate `σ (a - b)` is nonzero), so its image under
  -- the algebra map `f_∞` is a unit; but that image is `δ' (f (a - b)) = 0` in `ℂ^{S'} ≠ 0`.
  have hu : IsUnit (R.delta (a - b)) := by
    refine Pi.isUnit_iff.mpr fun τ => ?_
    simp only [delta_apply, isUnit_iff_ne_zero]
    exact fun h0 => hab (R.injective τ τ.2 (by rw [h0, map_zero]))
  have h0 : φ.fInf (R.delta (a - b)) = 0 := by
    rw [← φ.delta_comm, map_sub, h, sub_self, map_zero]
  obtain ⟨σ, hσ⟩ := R'.S_nonempty
  have : Nonempty R'.S := ⟨⟨σ, hσ⟩⟩
  exact (hu.map φ.fInf).ne_zero h0

/-! ### ℤ (GS 3.1.2 (1), (2)) -/

/-- **ℤ as an arithmetic ring** (GS Examples 3.1.2 (1) and (2), which agree for ℤ): its unique
embedding into `ℂ` and complex conjugation. -/
noncomputable def int : ArithmeticRing ℤ where
  S := {Int.castRingHom ℂ}
  S_nonempty := Finset.singleton_nonempty _
  injective σ hσ := by
    rw [Finset.mem_singleton] at hσ; subst hσ
    exact Int.cast_injective
  F := RingHom.pi fun σ => (starRingEnd ℂ).comp (Pi.evalRingHom _ σ)
  F_smul z x := by ext σ; simp [RingHom.pi_apply]
  F_F x := by ext σ; simp [RingHom.pi_apply]
  F_delta a := by ext σ; simp [RingHom.pi_apply]

/-- The unique element of `S` for ℤ. -/
lemma int_S : int.S = {Int.castRingHom ℂ} := rfl

/-- **ℤ is initial** (GS remark in 3.1.3): every arithmetic ring receives a homomorphism from ℤ. -/
noncomputable def int_hom (R : ArithmeticRing A) : Hom int R where
  f := Int.castRingHom A
  fInf := Algebra.ofId ℂ _ |>.comp
    (Pi.evalAlgHom ℂ (fun _ : int.S => ℂ) ⟨Int.castRingHom ℂ, Finset.mem_singleton_self _⟩)
  delta_comm n := by ext σ; simp
  F_comm x := by
    ext σ
    have hx := R.F_const (x ⟨Int.castRingHom ℂ, Finset.mem_singleton_self _⟩)
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply, Algebra.ofId_apply]
    have : (algebraMap ℂ (R.S → ℂ)) (x ⟨Int.castRingHom ℂ, Finset.mem_singleton_self _⟩) =
        fun _ => x ⟨Int.castRingHom ℂ, Finset.mem_singleton_self _⟩ := rfl
    rw [this, hx]
    show conj (x _) = (algebraMap ℂ (R.S → ℂ)) (int.F x _) σ
    rfl

/-- **Uniqueness**: any two homomorphisms out of ℤ agree (so ℤ is initial, GS 3.1.3). -/
lemma int_hom_unique (R : ArithmeticRing A) (φ ψ : Hom int R) :
    φ.f = ψ.f ∧ φ.fInf = ψ.fInf := by
  refine ⟨RingHom.ext_int _ _, ?_⟩
  -- `ℂ^S = ℂ` for ℤ, so a `ℂ`-algebra map out of it is determined by `ℂ`-linearity and `1 ↦ 1`.
  apply AlgHom.ext
  intro x
  have hx : x = (x ⟨Int.castRingHom ℂ, Finset.mem_singleton_self _⟩) • (1 : int.S → ℂ) := by
    ext ⟨τ, hτ⟩
    obtain rfl : τ = Int.castRingHom ℂ := Finset.mem_singleton.mp hτ
    simp
  rw [hx, map_smul, map_smul, map_one, map_one]

/-! ### Rings of integers (GS 3.1.2 (1)) -/

section NumberField

open NumberField

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/-- Every ring map `𝓞 K → ℂ` is injective: its kernel lies over `0` in ℤ (characteristic
zero), and `𝓞 K` is integral over ℤ. -/
lemma ringOfIntegers_hom_injective (τ : 𝓞 K →+* ℂ) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_under_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    simpa using (Int.cast_eq_zero (α := ℂ)).mp hn
  have : x ∈ RingHom.ker τ := hx
  rw [hker] at this
  exact this

/-- Every ring map `𝓞 K → ℂ` is the restriction of a unique embedding `K → ℂ`. -/
lemma exists_extend (τ : 𝓞 K →+* ℂ) :
    ∃ φ : K →+* ℂ, φ.comp (algebraMap (𝓞 K) K) = τ := by
  refine ⟨(IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ)
    (ringOfIntegers_hom_injective K τ) : K →+* ℂ), RingHom.ext fun x => ?_⟩
  exact IsFractionRing.lift_algebraMap (A := 𝓞 K) (K := K) (L := ℂ) (g := τ)
    (ringOfIntegers_hom_injective K τ) x

open Classical in
/-- The set `Hom(𝓞 K, ℂ)`, as the image of the (finitely many) embeddings of `K`. -/
noncomputable def embeddings : Finset (𝓞 K →+* ℂ) :=
  (Finset.univ : Finset (K →+* ℂ)).image fun φ => φ.comp (algebraMap (𝓞 K) K)

/-- `embeddings K` is all of `Hom(𝓞 K, ℂ)` (GS 3.1.2 (1): `S = Hom(A, ℂ)`). -/
lemma mem_embeddings (τ : 𝓞 K →+* ℂ) : τ ∈ embeddings K := by
  classical
  obtain ⟨φ, hφ⟩ := exists_extend K τ
  exact Finset.mem_image.mpr ⟨φ, Finset.mem_univ _, hφ⟩

/-- The conjugate embedding `σ̄ = conj ∘ σ`, as a member of `embeddings K`. -/
noncomputable def conjEmb (σ : embeddings K) : embeddings K :=
  ⟨(starRingEnd ℂ).comp (σ : 𝓞 K →+* ℂ), mem_embeddings K _⟩

@[simp] lemma conjEmb_apply (σ : embeddings K) (a : 𝓞 K) :
    ((conjEmb K σ : embeddings K) : 𝓞 K →+* ℂ) a = conj ((σ : 𝓞 K →+* ℂ) a) := rfl

lemma conjEmb_conjEmb (σ : embeddings K) : conjEmb K (conjEmb K σ) = σ := by
  apply Subtype.ext
  ext a
  simp

/-- **The ring of integers as an arithmetic ring** (GS Example 3.1.2 (1)):
`S = Hom(𝓞 K, ℂ)`, and `F_∞ x = (conj (x_{σ̄}))_σ`, the Frobenius on `ℂ^S ≅ ℂ ⊗_ℚ K` induced
by complex conjugation. -/
noncomputable def ringOfIntegers : ArithmeticRing (𝓞 K) where
  S := embeddings K
  S_nonempty := ⟨_, mem_embeddings K (Classical.arbitrary (K →+* ℂ) |>.comp (algebraMap _ K))⟩
  injective σ _ := ringOfIntegers_hom_injective K σ
  F := RingHom.pi fun σ => (starRingEnd ℂ).comp (Pi.evalRingHom _ (conjEmb K σ))
  F_smul z x := by ext σ; simp [RingHom.pi_apply]
  F_F x := by ext σ; simp [RingHom.pi_apply, conjEmb_conjEmb]
  F_delta a := by ext σ; simp [RingHom.pi_apply]

@[simp] lemma ringOfIntegers_F_apply (x : embeddings K → ℂ) (σ : embeddings K) :
    (ringOfIntegers K).F x σ = conj (x (conjEmb K σ)) := rfl

/-- `#S = [K : ℚ]` for `𝓞 K`. -/
lemma card_ringOfIntegers_S : (ringOfIntegers K).S.card = Module.finrank ℚ K := by
  classical
  show (embeddings K).card = _
  rw [embeddings, Finset.card_image_of_injective _ ?_, Finset.card_univ,
    NumberField.Embeddings.card]
  intro φ ψ h
  apply RingHom.ext
  intro x
  -- an embedding of `K` is determined by its values on `𝓞 K`, since `K = Frac(𝓞 K)`
  have hφ : φ = IsFractionRing.lift (ringOfIntegers_hom_injective K (φ.comp (algebraMap _ K))) :=
    RingHom.ext fun y => by
      obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
      simp [IsFractionRing.lift_algebraMap]
  have hψ : ψ = IsFractionRing.lift (ringOfIntegers_hom_injective K (ψ.comp (algebraMap _ K))) :=
    RingHom.ext fun y => by
      obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
      simp [IsFractionRing.lift_algebraMap]
  rw [hφ, hψ]
  simp only [h]

end NumberField

end ArithmeticRing

end WeilRH.Arakelov
