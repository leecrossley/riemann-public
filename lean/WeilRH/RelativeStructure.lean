import WeilRH.Deninger

/-!
# Relative structure (`prop:relative-structure`)

`latex/notes.tex`, `def:deninger-structure` (b) and `prop:relative-structure`. A morphism of
Deninger structures is a graded unital algebra homomorphism commuting with the generators; unlike
`DeningerStructure.Hom`, which lives inside one `Den_d(U)`, the proposed `Den^natural` repair allows
morphisms between arbitrary dimension and unit components. `prop:relative-structure` uses a morphism
`H(X̄_K) → H(X̄)` between structures of dimensions `1` and `dim X̄`.
`DeningerStructure.Morphism` is the cross-component notion.

Given such a morphism `φ : A → V`, the action `a • v := φ(a) ∪ v` makes `V` a graded
`A`-algebra on which `Θ` is a derivation (`prop:relative-structure`):

* `act_one`, `act_act`: unital and associative action;
* `act_mem`: `A^i • V^k ⊆ V^{i+k}`;
* `act_mul_left`, `act_mul_right`: compatibility with the cup product of `V`
  (the second with the Koszul sign);
* `Θ_act`: `Θ_V (a • v) = (Θ_A a) • v + a • (Θ_V v)`.

The notes deduce the statement from functoriality of a Deninger cohomology theory; here the
morphism is a hypothesis, so the result is the algebraic content of the proposition.
-/

namespace WeilRH

universe u v

namespace DeningerStructure

variable {U U' : Type v} [CommRing U] [Algebra ℂ U]
  [CommRing U'] [Algebra ℂ U'] {ΘU : Module.End ℂ U} {ΘU' : Module.End ℂ U'}
  {A : Type u} [AddCommGroup A] [Module ℂ A] {e : ℕ}
  {V : Type u} [AddCommGroup V] [Module ℂ V] {d : ℕ}

/-- **`Den^natural` repair of `def:deninger-structure` (b).** A morphism between Deninger
structures of possibly different dimensions and units: a graded unital algebra homomorphism
commuting with the generators. Traces need not be preserved. -/
structure Morphism (DA : DeningerStructure A e U ΘU)
    (DV : DeningerStructure V d U' ΘU') where
  /-- The linear map. -/
  toLin : A →ₗ[ℂ] V
  map_G : ∀ {j : ℕ} {x : A}, x ∈ DA.G j → toLin x ∈ DV.G j
  map_mul : ∀ x y, toLin (DA.mul x y) = DV.mul (toLin x) (toLin y)
  map_one : toLin DA.one = DV.one
  map_Θ : ∀ x, toLin (DA.Θ x) = DV.Θ (toLin x)

/-- A morphism inside `Den_d(U)` is a morphism. -/
def Hom.toMorphism {DA : DeningerStructure A d U ΘU} {DV : DeningerStructure V d U ΘU}
    (f : DA.Hom DV) : DA.Morphism DV :=
  ⟨f.toLin, f.map_G, f.map_mul, f.map_one, f.map_Θ⟩

/-- The identity morphism (nonvacuity of `Morphism`). -/
def Morphism.id (DV : DeningerStructure V d U ΘU) : DV.Morphism DV :=
  (Hom.id DV).toMorphism

namespace Morphism

variable {DA : DeningerStructure A e U ΘU} {DV : DeningerStructure V d U' ΘU'}

@[ext]
theorem ext {φ ψ : DA.Morphism DV} (h : φ.toLin = ψ.toLin) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- Composition of cross-component morphisms. -/
def comp {W : Type u} [AddCommGroup W] [Module ℂ W] {f : ℕ}
    {U'' : Type v} [CommRing U''] [Algebra ℂ U''] {ΘU'' : Module.End ℂ U''}
    {DW : DeningerStructure W f U'' ΘU''}
    (ψ : DV.Morphism DW) (φ : DA.Morphism DV) : DA.Morphism DW where
  toLin := ψ.toLin ∘ₗ φ.toLin
  map_G hx := ψ.map_G (φ.map_G hx)
  map_mul x y := by simp [φ.map_mul, ψ.map_mul]
  map_one := by simp [φ.map_one, ψ.map_one]
  map_Θ x := by simp [φ.map_Θ, ψ.map_Θ]

variable (φ : DA.Morphism DV)

@[simp]
theorem comp_id : comp (Morphism.id DV) φ = φ := by
  apply ext
  rfl

@[simp]
theorem id_comp : comp φ (Morphism.id DA) = φ := by
  apply ext
  rfl

theorem comp_assoc {W X : Type u} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] {f g : ℕ}
    {U'' U''' : Type v} [CommRing U''] [Algebra ℂ U'']
    [CommRing U'''] [Algebra ℂ U''']
    {ΘU'' : Module.End ℂ U''} {ΘU''' : Module.End ℂ U'''}
    {DW : DeningerStructure W f U'' ΘU''}
    {DX : DeningerStructure X g U''' ΘU'''}
    (ψ : DV.Morphism DW) (χ : DW.Morphism DX) :
    comp χ (comp ψ φ) = comp (comp χ ψ) φ := by
  apply ext
  rfl

/-- A morphism into dimension `d` kills source degrees above `2d`. -/
theorem map_eq_zero_of_gt {j : ℕ} {x : A} (hx : x ∈ DA.G j) (hj : 2 * d < j) :
    φ.toLin x = 0 := by
  have hm := φ.map_G hx
  simpa [DV.vanish j hj] using hm

/-- The action `a • v = φ(a) ∪ v` of `A` on `V` (`prop:relative-structure`). -/
def act (a : A) (v : V) : V := DV.mul (φ.toLin a) v

theorem act_one (v : V) : φ.act DA.one v = v := by
  simp [act, φ.map_one, DV.one_mul]

theorem act_act (a b : A) (v : V) : φ.act (DA.mul a b) v = φ.act a (φ.act b v) := by
  simp [act, φ.map_mul, DV.mul_assoc]

theorem act_mem {i k : ℕ} {a : A} {v : V} (ha : a ∈ DA.G i) (hv : v ∈ DV.G k) :
    φ.act a v ∈ DV.G (i + k) :=
  DV.mul_mem (φ.map_G ha) hv

theorem act_add_left (a b : A) (v : V) : φ.act (a + b) v = φ.act a v + φ.act b v := by
  simp [act]

theorem act_add_right (a : A) (v w : V) : φ.act a (v + w) = φ.act a v + φ.act a w := by
  simp [act]

/-- `V` is an `A`-algebra: `a • (v ∪ w) = (a • v) ∪ w`. -/
theorem act_mul_left (a : A) (v w : V) : φ.act a (DV.mul v w) = DV.mul (φ.act a v) w := by
  simp [act, DV.mul_assoc]

/-- Graded centrality: `a • (v ∪ w) = (-1)^{ik} v ∪ (a • w)` for `a ∈ A^i`, `v ∈ V^k`. -/
theorem act_mul_right {i k : ℕ} {a : A} {v : V} (ha : a ∈ DA.G i) (hv : v ∈ DV.G k) (w : V) :
    φ.act a (DV.mul v w) = ((-1 : ℂ) ^ (i * k)) • DV.mul v (φ.act a w) := by
  have hc := DV.mul_comm_graded (φ.map_G ha) hv
  -- `mul v (φ a) = (-1)^{ik} • mul (φ a) v`, hence `mul (φ a) v = (-1)^{ik} • mul v (φ a)`.
  have hsq : ((-1 : ℂ) ^ (i * k)) * ((-1 : ℂ) ^ (i * k)) = 1 := by
    rw [← mul_pow]; simp
  have hc' : DV.mul (φ.toLin a) v = ((-1 : ℂ) ^ (i * k)) • DV.mul v (φ.toLin a) := by
    rw [hc, smul_smul, hsq, one_smul]
  simp only [act]
  rw [← DV.mul_assoc, hc', map_smul, LinearMap.smul_apply, DV.mul_assoc]

/-- **`prop:relative-structure`.** `Θ` is a derivation for the action:
`Θ_V (a • v) = (Θ_A a) • v + a • (Θ_V v)`. -/
theorem Θ_act (a : A) (v : V) : DV.Θ (φ.act a v) = φ.act (DA.Θ a) v + φ.act a (DV.Θ v) := by
  simp [act, DV.Θ_mul, φ.map_Θ]

end Morphism

end DeningerStructure

end WeilRH
