import WeilRH.Spectral
import WeilRH.Suspension
import WeilRH.KunOrbits
import WeilRH.WeightedAlgebra

/-!
# The units `𝟙`, `𝟙_q` and their twists (`def:unit`, `prop:unit`)

`latex/notes.tex`, `def:unit`:

* (a) the *arithmetic unit* is the spectral core `𝟙 = (ℂ, 0)` with its multiplication;
* (b) the *`q`-periodic unit* is `𝟙_q = ⨁_{n ∈ ℤ} ℂ vⁿ` with `Θ vⁿ = (2πin/log q) vⁿ` and
  `vⁿ vᵐ = v^{n+m}`;
* (c) for a spectral core `(U, Θ_U)` and `k ∈ ℤ`, `U(-k)` is `U` with generator `Θ_U + k`.

Main results:

* `Unit.arith`, `Unit.twist`: (a) and (c). `Unit.arith_mul` is the derivation law for `Θ = 0`.
* `Unit.tensorSum_arith`, `Unit.tensorSum_twist`: `𝟙` is a unit for the tensor of spectral cores,
  `V ⊗ 𝟙 ≅ V` and `V ⊗ 𝟙(-k) ≅ V(-k)` by `TensorProduct.rid`, intertwining the generators.
* `Unit.spectralCore_tensor_arith_iff`: `V ⊗ 𝟙` is a spectral core iff `V` is.
* `Unit.spectralCore_arith`, `Unit.spec_arith`, `Unit.mult_arith`: `𝟙` is a spectral core with
  spectrum `{0}`, simple.
* `Unit.Periodic`, `Unit.periodicTheta`: (b), modelled on the Laurent polynomials
  `AddMonoidAlgebra ℂ ℤ`, so `vⁿ vᵐ = v^{n+m}` is the algebra product;
  `Unit.periodicTheta_mul` is the derivation law.
* `Unit.spectralCore_periodic`, `Unit.mem_spec_periodic`, `Unit.mult_periodic`: `𝟙_q` is a
  spectral core with spectrum `(2πi/log q)ℤ`, every eigenvalue simple (`prop:unit`, spectrum
  clause).
* `Unit.not_equiv_arith`: no linear isomorphism intertwines `𝟙_q` with `𝟙` (`prop:unit`, last
  clause).
-/

namespace WeilRH.Unit

open WeilRH.Spectral WeilRH.Suspension WeilRH.KunFq WeilRH.KunOrbits
open scoped TensorProduct DirectSum

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ### The arithmetic unit and twists -/

/-- `def:unit` (a): the generator of the arithmetic unit `𝟙 = (ℂ, 0)`. -/
def arith : Module.End ℂ ℂ := 0

/-- `def:unit` (c) / `def:flow`: the Tate twist `U(-k)`, i.e. `U` with generator `Θ_U + k`. -/
def twist (Θ : Module.End ℂ V) (k : ℤ) : Module.End ℂ V := Θ + (k : ℂ) • 1

/-- The generator of `𝟙` is a derivation of the multiplication of `ℂ` (`def:unit` (a)). -/
theorem arith_mul (a b : ℂ) : arith (a * b) = arith a * b + a * arith b := by
  simp [arith]

/-- **`𝟙` is a tensor unit.** `TensorProduct.rid : V ⊗ ℂ ≃ V` intertwines the generator
`Θ ⊗ 1 + 1 ⊗ 0` of `V ⊗ 𝟙` with `Θ`. -/
theorem tensorSum_arith (Θ : Module.End ℂ V) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (tensorSum Θ arith x) = Θ (TensorProduct.rid ℂ V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v c => simp [tensorSum, arith]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Twisting commutes with the tensor unit.** `V ⊗ 𝟙(-k) ≅ V(-k)` by `TensorProduct.rid`. -/
theorem tensorSum_twist (Θ : Module.End ℂ V) (k : ℤ) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (tensorSum Θ (twist arith k) x) =
      twist Θ k (TensorProduct.rid ℂ V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v c =>
    simp [tensorSum, twist, arith, smul_smul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `V ⊗ 𝟙` is a spectral core iff `V` is. -/
theorem spectralCore_tensor_arith_iff (Θ : Module.End ℂ V) :
    SpectralCore (tensorSum Θ arith) ↔ SpectralCore Θ := by
  constructor
  · intro h
    exact h.of_equiv (TensorProduct.rid ℂ V) (fun x => (tensorSum_arith Θ x).symm)
  · intro h
    refine h.of_equiv (TensorProduct.rid ℂ V).symm (fun y => ?_)
    apply (TensorProduct.rid ℂ V).injective
    rw [tensorSum_arith]; simp

/-- `𝟙` is a spectral core (`def:unit` (a)). -/
theorem spectralCore_arith : SpectralCore arith :=
  spectralCore_of_finiteDimensional arith

/-- The spectrum of `𝟙` is `{0}`. -/
theorem spec_arith : spec arith = {0} := by
  ext ρ
  simp only [spec, Set.mem_ofPred_eq, Set.mem_singleton_iff, arith]
  constructor
  · intro h
    by_contra hρ
    apply h
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
    have : ((0 : Module.End ℂ ℂ) - ρ • 1) ^ k = ((-ρ) ^ k) • (1 : Module.End ℂ ℂ) := by
      rw [zero_sub, ← neg_smul, smul_pow, one_pow]
    rw [this] at hk
    simp only [LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero] at hk
    rcases hk with h0 | h0
    · exact absurd (pow_eq_zero_iff'.1 h0).1 (neg_ne_zero.2 hρ)
    · simp [h0]
  · rintro rfl
    rw [Submodule.ne_bot_iff]
    exact ⟨1, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp⟩, one_ne_zero⟩

/-- The eigenvalue `0` of `𝟙` is simple. -/
theorem mult_arith : mult arith 0 = 1 := by
  have : arith.maxGenEigenspace 0 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [arith]⟩
  rw [mult, this, finrank_top, Module.finrank_self]

/-! ### The `q`-periodic unit -/

/-- `def:unit` (b): the underlying space of `𝟙_q`, the Laurent polynomials `⨁_{n∈ℤ} ℂ vⁿ`, with
`vⁿ = single n 1` and the algebra product `vⁿ vᵐ = v^{n+m}`. -/
abbrev Periodic : Type := AddMonoidAlgebra ℂ ℤ

/-- The diagonal model `⨁_{n∈ℤ} ℂ` of `𝟙_q`, with `Θ = ⨁ (2πin/log q)`. -/
noncomputable def periodicDiag (q : ℝ) : Module.End ℂ (⨁ _ : ℤ, ℂ) :=
  diag fun n : ℤ => shift q n • (1 : Module.End ℂ ℂ)

/-- The coordinate isomorphism `𝟙_q ≃ ⨁_{n∈ℤ} ℂ`, `vⁿ ↦ eₙ`. -/
noncomputable def periodicEquiv : Periodic ≃ₗ[ℂ] (⨁ _ : ℤ, ℂ) :=
  (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans (finsuppLequivDFinsupp ℂ)

lemma periodicEquiv_single (n : ℤ) (c : ℂ) :
    periodicEquiv (AddMonoidAlgebra.single n c) = DirectSum.of (fun _ : ℤ => ℂ) n c := by
  change Finsupp.toDFinsupp (Finsupp.single n c) = _
  rw [Finsupp.toDFinsupp_single]; rfl

/-- `def:unit` (b): the generator `Θ vⁿ = (2πin/log q) vⁿ` of `𝟙_q`, defined on coordinates. -/
noncomputable def periodicTheta (q : ℝ) : Module.End ℂ Periodic :=
  periodicEquiv.symm.toLinearMap ∘ₗ periodicDiag q ∘ₗ periodicEquiv.toLinearMap

lemma periodicEquiv_intertwines (q : ℝ) (x : Periodic) :
    periodicDiag q (periodicEquiv x) = periodicEquiv (periodicTheta q x) := by
  simp [periodicTheta]

lemma periodicDiag_of (q : ℝ) (n : ℤ) (c : ℂ) :
    periodicDiag q (DirectSum.of (fun _ : ℤ => ℂ) n c) =
      DirectSum.of (fun _ : ℤ => ℂ) n (shift q n * c) := by
  ext i
  rw [periodicDiag, diag_apply]
  by_cases h : i = n
  · subst h; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ h, DirectSum.of_eq_of_ne _ _ _ h]
    simp

@[simp] lemma periodicTheta_single (q : ℝ) (n : ℤ) (c : ℂ) :
    periodicTheta q (AddMonoidAlgebra.single n c) =
      AddMonoidAlgebra.single n (shift q n * c) := by
  apply periodicEquiv.injective
  rw [← periodicEquiv_intertwines, periodicEquiv_single, periodicEquiv_single, periodicDiag_of]

/-- `vⁿ vᵐ = v^{n+m}` (`def:unit` (b)). -/
lemma single_mul_single (n m : ℤ) :
    (AddMonoidAlgebra.single n (1 : ℂ) : Periodic) * AddMonoidAlgebra.single m 1 =
      AddMonoidAlgebra.single (n + m) 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one]

lemma shift_add' (q : ℝ) (a b : ℤ) : shift q (a + b) = shift q a + shift q b := by
  simp only [shift]; push_cast; ring

/-- The generator of `𝟙_q` is a derivation of its multiplication. -/
theorem periodicTheta_mul (q : ℝ) (f g : Periodic) :
    periodicTheta q (f * g) = periodicTheta q f * g + f * periodicTheta q g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; abel
  | single n a =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; abel
    | single m b =>
      simp only [AddMonoidAlgebra.single_mul_single, periodicTheta_single, shift_add',
        ← AddMonoidAlgebra.single_add]
      congr 1; ring

lemma range_shift_subset (q : ℝ) (hq : 1 < q) :
    Set.range (shift q) ⊆ {ρ : ℂ | (1 : Module.End ℂ ℂ).HasEigenvalue (qpow q ρ)} := by
  rintro _ ⟨k, rfl⟩
  have hk : qpow q (shift q k) = 1 := (qpow_eq_one_iff hq _).2 ⟨k, rfl⟩
  rw [Set.mem_ofPred_eq, hk]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (by simp), one_ne_zero⟩

lemma nilpotent_block (q : ℝ) (n : ℤ) :
    IsNilpotent ((shift q n • (1 : Module.End ℂ ℂ)) - shift q n • 1) :=
  ⟨1, by simp⟩

/-- **`𝟙_q` is a spectral core** (`def:unit` (b)). -/
theorem spectralCore_periodic {q : ℝ} (hq : 1 < q) : SpectralCore (periodicTheta q) := by
  have hdiag : SpectralCore (periodicDiag q) :=
    spectralCore_diag (fun n => shift q n) (fun n => shift q n • 1) (shift_injective hq)
      (nilpotent_block q)
      (fun z hz => noAccPt_idx (F := (1 : Module.End ℂ ℂ)) hq z
        (hz.mono (Filter.principal_mono.2 (range_shift_subset q hq))))
  refine hdiag.of_equiv periodicEquiv.symm (fun y => ?_)
  apply periodicEquiv.injective
  rw [← periodicEquiv_intertwines]; simp

/-- **Spectrum of `𝟙_q`** (`prop:unit`): `spec 𝟙_q = (2πi/log q)ℤ`. -/
theorem mem_spec_periodic {q : ℝ} (hq : 1 < q) (ρ : ℂ) :
    ρ ∈ spec (periodicTheta q) ↔ ∃ k : ℤ, ρ = shift q k := by
  have hs : spec (periodicTheta q) = spec (periodicDiag q) := by
    ext σ
    simp only [spec, Set.mem_ofPred_eq, ne_eq,
      ← map_maxGenEigenspace_of_equiv periodicEquiv (periodicEquiv_intertwines q)]
    rw [Submodule.map_eq_bot_iff (e := periodicEquiv)]
  rw [hs]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    apply h
    rw [eq_bot_iff]
    intro x hx
    rw [periodicDiag, mem_maxGenEigenspace_diag (fun n => shift q n) _ (shift_injective hq)
      (nilpotent_block q)] at hx
    rw [Submodule.mem_bot]
    ext i
    exact hx i (hne i).symm
  · rintro ⟨k, rfl⟩
    simp only [spec, Set.mem_ofPred_eq]
    rw [Submodule.ne_bot_iff]
    refine ⟨DirectSum.of (fun _ : ℤ => ℂ) k 1, ?_, ?_⟩
    · rw [periodicDiag, mem_maxGenEigenspace_diag (fun n => shift q n) _ (shift_injective hq)
        (nilpotent_block q)]
      intro i hi
      rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hi (by rw [h]))]
    · intro h
      have := congrArg (fun x : ⨁ _ : ℤ, ℂ => x k) h
      simp at this

/-- **Every eigenvalue of `𝟙_q` is simple** (`prop:unit`). -/
theorem mult_periodic {q : ℝ} (hq : 1 < q) (k : ℤ) : mult (periodicTheta q) (shift q k) = 1 := by
  have h1 : mult (periodicTheta q) (shift q k) = mult (periodicDiag q) (shift q k) := by
    rw [mult, mult, ← map_maxGenEigenspace_of_equiv periodicEquiv (periodicEquiv_intertwines q)]
    exact (periodicEquiv.submoduleMap ((periodicTheta q).maxGenEigenspace (shift q k))).finrank_eq
  rw [h1, periodicDiag]
  simpa using mult_diag (fun n => shift q n) (fun n => shift q n • (1 : Module.End ℂ ℂ))
    (shift_injective hq) (nilpotent_block q) k

/-- **`𝟙_q` is not isomorphic to `𝟙`** (`prop:unit`, last clause): no linear isomorphism
intertwines the two generators, since `2πi/log q ∈ spec 𝟙_q` while `spec 𝟙 = {0}`. -/
theorem not_equiv_arith {q : ℝ} (hq : 1 < q) :
    ¬ ∃ e : Periodic ≃ₗ[ℂ] ℂ, ∀ x, arith (e x) = e (periodicTheta q x) := by
  rintro ⟨e, he⟩
  have hmem : shift q 1 ∈ spec (periodicTheta q) := (mem_spec_periodic hq _).2 ⟨1, rfl⟩
  have hs : shift q 1 ∈ spec arith := by
    simp only [spec, Set.mem_ofPred_eq, ne_eq] at hmem ⊢
    rw [← map_maxGenEigenspace_of_equiv e he, Submodule.map_eq_bot_iff (e := e)]
    exact hmem
  rw [spec_arith, Set.mem_singleton_iff] at hs
  exact (shift_injective hq).ne (by norm_num : (1 : ℤ) ≠ 0) (by rw [hs]; simp [shift])

/-- Nonvacuity: `𝟙_q` is nonzero (`v⁰ ≠ 0`). -/
theorem periodic_nontrivial : (AddMonoidAlgebra.single 0 (1 : ℂ) : Periodic) ≠ 0 := by
  simp

end WeilRH.Unit
