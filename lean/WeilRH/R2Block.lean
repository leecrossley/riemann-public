/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.HermAlgebra
import WeilRH.Negative

/-!
# `prop:R2` and `prop:R3` for the quaternionic block of `def:R2-block`

Source: `latex/notes.tex`, `def:R2-block`, `prop:R2` (claim R2), `def:twist-cone` and `prop:R3`
(claim R3). The matrices `Θ, Ω, S` and the forms `B(v, w) = vᵀΩw`, `h₁(v, w) = vᵀ(ΩS)w̄` are those
of `WeilRH.R2` (`Negative.lean`), in the basis `e₁, e₂, f₁, f₂` = `Fin 4`.

* `prop:R2` (i): `R2.gradedBlock a T` is the quaternionic block `ℂ·1 ⊕ ℂ⁴ ⊕ ℂη` as a
  `HermAlgebraDatum _ 1 0` (AW1 derivation rule, AW3 trace of weight one, the star laws of AW4 in
  degrees `0, 1, 2`, Hermitian nondegenerate `h_j`); its degree-one data are `Θ`, `B`, `J v = S v̄`
  (`ContentAssembly.R2_Θ`, `R2_Ω`, `R2_S`); `J² = -1` (`R2.quaternionic`); `h₀`, `h₂` are positive
  definite (`R2.gradedBlock_h_zero`, `gradedBlock_h_two`).
* `prop:R2` (ii): `H = ΩS = [[0, R], [-R, 0]]`, `h₁` Hermitian, nondegenerate, of signature
  `(2, 2)` (`R2.signature`: a real invertible `P` with `Pᵀ H P = diag(2, 2, -2, -2)`), and
  `h₁(e₁ + f₂, e₁ + f₂) = -2`.
* `prop:R2` (iii): every eigenvalue of `Θ` has real part `1/2 + a` or `1/2 - a`
  (`R2.re_of_eigen`), hence none lies on `Re s = 1/2` when `a ≠ 0`.
* `prop:R3` (i): for `T ≠ 0` and `n ∈ ℤ`, `Θ - n` is invertible, so the twist cone
  `C_n = [V --(Θ - n)--> V]` has zero cohomology (`R2.cone_acyclic`).
* `prop:R3` (ii): `p(s) = det(s - Θ) = ((w - a)² + T²)((w + a)² + T²)`, `p(1 - s) = p(s)`,
  `p(s) > 0` for real `s` (`T ≠ 0`), and `p` is the evaluation of a polynomial of degree four
  (`R2.pPoly`).

`prop:R3` (iii) (zeta-regularized determinants of a sum) is not formalized: it needs
`def:regdet` (open obligation 1).
-/

open Matrix Complex Polynomial
open scoped ComplexConjugate

namespace WeilRH.R2

variable (a T : ℝ)

/-! ### `prop:R2` (i): the graded quaternionic block -/

/-- **The quaternionic block of `def:R2-block`** as a graded Weil datum of type `(1, 0)`: the
`prop:content` (iii) assembly with a single quartet `λ = 1/2 + a + iT` and no line or real-pair
units. -/
noncomputable def gradedBlock :
    HermAlgebraDatum (PairingModel.Tot (ContentAssembly.X Empty Empty Unit)) 1 0 :=
  ContentAssembly.gradedDatum (fun e : Empty => e.elim) (fun e => e.elim) (fun e : Empty => e.elim)
    (fun _ : Unit => lam a T)

/-- `h₀(c, c') = c c̄'`: `h₀` is positive definite. -/
theorem gradedBlock_h_zero (c c' : ℂ) :
    (gradedBlock a T).h 0 (c, 0, 0) (c', 0, 0) = c * conj c' := by
  simp [HermAlgebraDatum.h, gradedBlock, ContentAssembly.gradedDatum,
    PairingModel.gradedDatum, PairingModel.st, PairingModel.st0, PairingModel.trT,
    PairingModel.mul]

/-- `h₂(cη, c'η) = c c̄'`: `h₂` is positive definite. -/
theorem gradedBlock_h_two (c c' : ℂ) :
    (gradedBlock a T).h 2 (0, 0, c) (0, 0, c') = c * conj c' := by
  simp [HermAlgebraDatum.h, gradedBlock, ContentAssembly.gradedDatum,
    PairingModel.gradedDatum, PairingModel.st, PairingModel.st2, PairingModel.trT,
    PairingModel.mul]

/-- `h₀` and `h₂` are positive definite. -/
theorem gradedBlock_h_pos {c : ℂ} (hc : c ≠ 0) :
    0 < ((gradedBlock a T).h 0 (c, 0, 0) (c, 0, 0)).re ∧
      0 < ((gradedBlock a T).h 2 (0, 0, c) (0, 0, c)).re := by
  rw [gradedBlock_h_zero, gradedBlock_h_two, Complex.mul_conj]
  exact ⟨by exact_mod_cast Complex.normSq_pos.2 hc, by exact_mod_cast Complex.normSq_pos.2 hc⟩

/-- **`prop:R2` (i).** The quaternionic block is a graded Weil datum of type `(1, 0)` whose
degree-one data are the matrices of `def:R2-block`, with `J² = -1` and `h₀`, `h₂` positive
definite. -/
theorem axioms :
    Nonempty (HermAlgebraDatum (PairingModel.Tot (ContentAssembly.X Empty Empty Unit)) 1 0) ∧
    Θ a T = Matrix.diagonal (ContentAssembly.qlam (lam a T)) ∧
    (∀ i j, Ω i j = if j = ContentAssembly.qswp i then ContentAssembly.qsgn i else 0) ∧
    (∀ i j, S i j = if j = ContentAssembly.qtau i then ContentAssembly.qt i else 0) ∧
    S * S.map conj = -1 ∧
    ∀ c : ℂ, c ≠ 0 → 0 < ((gradedBlock a T).h 0 (c, 0, 0) (c, 0, 0)).re ∧
      0 < ((gradedBlock a T).h 2 (0, 0, c) (0, 0, c)).re :=
  ⟨⟨gradedBlock a T⟩, ContentAssembly.R2_Θ a T, ContentAssembly.R2_Ω, ContentAssembly.R2_S,
    quaternionic, fun _ hc => gradedBlock_h_pos a T hc⟩


/-! ### `prop:R2` (i), stated about `gradedBlock` itself (round 71)

The independent review of rounds 65–69 found that `axioms` above asserts only
`Nonempty (HermAlgebraDatum …)` and matrix identities: its type never says that the degree-one data
of `gradedBlock a T` are the matrices of `def:R2-block`. The theorems below say exactly that, in the
basis `eb 0, eb 1, eb 2, eb 3` = `e₁, e₂, f₁, f₂` of `V¹`. -/

/-- The basis vector `e₁, e₂, f₁, f₂` (= `Fin 4`) of `V¹` in the quaternionic block. -/
noncomputable def eb (i : Fin 4) : PairingModel.Tot (ContentAssembly.X Empty Empty Unit) :=
  (0, DirectSum.lof ℂ _ (fun _ => ℂ) (Sum.inr (Sum.inr ((), i))) 1, 0)

lemma eb_coord (i : Fin 4) (k : ContentAssembly.X Empty Empty Unit) :
    (eb i).2.1 k = if k = Sum.inr (Sum.inr ((), i)) then 1 else 0 := by
  rw [eb, PairingModel.lof_eval]
  split_ifs with h1 h2 h2 <;> first | rfl | (exact absurd h1.symm h2) | exact absurd h2.symm h1

/-- Each `eb i` lies in `V¹`. -/
theorem eb_mem (i : Fin 4) : eb i ∈ (gradedBlock a T).G 1 := by
  simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum, PairingModel.mem_G1, eb]

/-- The `eb i` span `V¹`: every `x ∈ V¹` is `Σ_i x_i eb i`. -/
theorem eq_sum_eb {x : PairingModel.Tot (ContentAssembly.X Empty Empty Unit)}
    (hx : x ∈ (gradedBlock a T).G 1) :
    x = ∑ i, x.2.1 (Sum.inr (Sum.inr ((), i))) • eb i := by
  have hx' : x.1 = 0 ∧ x.2.2 = 0 := by
    simpa [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum,
      PairingModel.mem_G1] using hx
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [hx'.1, eb, Prod.fst_sum]
  · ext k
    rcases k with ⟨e, _⟩ | ⟨e, _⟩ | ⟨⟨⟩, k⟩
    · exact e.elim
    · exact e.elim
    · simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_mk]
      fin_cases k <;> simp [Fin.sum_univ_four, eb, PairingModel.lof_eval, DirectSum.smul_apply]
  · simp [hx'.2, eb, Prod.snd_sum]

/-- The generator of `gradedBlock a T` acts on `V¹` by the matrix `Θ` of `def:R2-block`. -/
theorem theta_eb (i : Fin 4) : (gradedBlock a T).Θ (eb i) = ∑ j, Θ a T j i • eb j := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum, eb,
      PairingModel.thetaL, PairingModel.thetaTot, Prod.fst_sum]
  · ext k
    rcases k with ⟨e, _⟩ | ⟨e, _⟩ | ⟨⟨⟩, k⟩
    · exact e.elim
    · exact e.elim
    · simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum,
        PairingModel.thetaL, PairingModel.thetaTot, PairingModel.theta_apply]
      simp only [Prod.snd_sum, Prod.fst_sum, Prod.smul_mk, DFinsupp.finsetSum_apply]
      rw [Θ_eq_diagonal]
      fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_four, eb, PairingModel.lof_eval,
        ContentAssembly.data, ContentAssembly.lamX, ContentAssembly.qlam, diagonal,
        DFinsupp.smul_apply, DirectSum.smul_apply]
  · simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum, eb,
      PairingModel.thetaL, PairingModel.thetaTot, Prod.snd_sum]

/-- The degree-one pairing `B(u, v) = Tr(u ∪ v)` of `gradedBlock a T` has matrix `Ω`. -/
theorem pairing_eb (i j : Fin 4) :
    (gradedBlock a T).Tr ((gradedBlock a T).mul (eb i) (eb j)) = Ω i j := by
  rw [ContentAssembly.R2_Ω]
  simp only [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum,
    PairingModel.mulL, PairingModel.trT, eb]
  simp [PairingModel.mul, PairingModel.B_lof, PairingModel.lof_eval]
  fin_cases i <;> fin_cases j <;> simp [ContentAssembly.data, ContentAssembly.swp,
    ContentAssembly.sgn, ContentAssembly.qswp, ContentAssembly.qsgn]

/-- The star `*₁` of `gradedBlock a T` is `J v = S v̄`: on the basis, `*₁ eb i = Σ_j S j i eb j`. -/
theorem star_eb (i : Fin 4) : (gradedBlock a T).st 1 (eb i) = ∑ j, S j i • eb j := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum, eb,
      PairingModel.st, PairingModel.st1, Prod.fst_sum]
  · ext k
    rcases k with ⟨e, _⟩ | ⟨e, _⟩ | ⟨⟨⟩, k⟩
    · exact e.elim
    · exact e.elim
    · simp only [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum,
        PairingModel.st, PairingModel.st1]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, PairingModel.star_apply, Prod.snd_sum,
        Prod.fst_sum, Prod.smul_mk]
      fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_four, eb, PairingModel.lof_eval,
        ContentAssembly.data, ContentAssembly.tau, ContentAssembly.t, ContentAssembly.qtau,
        ContentAssembly.qt, DirectSum.smul_apply, S] <;>
        erw [DFinsupp.neg_apply, PairingModel.lof_eval] <;> simp
  · simp [gradedBlock, ContentAssembly.gradedDatum, PairingModel.gradedDatum, eb,
      PairingModel.st, PairingModel.st1, Prod.snd_sum]

/-- **`prop:R2` (i), about the block itself.** `gradedBlock a T` is a graded Weil datum of type
`(1, 0)` (with Hermitian nondegenerate `h_j`); `V¹` has basis `eb 0, …, eb 3`, on which its generator,
degree-one pairing and star are the matrices `Θ`, `Ω`, `S` of `def:R2-block`; `J² = -1`
(`S S̄ = -1`); `h₀`, `h₂` are positive definite. Not encoded (fields missing from
`HermAlgebraDatum`): AW3 perfectness of the pairing of eigenlines, associativity and graded
commutativity of the product (proved separately for the underlying `PairingModel.mul`). -/
theorem axioms_block :
    (∀ i, eb i ∈ (gradedBlock a T).G 1) ∧
    (∀ x ∈ (gradedBlock a T).G 1, x = ∑ i, x.2.1 (Sum.inr (Sum.inr ((), i))) • eb i) ∧
    (∀ i, (gradedBlock a T).Θ (eb i) = ∑ j, Θ a T j i • eb j) ∧
    (∀ i j, (gradedBlock a T).Tr ((gradedBlock a T).mul (eb i) (eb j)) = Ω i j) ∧
    (∀ i, (gradedBlock a T).st 1 (eb i) = ∑ j, S j i • eb j) ∧
    S * S.map conj = -1 ∧
    ∀ c : ℂ, c ≠ 0 → 0 < ((gradedBlock a T).h 0 (c, 0, 0) (c, 0, 0)).re ∧
      0 < ((gradedBlock a T).h 2 (0, 0, c) (0, 0, c)).re :=
  ⟨eb_mem a T, fun _ hx => eq_sum_eb a T hx, theta_eb a T, pairing_eb a T, star_eb a T,
    quaternionic, fun _ hc => gradedBlock_h_pos a T hc⟩

/-! ### `prop:R2` (ii): signature `(2, 2)` -/

/-- Columns `e₁ - f₂, e₂ + f₁, e₁ + f₂, e₂ - f₁`. -/
def sigBasis : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 1, 0;
     0, 1, 0, 1;
     0, 1, 0, -1;
     -1, 0, 1, 0]

/-- `Pᵀ H P = diag(2, 2, -2, -2)` with `P` real and invertible: `h₁` has signature `(2, 2)`. -/
theorem signature :
    sigBasisᵀ * H * sigBasis = diagonal ![2, 2, -2, -2] ∧ sigBasis.map conj = sigBasis ∧
      IsUnit sigBasis.det := by
  refine ⟨?_, ?_, ?_⟩
  · rw [H_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigBasis, mul_apply, Fin.sum_univ_four, diagonal] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [sigBasis]
  · refine Matrix.isUnit_det_of_left_inverse (B := (1 / 2 : ℂ) • sigBasisᵀ) ?_
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigBasis, mul_apply, Fin.sum_univ_four, one_apply] <;> norm_num

/-- **`prop:R2` (ii).** `H = ΩS = [[0, R], [-R, 0]]`, `h₁` is Hermitian, nondegenerate
(`H² = 1`) of signature `(2, 2)`, and `h₁(e₁ + f₂, e₁ + f₂) = -2`. -/
theorem form :
    H = !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0] ∧ H.IsHermitian ∧ H * H = 1 ∧
      sigBasisᵀ * H * sigBasis = diagonal ![2, 2, -2, -2] ∧ IsUnit sigBasis.det ∧
      h ![1, 0, 0, 1] ![1, 0, 0, 1] = -2 :=
  ⟨H_eq, H_isHermitian, H_sq, signature.1, signature.2.2, h_neg⟩

/-! ### `prop:R2` (iii): the eigenvalues are off the line -/

/-- **`prop:R2` (iii).** Every eigenvalue of `Θ` has real part `1/2 + a` or `1/2 - a`. -/
theorem re_of_eigen {μ : ℂ} {v : Fin 4 → ℂ} (hv : v ≠ 0) (h : Θ a T *ᵥ v = μ • v) :
    μ.re = 1 / 2 + a ∨ μ.re = 1 / 2 - a := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc; push Not at hc; exact hv (funext hc)
  have hk' := congrFun h k
  rw [Θ_eq_diagonal, mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hk'
  have hμ := (mul_left_inj' hk).1 hk'
  fin_cases k <;> simp [lam] at hμ <;> rw [← hμ] <;> simp <;> ring_nf <;> simp

/-- Hence no eigenvalue lies on `Re s = 1/2` when `a ≠ 0`. -/
theorem re_ne_half_of_eigen (ha : a ≠ 0) {μ : ℂ} {v : Fin 4 → ℂ} (hv : v ≠ 0)
    (h : Θ a T *ᵥ v = μ • v) : μ.re ≠ 1 / 2 := by
  rcases re_of_eigen a T hv h with h' | h' <;> rw [h'] <;> intro h'' <;> apply ha <;> linarith

/-! ### `prop:R3` -/

/-- **`prop:R3` (i).** For `T ≠ 0` and `n ∈ ℤ`, `Θ - n` is bijective, so the twist cone
`C_n(V, Θ) = [V --(Θ - n)--> V]` has zero cohomology in degrees `0` and `1`. -/
theorem cone_acyclic (hT : T ≠ 0) (n : ℤ) :
    LinearMap.ker (toLin' (Θ a T - scalar (Fin 4) (n : ℂ))) = ⊥ ∧
      LinearMap.range (toLin' (Θ a T - scalar (Fin 4) (n : ℂ))) = ⊤ := by
  obtain ⟨u, hu⟩ := isUnit_sub_intCast a T hT n
  have hb : Function.Bijective (toLin' (Θ a T - scalar (Fin 4) (n : ℂ))) := by
    rw [← hu]
    refine ⟨fun x y hxy => ?_, fun y => ⟨(u⁻¹ : (Matrix (Fin 4) (Fin 4) ℂ)ˣ).1 *ᵥ y, ?_⟩⟩
    · have := congrArg (fun z => (u⁻¹ : (Matrix (Fin 4) (Fin 4) ℂ)ˣ).1 *ᵥ z) hxy
      simpa [toLin'_apply, mulVec_mulVec] using this
    · simp [toLin'_apply, mulVec_mulVec]
  exact ⟨LinearMap.ker_eq_bot.2 hb.1, LinearMap.range_eq_top.2 hb.2⟩

/-- `p(s) = ((w - a)² + T²)((w + a)² + T²)` with `w = s - 1/2`. -/
theorem p_eq_mul (s : ℂ) :
    p a T s = ((s - 1 / 2 - a) ^ 2 + (T : ℂ) ^ 2) * ((s - 1 / 2 + a) ^ 2 + (T : ℂ) ^ 2) := by
  simp only [p]; ring

/-- `p(s) > 0` for real `s` when `T ≠ 0`. -/
theorem p_real_pos (hT : T ≠ 0) (x : ℝ) :
    p a T x = (((x - 1 / 2 - a) ^ 2 + T ^ 2) * ((x - 1 / 2 + a) ^ 2 + T ^ 2) : ℝ) ∧
      0 < ((x - 1 / 2 - a) ^ 2 + T ^ 2) * ((x - 1 / 2 + a) ^ 2 + T ^ 2) := by
  refine ⟨by simp only [p]; push_cast; ring, ?_⟩
  have hT2 : 0 < T ^ 2 := by positivity
  positivity

/-- The polynomial `p = w⁴ + 2(T² - a²)w² + (T² + a²)²`, `w = X - 1/2`. -/
noncomputable def pPoly : ℂ[X] :=
  (X - C (1 / 2)) ^ 4 + C (2 * ((T : ℂ) ^ 2 - (a : ℂ) ^ 2)) * (X - C (1 / 2)) ^ 2 +
    C (((T : ℂ) ^ 2 + (a : ℂ) ^ 2) ^ 2)

theorem eval_pPoly (s : ℂ) : (pPoly a T).eval s = p a T s := by
  simp [pPoly, p]

theorem natDegree_pPoly : (pPoly a T).natDegree = 4 := by
  have h4 : ((X - C (1 / 2 : ℂ)) ^ 4).natDegree = 4 := by
    rw [natDegree_pow, natDegree_X_sub_C]
  have h2 : (C (2 * ((T : ℂ) ^ 2 - (a : ℂ) ^ 2)) * (X - C (1 / 2)) ^ 2 +
      C (((T : ℂ) ^ 2 + (a : ℂ) ^ 2) ^ 2)).natDegree < 4 := by
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [natDegree_pow, natDegree_X_sub_C]; norm_num
    · rw [natDegree_C]; norm_num
  unfold pPoly
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt (by rw [h4]; exact h2), h4]

/-- **`prop:R3` (ii).** `p(s) = det(s - Θ)` equals `((w - a)² + T²)((w + a)² + T²)` and the
displayed quartic, satisfies `p(1 - s) = p(s)`, is positive at real `s` (`T ≠ 0`), and is a
polynomial of degree four. -/
theorem poly (hT : T ≠ 0) :
    (∀ s, (scalar (Fin 4) s - Θ a T).det = p a T s) ∧
    (∀ s, p a T s = ((s - 1 / 2 - a) ^ 2 + (T : ℂ) ^ 2) * ((s - 1 / 2 + a) ^ 2 + (T : ℂ) ^ 2)) ∧
    (∀ s, p a T (1 - s) = p a T s) ∧
    (∀ x : ℝ, 0 < ((x - 1 / 2 - a) ^ 2 + T ^ 2) * ((x - 1 / 2 + a) ^ 2 + T ^ 2) ∧
      p a T x = (((x - 1 / 2 - a) ^ 2 + T ^ 2) * ((x - 1 / 2 + a) ^ 2 + T ^ 2) : ℝ)) ∧
    (∀ s, (pPoly a T).eval s = p a T s) ∧ (pPoly a T).natDegree = 4 :=
  ⟨det_eq a T, p_eq_mul a T, p_one_sub a T,
    fun x => ⟨(p_real_pos a T hT x).2, (p_real_pos a T hT x).1⟩, eval_pPoly a T,
    natDegree_pPoly a T⟩

end WeilRH.R2
