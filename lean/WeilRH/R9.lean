/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.ElementaryGaps

/-!
# Common real zeros of `E` and `E^#`, and cyclic vectors (`prop:R9`)

Source: `latex/notes.tex`, Proposition `prop:R9`, with `def:hb` (reflection `E^#(z) = conj E(conj z)`
and HB companion `E_G = G + iG'`).

* (i) If `G` is entire with `G^# = G`, then `E_G^# = G - iG'` (`reflect_companion`); and if `G` has a
  zero of order `k ≥ 1` at `r`, then `G + iG'` and `G - iG'` vanish at `r` to order exactly `k - 1`
  (`order_companion`, `order_reflect_companion`).
* (ii) For `G = (z² - 1)²`: `E = (z² - 1)(z² - 1 + 4iz)`, `E^# = (z² - 1)(z² - 1 - 4iz)`, and `±1` are
  simple zeros of both (`example_E`, `example_Esharp`, `example_order`).
* (iii) A self-adjoint operator with a cyclic vector has eigenspaces of dimension at most one
  (`ker_le_span`).

## Representation

* Orders are `analyticOrderAt`. In (i) the point `r` may be any complex number (the manuscript takes
  `r ∈ ℝ`); `G ≢ 0` near `r` is implied by the finite order.
* (iii) is stated for a **bounded** self-adjoint `A : H →L[ℂ] H`, with "cyclic" meaning that the
  polynomial orbit `{Aⁿ v₀}` spans a dense subspace. The manuscript allows unbounded `A` and uses the
  resolvent orbit `{v₀} ∪ {R_z v₀}`; for bounded `A` the two notions of cyclicity agree (standard,
  not proved here). "`dim ker(A - λ) ≤ 1`" is `ker(A - λ) ⊆ ℂ w` for some `w`.
-/

open Complex Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace WeilRH.R9

open WeilRH.R17

/-- The reflection commutes with differentiation: `(G')^# = (G^#)'`. -/
theorem deriv_reflect {G : ℂ → ℂ} (hG : Differentiable ℂ G) (z : ℂ) :
    deriv (reflect G) z = reflect (deriv G) z := by
  have h := ((hG (conj z)).hasDerivAt).conj_conj
  rw [Complex.conj_conj] at h
  exact h.deriv

/-- **`prop:R9` (i), first claim.** If `G` is entire and `G^# = G`, then `(G + iG')^# = G - iG'`. -/
theorem reflect_companion {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hsym : reflect G = G) :
    reflect (fun z => G z + I * deriv G z) = fun z => G z - I * deriv G z := by
  funext z
  have hd : reflect (deriv G) z = deriv G z := by
    rw [← deriv_reflect hG, hsym]
  have hG' : conj (G (conj z)) = G z := congrFun hsym z
  have hd' : conj (deriv G (conj z)) = deriv G z := hd
  simp only [reflect, map_add, map_mul, conj_I]
  rw [hG', hd']
  ring

/-- Orders of `G + c G'`: if `G` has a zero of order `k ≥ 1` at `r` and `c ≠ 0`, then `G + c G'`
has a zero of order exactly `k - 1` at `r`. -/
theorem order_add_smul_deriv {G : ℂ → ℂ} (hG : Differentiable ℂ G) {r : ℂ} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : analyticOrderAt G r = k) {c : ℂ} (hc : c ≠ 0) :
    analyticOrderAt (fun z => G z + c * deriv G z) r = (k - 1 : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hGa : AnalyticAt ℂ G r := hG.analyticAt r
  obtain ⟨U, hUa, hU0, hev⟩ := hGa.analyticOrderAt_eq_natCast.mp hk
  have hEa : AnalyticAt ℂ (fun z => G z + c * deriv G z) r :=
    hGa.add (analyticAt_const.mul (hG.analyticAt r).deriv)
  refine hEa.analyticOrderAt_eq_natCast.mpr ⟨fun z => (z - r) * U z +
      c * (((m + 1 : ℕ) : ℂ) * U z + (z - r) * deriv U z), ?_, ?_, ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const).mul hUa).add (analyticAt_const.mul
      ((analyticAt_const.mul hUa).add ((analyticAt_id.sub analyticAt_const).mul hUa.deriv)))
  · simp only [sub_self, zero_mul, zero_add, add_zero]
    exact mul_ne_zero hc (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) hU0)
  · have hev2 : ∀ᶠ w in 𝓝 r, ∀ᶠ z in 𝓝 w, G z = (z - r) ^ (m + 1) • U z := hev.eventually_nhds
    filter_upwards [hev2, hUa.eventually_analyticAt] with w hw hUw
    have heq : G =ᶠ[𝓝 w] fun z => (z - r) ^ (m + 1) * U z := by
      filter_upwards [hw] with z hz; rw [hz, smul_eq_mul]
    have hderiv : HasDerivAt (fun z => (z - r) ^ (m + 1) * U z)
        (((m + 1 : ℕ) : ℂ) * (w - r) ^ m * 1 * U w + (w - r) ^ (m + 1) * deriv U w) w := by
      have h1 := ((hasDerivAt_id w).sub_const r).pow (m + 1)
      simp only [Nat.add_sub_cancel] at h1
      exact h1.mul hUw.differentiableAt.hasDerivAt
    rw [heq.deriv_eq, hderiv.deriv, hw.self_of_nhds, smul_eq_mul, smul_eq_mul]
    ring

/-- **`prop:R9` (i), orders.** If `G` is entire with a zero of order `k ≥ 1` at `r`, then
`E = G + iG'` vanishes at `r` to order exactly `k - 1`. -/
theorem order_companion {G : ℂ → ℂ} (hG : Differentiable ℂ G) {r : ℂ} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : analyticOrderAt G r = k) :
    analyticOrderAt (fun z => G z + I * deriv G z) r = (k - 1 : ℕ) :=
  order_add_smul_deriv hG hk1 hk I_ne_zero

/-- **`prop:R9` (i), orders for `E^#`.** Under the same hypotheses `G - iG'` vanishes at `r` to
order exactly `k - 1`; with `G^# = G` this is `E^#` (`reflect_companion`). -/
theorem order_reflect_companion {G : ℂ → ℂ} (hG : Differentiable ℂ G) {r : ℂ} {k : ℕ}
    (hk1 : 1 ≤ k) (hk : analyticOrderAt G r = k) :
    analyticOrderAt (fun z => G z - I * deriv G z) r = (k - 1 : ℕ) := by
  have := order_add_smul_deriv hG hk1 hk (neg_ne_zero.mpr I_ne_zero)
  simpa [neg_mul, ← sub_eq_add_neg] using this

/-! ### (ii) The example `G = (z² - 1)²` -/

/-- `G(z) = (z² - 1)²`. -/
noncomputable def G (z : ℂ) : ℂ := (z ^ 2 - 1) ^ 2

lemma G_differentiable : Differentiable ℂ G := by unfold G; fun_prop

lemma deriv_G (z : ℂ) : deriv G z = 4 * z * (z ^ 2 - 1) := by
  have h : HasDerivAt G (2 * (z ^ 2 - 1) * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).sub_const 1).pow 2
    convert this using 1
    · funext x; simp [G]
    · norm_num
  rw [h.deriv]; ring

lemma G_reflect : reflect G = G := by
  funext z; simp [reflect, G, map_sub, map_pow]

/-- **`prop:R9` (ii), `E`.** `E_G(z) = (z² - 1)(z² - 1 + 4iz)`. -/
theorem example_E (z : ℂ) : G z + I * deriv G z = (z ^ 2 - 1) * (z ^ 2 - 1 + 4 * I * z) := by
  rw [deriv_G, G]; ring

/-- **`prop:R9` (ii), `E^#`.** `E_G^#(z) = (z² - 1)(z² - 1 - 4iz)`. -/
theorem example_Esharp (z : ℂ) :
    reflect (fun z => G z + I * deriv G z) z = (z ^ 2 - 1) * (z ^ 2 - 1 - 4 * I * z) := by
  rw [reflect_companion G_differentiable G_reflect]
  show G z - I * deriv G z = _
  rw [deriv_G, G]; ring

lemma order_G (r : ℂ) (hr : r = 1 ∨ r = -1) : analyticOrderAt G r = (2 : ℕ) := by
  have hGa : AnalyticAt ℂ G r := G_differentiable.analyticAt r
  refine hGa.analyticOrderAt_eq_natCast.mpr ⟨fun z => (z + r) ^ 2, by fun_prop, ?_, ?_⟩
  · rcases hr with rfl | rfl <;> norm_num
  · refine Filter.Eventually.of_forall fun z => ?_
    have hr2 : r ^ 2 = 1 := by rcases hr with rfl | rfl <;> norm_num
    rw [G, smul_eq_mul, ← mul_pow]
    congr 1
    linear_combination hr2

/-- **`prop:R9` (ii), simple zeros.** `±1` are simple zeros of both `E = G + iG'` and
`E^# = G - iG'`. -/
theorem example_order (r : ℂ) (hr : r = 1 ∨ r = -1) :
    analyticOrderAt (fun z => G z + I * deriv G z) r = (1 : ℕ) ∧
      analyticOrderAt (fun z => G z - I * deriv G z) r = (1 : ℕ) :=
  ⟨order_companion G_differentiable (by norm_num) (order_G r hr),
    order_reflect_companion G_differentiable (by norm_num) (order_G r hr)⟩

/-! ### (iii) Cyclic vectors force simple eigenvalues -/

section Cyclic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`prop:R9` (iii)**, bounded version. Let `A` be a bounded self-adjoint operator with a cyclic
vector `v₀` (the vectors `Aⁿ v₀` span a dense subspace). Then every eigenspace `ker(A - λ)` lies in
a line `ℂ w`, so `dim ker(A - λ) ≤ 1`. -/
theorem ker_le_span {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {v₀ : H}
    (hcyc : Dense (Submodule.span ℂ (Set.range fun n : ℕ => (A ^ n) v₀) : Set H)) (μ : ℂ) :
    ∃ w : H, LinearMap.ker ((A : H →ₗ[ℂ] H) - μ • 1) ≤ Submodule.span ℂ {w} := by
  set B : H →L[ℂ] H := A - μ • 1
  set K : Submodule ℂ H := LinearMap.ker (B : H →ₗ[ℂ] H)
  have hK : K = LinearMap.ker ((A : H →ₗ[ℂ] H) - μ • 1) := by
    ext x; simp [K, B]
  have hKc : IsClosed (K : Set H) := B.isClosed_ker
  have : CompleteSpace K := hKc.completeSpace_coe
  have hsymm := hA.isSymmetric
  have hmemK : ∀ x, x ∈ K ↔ A x = μ • x := by
    intro x; simp [K, B, sub_eq_zero]
  -- `A` preserves `Kᗮ`
  have horth : ∀ u ∈ Kᗮ, A u ∈ Kᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro v hv
    have hAv := (hmemK v).mp hv
    have := hsymm v u
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hAv, inner_smul_left, hu v hv, mul_zero]
  -- `P A = μ P`
  have hPA : ∀ x, K.starProjection (A x) = μ • K.starProjection x := by
    intro x
    have hdec : x = K.starProjection x + (x - K.starProjection x) := by abel
    have hPx : K.starProjection x ∈ K := K.starProjection_apply_mem x
    have hu : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
    conv_lhs => rw [hdec]
    rw [map_add, map_add, (hmemK _).mp hPx, map_smul,
      K.starProjection_eq_self_iff.mpr hPx,
      K.starProjection_apply_eq_zero_iff.mpr (horth _ hu), add_zero]
  have hPAn : ∀ n : ℕ, K.starProjection ((A ^ n) v₀) = μ ^ n • K.starProjection v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, hPA, ih, smul_smul, pow_succ']
  refine ⟨K.starProjection v₀, ?_⟩
  rw [← hK]
  -- the closed set `{x | P x ∈ ℂ P v₀}` contains the dense span, hence everything
  set L : Submodule ℂ H := Submodule.span ℂ {K.starProjection v₀}
  have hLc : IsClosed (L : Set H) := L.closed_of_finiteDimensional
  have hS : Submodule.span ℂ (Set.range fun n : ℕ => (A ^ n) v₀) ≤ L.comap (K.starProjection : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    show K.starProjection ((A ^ n) v₀) ∈ L
    rw [hPAn]
    exact L.smul_mem _ (Submodule.mem_span_singleton_self _)
  have hclosed : IsClosed {x : H | K.starProjection x ∈ L} :=
    hLc.preimage K.starProjection.continuous
  have hall : ∀ x : H, K.starProjection x ∈ L := by
    intro x
    have hsub : (Submodule.span ℂ (Set.range fun n : ℕ => (A ^ n) v₀) : Set H) ⊆
        {x : H | K.starProjection x ∈ L} := fun y hy => hS hy
    have := hcyc.closure_eq ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  intro w hw
  have := hall w
  rwa [K.starProjection_eq_self_iff.mpr hw] at this

end Cyclic

end WeilRH.R9
