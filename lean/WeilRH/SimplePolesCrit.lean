import WeilRH.XiK

/-!
# Simple poles of `Λ_K` from a bound at `s = 1` (round 64)

Round 63 removed the last arithmetic hypothesis (`NonvanishingRight`) on the `X̄_K` side; the only
analytic hypothesis left is `DedekindContinuation.SimplePoles` (Hecke). Mathlib v4.34.1 does **not**
contain Hecke's theorem: `Mathlib/NumberTheory/NumberField/DedekindZeta.lean` defines
`dedekindZeta` as an `L`-series and proves only the class number formula
(`tendsto_sub_one_mul_dedekindZeta_nhdsGT`, a limit along `(1, ∞)`); there is no completed
Dedekind zeta, no meromorphic continuation and no functional equation, and Poisson summation
(`Real.tsum_eq_tsum_fourier`, `Complex.tsum_exp_neg_quadratic`) exists only on `ℝ`, not for
lattices in `ℝⁿ`. So `SimplePoles` cannot be discharged from Mathlib for general `K`.

What this file does prove is a reduction: given any continuation `C` (holomorphy off `{0, 1}`
and the functional equation, the fields of `DedekindContinuation`), the simple-pole hypothesis is
**equivalent** to the single bound

  `(s - 1) Λ_K(s)` is bounded on some punctured disc around `1` (`BoundedAtOne`).

The bound at `0` is not needed: it follows from the functional equation `Λ(1 - s) = Λ(s)`.
The proof is Riemann's removable-singularity theorem
(`Complex.differentiableOn_update_limUnder_of_bddAbove`) applied at `1` and at `0`.

* `DedekindContinuation.BoundedAtOne C` — the bound.
* `DedekindContinuation.simplePolesOfBoundedAtOne` — `BoundedAtOne C → SimplePoles C`.
* `DedekindContinuation.boundedAtOne_of_simplePoles` — the converse.
* `DedekindContinuation.boundedAtOne_rat` — the bound holds for `ℚ` (via `SimplePoles.ofRat`).

So Hecke's theorem enters this repository through exactly one analytic statement about `Λ_K`
near `s = 1`, beyond the existence of the continuation itself.
-/

open NumberField Filter Topology Complex Metric Function Set

noncomputable section

namespace WeilRH

variable {K : Type*} [Field K] [NumberField K]

namespace DedekindContinuation

/-- `(s - 1) Λ_K(s)` is bounded on a punctured disc around `s = 1`: the only analytic input
beyond the continuation that the simple-pole hypothesis needs. -/
def BoundedAtOne (C : DedekindContinuation K) : Prop :=
  ∃ r > 0, BddAbove ((fun s => ‖(s - 1) * C.Λ s‖) '' (ball (1 : ℂ) r \ {1}))

lemma differentiableOn_xiK (C : DedekindContinuation K) :
    DifferentiableOn ℂ (xiK C) ({0, 1}ᶜ : Set ℂ) := by
  have h : DifferentiableOn ℂ (fun s : ℂ => s * (s - 1)) ({0, 1}ᶜ : Set ℂ) :=
    (differentiable_id.mul (differentiable_id.sub_const 1)).differentiableOn
  exact h.mul C.differentiableOn

private lemma norm_le_of_mem_ball_one {s : ℂ} {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (hs : s ∈ ball (1 : ℂ) ρ) :
    ‖s‖ ≤ 3 / 2 := by
  have h := mem_ball.1 hs
  rw [dist_eq] at h
  calc ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
    _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 / 2 := by rw [norm_one]; linarith

private lemma ne_zero_of_mem_ball_one {s : ℂ} {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (hs : s ∈ ball (1 : ℂ) ρ) :
    s ≠ 0 := by
  rintro rfl
  have h := mem_ball.1 hs
  rw [dist_eq, zero_sub, norm_neg, norm_one] at h
  linarith

private lemma ne_one_of_mem_ball_zero {s : ℂ} {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (hs : s ∈ ball (0 : ℂ) ρ) :
    s ≠ 1 := by
  rintro rfl
  have h := mem_ball.1 hs
  rw [dist_eq, sub_zero, norm_one] at h
  linarith

/-- **Simple poles from a bound at `1`.** If `(s - 1) Λ_K(s)` is bounded near `1`, then
`s (s - 1) Λ_K(s)` extends to an entire function. The bound at `0` comes from the functional
equation. -/
def simplePolesOfBoundedAtOne (C : DedekindContinuation K) (hB : C.BoundedAtOne) :
    C.SimplePoles := by
  classical
  refine
    { ξ := update (update (xiK C) 1 (limUnder (𝓝[≠] 1) (xiK C))) 0 (limUnder (𝓝[≠] 0) (xiK C))
      differentiable := ?_
      eq_xiK := fun s h0 h1 => by rw [update_of_ne h0, update_of_ne h1] }
  obtain ⟨r, hr, B, hBd⟩ := hB
  set ρ : ℝ := min r (1 / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min hr (by norm_num)
  have hρ2 : ρ ≤ 1 / 2 := min_le_right _ _
  have hρr : ρ ≤ r := min_le_left _ _
  -- bound for `(s - 1) Λ s` on the small punctured disc at `1`
  have hb1 : ∀ s ∈ ball (1 : ℂ) ρ \ {1}, ‖(s - 1) * C.Λ s‖ ≤ B := fun s hs =>
    hBd ⟨s, ⟨ball_subset_ball hρr hs.1, hs.2⟩, rfl⟩
  have hfd := C.differentiableOn_xiK
  -- removable singularity at `1`
  have hU1 : ball (1 : ℂ) ρ ∈ 𝓝 (1 : ℂ) := ball_mem_nhds _ hρ0
  have hd1 : DifferentiableOn ℂ (xiK C) (ball (1 : ℂ) ρ \ {1}) := hfd.mono fun s hs => by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨ne_zero_of_mem_ball_one hρ2 hs.1, hs.2⟩
  have hbd1 : BddAbove (norm ∘ xiK C '' (ball (1 : ℂ) ρ \ {1})) := by
    refine ⟨3 / 2 * B, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    simp only [comp_apply, xiK]
    rw [mul_assoc, norm_mul]
    exact mul_le_mul (norm_le_of_mem_ball_one hρ2 hs.1) (hb1 s hs) (norm_nonneg _) (by norm_num)
  have hg1 := Complex.differentiableOn_update_limUnder_of_bddAbove hU1 hd1 hbd1
  -- removable singularity at `0`, via the functional equation
  have hU0 : ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hρ0
  have hd0 : DifferentiableOn ℂ (xiK C) (ball (0 : ℂ) ρ \ {0}) := hfd.mono fun s hs => by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hs.2, ne_one_of_mem_ball_zero hρ2 hs.1⟩
  have hbd0 : BddAbove (norm ∘ xiK C '' (ball (0 : ℂ) ρ \ {0})) := by
    refine ⟨3 / 2 * B, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : s ≠ 0 := hs.2
    have hs1 : s ≠ 1 := ne_one_of_mem_ball_zero hρ2 hs.1
    have ht : 1 - s ∈ ball (1 : ℂ) ρ \ {1} := by
      refine ⟨?_, ?_⟩
      · have h := mem_ball.1 hs.1
        rw [dist_eq, sub_zero] at h
        rw [mem_ball, dist_eq, show 1 - s - 1 = -s by ring, norm_neg]
        exact h
      · simpa [sub_eq_self] using hs0
    simp only [comp_apply]
    rw [← xiK_one_sub C hs0 hs1]
    simp only [xiK]
    rw [mul_assoc, norm_mul]
    exact mul_le_mul (norm_le_of_mem_ball_one hρ2 ht.1) (hb1 _ ht) (norm_nonneg _) (by norm_num)
  have hg0 := Complex.differentiableOn_update_limUnder_of_bddAbove hU0 hd0 hbd0
  -- assemble: three open sets cover `ℂ`
  intro z
  by_cases hz0 : z = 0
  · subst hz0
    have hc : DifferentiableOn ℂ
        (update (update (xiK C) 1 (limUnder (𝓝[≠] 1) (xiK C))) 0 (limUnder (𝓝[≠] 0) (xiK C)))
        (ball (0 : ℂ) ρ) := by
      refine hg0.congr fun s hs => ?_
      by_cases hs0 : s = 0
      · subst hs0; simp
      · rw [update_of_ne hs0, update_of_ne hs0,
          update_of_ne (ne_one_of_mem_ball_zero hρ2 hs)]
    exact hc.differentiableAt hU0
  by_cases hz1 : z = 1
  · subst hz1
    have hc : DifferentiableOn ℂ
        (update (update (xiK C) 1 (limUnder (𝓝[≠] 1) (xiK C))) 0 (limUnder (𝓝[≠] 0) (xiK C)))
        (ball (1 : ℂ) ρ) :=
      hg1.congr fun s hs => by rw [update_of_ne (ne_zero_of_mem_ball_one hρ2 hs)]
    exact hc.differentiableAt hU1
  · have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := DedekindContinuation.isOpen_compl
    have hz : z ∈ ({0, 1}ᶜ : Set ℂ) := by simp [hz0, hz1]
    have hc : DifferentiableOn ℂ
        (update (update (xiK C) 1 (limUnder (𝓝[≠] 1) (xiK C))) 0 (limUnder (𝓝[≠] 0) (xiK C)))
        ({0, 1}ᶜ : Set ℂ) := by
      refine hfd.congr fun s hs => ?_
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
      rw [update_of_ne hs.1, update_of_ne hs.2]
    exact hc.differentiableAt (hopen.mem_nhds hz)

/-- Conversely, simple poles give the bound at `1`: `(s - 1) Λ_K(s) = ξ(s) / s` near `1`. -/
theorem boundedAtOne_of_simplePoles (C : DedekindContinuation K) (P : C.SimplePoles) :
    C.BoundedAtOne := by
  -- `ξ / s` is continuous on the closed ball of radius `1/2` around `1`, hence bounded there
  have hcont : ContinuousOn (fun s : ℂ => P.ξ s / s) (closedBall (1 : ℂ) (1 / 2)) := by
    refine P.differentiable.continuous.continuousOn.div continuousOn_id fun s hs => ?_
    rintro rfl
    have h := mem_closedBall.1 hs
    rw [dist_eq, zero_sub, norm_neg, norm_one] at h
    norm_num at h
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn hcont
  refine ⟨1 / 2, by norm_num, B, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs0 : s ≠ 0 := ne_zero_of_mem_ball_one le_rfl hs.1
  have hs1 : s ≠ 1 := hs.2
  have heq : (s - 1) * C.Λ s = P.ξ s / s := by
    rw [P.eq_xiK s hs0 hs1, xiK]
    field_simp
  show ‖(s - 1) * C.Λ s‖ ≤ B
  rw [heq]
  exact hB s (ball_subset_closedBall hs.1)

/-- The bound holds for `ℚ`. -/
theorem boundedAtOne_rat (C : DedekindContinuation ℚ) : C.BoundedAtOne := by
  refine C.boundedAtOne_of_simplePoles ?_
  exact
    { ξ := (DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat).ξ
      differentiable := (DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat).differentiable
      eq_xiK := fun s h0 h1 => by
        rw [(DedekindContinuation.SimplePoles.ofRat DedekindContinuation.rat).eq_xiK s h0 h1,
          xiK_eqOn DedekindContinuation.rat C h0 h1] }

/-- `SimplePoles C` holds iff `BoundedAtOne C`. -/
theorem nonempty_simplePoles_iff (C : DedekindContinuation K) :
    Nonempty C.SimplePoles ↔ C.BoundedAtOne :=
  ⟨fun ⟨P⟩ => C.boundedAtOne_of_simplePoles P, fun h => ⟨C.simplePolesOfBoundedAtOne h⟩⟩

end DedekindContinuation

end WeilRH

end
