/-
Copyright (c) 2026. All rights reserved.
-/
import WeilRH.KunOrbits

/-!
# Closed orbits of the diagonal flow on a torus (`prop:kun-torus`)

`prop:kun-torus`: on `𝕋 = (ℝ/aℤ) × (ℝ/bℤ)` with the diagonal flow `φ^t(x, y) = (x + t, y + t)`,
closed orbits exist only when `a/b ∈ ℚ` and are then never isolated; for primes,
`log p / log p' ∈ ℚ` iff `p = p'`. "`x ∈ ℚ`" is `x ∈ Set.range ((↑) : ℚ → ℝ)`.

## Main results

* `KunTorus.eq_zero_of_flow_eq_self` (**(i)**): if `a/b ∉ ℚ`, `φ^t z = z` forces `t = 0`.
* `KunTorus.exists_flow_eq_self`, `KunTorus.not_isolated` (**(ii)**): if `a, b > 0` and
  `a/b ∈ ℚ`, every orbit is closed, and every neighbourhood of `z` contains a point whose (closed)
  orbit differs from that of `z`.
* `KunTorus.log_div_log_mem_rat_iff` (**(iii)**), from `KunOrbits.int_mul_log_eq`.
-/

open MeasureTheory

namespace WeilRH.KunTorus

/-- The torus `𝕋 = (ℝ/aℤ) × (ℝ/bℤ)`. -/
abbrev Torus (a b : ℝ) : Type := AddCircle a × AddCircle b

/-- The diagonal flow `φ^t(x, y) = (x + t, y + t)`. -/
def flow (a b : ℝ) (t : ℝ) (z : Torus a b) : Torus a b := (z.1 + t, z.2 + t)

variable {a b : ℝ}

/-- `φ^t z = z` iff `t ∈ aℤ ∩ bℤ`. -/
lemma flow_eq_self_iff {t : ℝ} {z : Torus a b} :
    flow a b t z = z ↔ (∃ n : ℤ, n • a = t) ∧ ∃ m : ℤ, m • b = t := by
  simp only [flow, Prod.ext_iff, add_eq_left, AddCircle.coe_eq_zero_iff]

/-- **`prop:kun-torus` (i).** If `a/b ∉ ℚ`, no point of `𝕋` has a periodic orbit: `φ^t z = z`
forces `t = 0`. -/
theorem eq_zero_of_flow_eq_self (hab : a / b ∉ Set.range ((↑) : ℚ → ℝ)) {z : Torus a b} {t : ℝ}
    (ht : flow a b t z = z) : t = 0 := by
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := flow_eq_self_iff.1 ht
  by_contra h0
  have hn0 : (n : ℝ) ≠ 0 := by rintro h; apply h0; rw [← hn, zsmul_eq_mul, h, zero_mul]
  have hb0 : b ≠ 0 := by rintro rfl; apply h0; rw [← hm, smul_zero]
  apply hab
  refine ⟨(m : ℚ) / n, ?_⟩
  rw [zsmul_eq_mul] at hn hm
  push_cast
  rw [div_eq_div_iff hn0 hb0]
  linear_combination hm - hn

/-- **`prop:kun-torus` (ii), first clause.** If `a, b > 0` and `a/b ∈ ℚ`, every orbit is closed. -/
theorem exists_flow_eq_self (ha : 0 < a) (hb : 0 < b) (hab : a / b ∈ Set.range ((↑) : ℚ → ℝ))
    (z : Torus a b) : ∃ t > 0, flow a b t z = z := by
  obtain ⟨r, hr⟩ := hab
  have hr0 : (0 : ℝ) < r := hr ▸ div_pos ha hb
  refine ⟨r.den * a, by positivity, flow_eq_self_iff.2 ⟨⟨r.den, by simp⟩, ⟨r.num, ?_⟩⟩⟩
  have : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
  rw [zsmul_eq_mul]
  have hd : (r.den : ℝ) ≠ 0 := by positivity
  rw [this, div_eq_div_iff hd hb.ne'] at hr
  linear_combination hr

/-- **`prop:kun-torus` (ii), second clause.** If `a, b > 0` and `a/b ∈ ℚ`, no closed orbit is
isolated among closed orbits: every neighbourhood of `z` contains a point with a closed orbit
different from that of `z`. -/
theorem not_isolated (ha : 0 < a) (hb : 0 < b) (hab : a / b ∈ Set.range ((↑) : ℚ → ℝ))
    (z : Torus a b) {U : Set (Torus a b)} (hU : U ∈ nhds z) :
    ∃ w ∈ U, (∃ t > 0, flow a b t w = w) ∧ w ∉ Set.range fun t => flow a b t z := by
  let g : ℝ → Torus a b := fun s => (z.1, z.2 + s)
  have hg : Continuous g := by fun_prop
  have hg0 : g 0 = z := by simp [g]
  have hpre : g ⁻¹' U ∈ nhds (0 : ℝ) := hg.continuousAt.preimage_mem_nhds (hg0 ▸ hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  -- the `s` with `g s` on the orbit of `z` lie in the countable set `aℤ + bℤ`
  let B : Set ℝ := Set.range fun nm : ℤ × ℤ => nm.1 * a + nm.2 * b
  have hB : B.Countable := Set.countable_range _
  have hbad : ∀ s, g s ∈ Set.range (fun t => flow a b t z) → s ∈ B := by
    rintro s ⟨t, ht⟩
    simp only [flow, g, Prod.ext_iff, add_eq_left, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨⟨n, hn⟩, h2⟩ := ht
    have h3 : ((t - s : ℝ) : AddCircle b) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]; exact add_left_cancel h2
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
    refine ⟨(n, -m), ?_⟩
    rw [zsmul_eq_mul] at hn hm
    push_cast
    linarith
  have hnot : ¬ Set.Ioo 0 ε ⊆ B := by
    intro hsub
    have := measure_mono_null hsub (hB.measure_zero volume)
    rw [Real.volume_Ioo] at this
    simp at this
    linarith
  obtain ⟨s, hs, hsB⟩ := Set.not_subset.1 hnot
  refine ⟨g s, hball ?_, exists_flow_eq_self ha hb hab _, fun h => hsB (hbad s h)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  exact ⟨by linarith [hs.1], hs.2⟩

/-- **`prop:kun-torus` (iii).** For primes `p, p'`, `log p / log p' ∈ ℚ` iff `p = p'`. -/
theorem log_div_log_mem_rat_iff {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) :
    Real.log p / Real.log p' ∈ Set.range ((↑) : ℚ → ℝ) ↔ p = p' := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hne
    have hl' : Real.log p' ≠ 0 := (Real.log_pos (by exact_mod_cast hp'.one_lt)).ne'
    have hrr : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    have hd : (r.den : ℝ) ≠ 0 := by positivity
    rw [hrr, div_eq_div_iff hd hl'] at hr
    have h := (KunOrbits.int_mul_log_eq hp hp' hne (x := r.num) (y := r.den)
      (by push_cast; linear_combination hr)).2
    exact r.den_nz (by exact_mod_cast h)
  · rintro rfl
    have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    exact ⟨1, by simp [div_self hl]⟩

end WeilRH.KunTorus
