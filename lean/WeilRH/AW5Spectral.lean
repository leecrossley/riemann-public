/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.AW5Contains
import WeilRH.HilbertSelfAdjoint

/-!
# The diagonal operator of AW5 (`prop:aw5-contains` (iii), diagonal model)

Source: `latex/notes.tex`, Proposition `prop:aw5-contains` (iii): under AW5 in degree `j`, `T_j` is
the diagonal operator of an orthonormal basis of `𝓗^j` consisting of eigenvectors of `Θ_j` in `V^j`;
its spectrum is pure point, equal to `{(ρ - j/2)/i : ρ ∈ spec Θ_j}` with the multiplicities `m_j`,
without finite accumulation point.

`aw5_spectral` combines `prop:aw5-contains` (i) (`AW5Contains.isInfPol_of_aw5`) with `prop:hilbert`
(`Hilbert.exists_spectral`), as the manuscript's proof does, and adds the identification of the
spectrum: a real `μ` is a diagonal entry `τ_k` iff `j/2 + iμ` is an eigenvalue of `Θ`.

## What is not encoded

* AW5's unitary group `U_j` on `𝓗^j` and its generator are not modelled (Mathlib has no Stone
  theorem). `T_j` is therefore *the* diagonal operator `diag(τ_k)` of the theorem, which is
  self-adjoint and extends `-i(Θ - j/2)` on `V`; the step "`T_j = -iA_j` is the closure of its
  restriction to `V^j`" of the manuscript's proof, which identifies this operator with the generator
  of `U_j`, is outside the encoding.
* The multiplicity clause (`#{k : τ_k = μ} = m_j(j/2 + iμ)`) is `aw5_spectral_mult` (round 74),
  with `m_j` the algebraic multiplicity `dim V_{(j/2+iμ)}` (`maxGenEigenspace`).
* (iv) (trace class) is not formalized: it needs `U_j`, condition (G), `prop:exp-unique` (i), and
  trace-class operators, none of which are available here.
-/

open Complex

namespace WeilRH.AW5Spectral

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

open WeilRH.Hilbert

lemma incl_eq_zero {h : PosHermForm V} {x : V} (hx : incl h x = 0) : x = 0 := by
  by_contra hne
  have h1 := h.re_pos x hne
  have h2 : (inner ℂ (incl h x) (incl h x)) = h.toFun x x := inner_incl h x x
  rw [hx, inner_zero_left] at h2
  rw [← h2] at h1
  simp at h1

/-- **`prop:aw5-contains` (iii), diagonal model.** On a spectral core `(V, Θ)` with AW5 in degree `j`
(`AW5Local`), the completion `𝓗` of `(V, h)` has a Hilbert basis `b_k = e_k` of eigenvectors of `Θ`
in `V`, `Θ e_k = (j/2 + iτ_k) e_k`, such that `T = diag(τ_k)` is self-adjoint, extends `-i(Θ - j/2)`
on `V`, has finite multiplicities and no finite accumulation point, every eigenvector of `T` lies in
the span of the `b_k` with that eigenvalue, `T - μ` is invertible off `{τ_k}`, and the set `{τ_k}`
is `{(ρ - j/2)/i : ρ ∈ spec Θ}`. -/
theorem aw5_spectral {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hU : AW5Contains.AW5Local h Θ j) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ),
      (∀ k, b k = incl h (e k)) ∧
      (∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k) ∧
      IsSelfAdjoint (Diag.op b τ) ∧
      (∀ x : V, ∃ hx : incl h x ∈ (Diag.op b τ).domain,
        Diag.op b τ ⟨incl h x, hx⟩ = incl h (T Θ j x)) ∧
      (∀ μ : ℂ, {k | (τ k : ℂ) = μ}.Finite) ∧
      (∀ z : ℂ, ¬ AccPt z (Filter.principal (Set.range fun k => (τ k : ℂ)))) ∧
      (∀ (μ : ℂ) (x : (Diag.op b τ).domain), Diag.op b τ x = μ • (x : Completion h) →
        (x : Completion h) ∈ Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ})) ∧
      (∀ μ : ℂ, μ ∉ Set.range (fun k => (τ k : ℂ)) →
        ∀ y : Completion h, ∃! x : (Diag.op b τ).domain,
          Diag.op b τ x - μ • (x : Completion h) = y) ∧
      (∀ μ : ℝ, (∃ k, τ k = μ) ↔ Θ.HasEigenvalue ((j / 2 : ℂ) + I * (μ : ℂ))) := by
  have hpol := AW5Contains.isInfPol_of_aw5 (AW5Contains.locFin_of_spectralCore hS) hU
  obtain ⟨ι, b, e, τ, hb, he, hsa, hext, hfin, hdisc, -, hspan, hres⟩ := exists_spectral hS hpol
  refine ⟨ι, b, e, τ, hb, he, hsa, hext, hfin, hdisc, hspan, hres, fun μ => ⟨?_, ?_⟩⟩
  · rintro ⟨k, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (he k), ?_⟩
    intro h0
    have : b k = 0 := by rw [hb k, h0, map_zero]
    have hn := b.orthonormal.1 k
    rw [this, norm_zero] at hn
    exact zero_ne_one hn
  · intro hμ
    obtain ⟨x, hxe, hx0⟩ := hμ.exists_hasEigenvector
    have hΘx : Θ x = ((j / 2 : ℂ) + I * (μ : ℂ)) • x := Module.End.mem_eigenspace_iff.mp hxe
    have hTx : T Θ j x = (μ : ℂ) • x := T_apply_of_eq hΘx
    obtain ⟨hxd, hop⟩ := hext x
    have hop' : Diag.op b τ ⟨incl h x, hxd⟩ = (μ : ℂ) • ((⟨incl h x, hxd⟩ : (Diag.op b τ).domain) :
        Completion h) := by
      rw [hop, hTx, map_smul]
    have hmem := hspan (μ : ℂ) _ hop'
    by_contra hnone
    push_neg at hnone
    have hempty : {k | (τ k : ℂ) = (μ : ℂ)} = ∅ := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hk => hnone k (by exact_mod_cast hk)
    rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hmem
    exact hx0 (incl_eq_zero hmem)

/-- The eigenvectors `e_k` with `τ_k = μ` span the `Θ`-eigenspace of `j/2 + iμ`, and they are
linearly independent; so their number is its dimension. -/
lemma card_eq_finrank_eigenspace {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    {ι : Type u} (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ)
    (hb : ∀ k, b k = incl h (e k))
    (he : ∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k)
    (hext : ∀ x : V, ∃ hx : incl h x ∈ (Diag.op b τ).domain,
        Diag.op b τ ⟨incl h x, hx⟩ = incl h (T Θ j x))
    (hspan : ∀ (μ : ℂ) (x : (Diag.op b τ).domain), Diag.op b τ x = μ • (x : Completion h) →
        (x : Completion h) ∈ Submodule.span ℂ (b '' {k | (τ k : ℂ) = μ}))
    (μ : ℝ) (hK : {k | (τ k : ℂ) = (μ : ℂ)}.Finite) :
    hK.toFinset.card = Module.finrank ℂ (Θ.eigenspace ((j / 2 : ℂ) + I * (μ : ℂ))) := by
  set K := {k | (τ k : ℂ) = (μ : ℂ)}
  have hτ : ∀ k ∈ K, τ k = μ := fun k hk => by
    have h' : (τ k : ℂ) = (μ : ℂ) := hk
    exact_mod_cast h'
  -- the `e_k`, `k ∈ K`, are linearly independent
  have hli : LinearIndependent ℂ (fun k : K => e k) := by
    apply LinearIndependent.of_comp (incl h)
    have : (incl h) ∘ (fun k : K => e k) = fun k : K => b k := funext fun k => (hb k).symm
    rw [this]
    exact b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  -- they span the eigenspace
  have hspanE : Submodule.span ℂ (Set.range fun k : K => e k) =
      Θ.eigenspace ((j / 2 : ℂ) + I * (μ : ℂ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨k, hk⟩, rfl⟩
      exact Module.End.mem_eigenspace_iff.2 (by rw [he k, hτ k hk])
    · intro x hx
      have hΘx : Θ x = ((j / 2 : ℂ) + I * (μ : ℂ)) • x := Module.End.mem_eigenspace_iff.1 hx
      obtain ⟨hxd, hop⟩ := hext x
      have hop' : Diag.op b τ ⟨incl h x, hxd⟩ = (μ : ℂ) • ((⟨incl h x, hxd⟩ :
          (Diag.op b τ).domain) : Completion h) := by
        rw [hop, T_apply_of_eq hΘx, map_smul]
      have hmem := hspan (μ : ℂ) _ hop'
      have himg : b '' K = (incl h) '' (Set.range fun k : K => e k) := by
        ext y; constructor
        · rintro ⟨k, hk, rfl⟩; exact ⟨e k, ⟨⟨k, hk⟩, rfl⟩, (hb k).symm⟩
        · rintro ⟨_, ⟨⟨k, hk⟩, rfl⟩, rfl⟩; exact ⟨k, hk, hb k⟩
      rw [himg, Submodule.span_image] at hmem
      obtain ⟨y, hy, hyx⟩ := hmem
      have : y = x := by
        have h0 : incl h (y - x) = 0 := by rw [map_sub, hyx, sub_self]
        exact sub_eq_zero.1 (incl_eq_zero h0)
      exact this ▸ hy
  have : Fintype K := hK.fintype
  rw [← hspanE, finrank_span_eq_card hli]
  exact Set.Finite.card_toFinset hK

/-- **`prop:aw5-contains` (iii), multiplicity clause.** In the diagonal model of `aw5_spectral`,
each diagonal value `μ` occurs exactly `m_j(j/2 + iμ) = dim V_{j/2+iμ}` times, the algebraic
multiplicity of `j/2 + iμ` as an eigenvalue of `Θ`. -/
theorem aw5_spectral_mult {h : PosHermForm V} {Θ : Module.End ℂ V} {j : ℝ}
    (hS : Spectral.SpectralCore Θ) (hU : AW5Contains.AW5Local h Θ j) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Completion h)) (e : ι → V) (τ : ι → ℝ),
      (∀ k, b k = incl h (e k)) ∧
      (∀ k, Θ (e k) = ((j / 2 : ℂ) + I * (τ k : ℂ)) • e k) ∧
      IsSelfAdjoint (Diag.op b τ) ∧
      ∀ μ : ℝ, ∃ hK : {k | (τ k : ℂ) = (μ : ℂ)}.Finite,
        hK.toFinset.card =
          Module.finrank ℂ (Θ.maxGenEigenspace ((j / 2 : ℂ) + I * (μ : ℂ))) := by
  have hpol := AW5Contains.isInfPol_of_aw5 (AW5Contains.locFin_of_spectralCore hS) hU
  have hE := AW4Forms.aw4E_of_aw4V hS ⟨h, hpol⟩
  obtain ⟨ι, b, e, τ, hb, he, hsa, hext, hfin, -, -, hspan, -⟩ := exists_spectral hS hpol
  refine ⟨ι, b, e, τ, hb, he, hsa, fun μ => ⟨hfin μ, ?_⟩⟩
  rw [AW4Forms.maxGenEigenspace_eq_eigenspace hE]
  exact card_eq_finrank_eigenspace b e τ hb he hext hspan μ (hfin μ)

end WeilRH.AW5Spectral
