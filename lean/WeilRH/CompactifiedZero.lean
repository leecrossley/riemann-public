import Mathlib
import WeilRH.CompactifiedDeligne
import WeilRH.ZetaOrder

/-!
# A nontrivial Kähler retraction: `X̄_K` at twist `n = 0` (round 59)

Round 59 of `lean/ROADMAP-arakelov.md`, on the Flach–Morin path (decision D8). Source:
Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020),
checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:

* §3.1 (p. 523): `RΓ_D(X/ℝ, ℝ(n)) := RΓ(G_ℝ, X(ℂ), ℝ(n)_D)` with
  `ℝ(n)_D = ((2πi)^n ℝ → Ω^0_{X(ℂ)} → ⋯ → Ω^{n-1}_{X(ℂ)})`; for `n = 0` the Ω-part is empty, so
  `ℝ(0)_D = ℝ` (our reading of the displayed complex; FM state the case `n < 0` explicitly).
* §3.2 (p. 523): the Kähler metric gives a retraction `RΓ_D → τ_{<2n} RΓ_D` of the adjunction map
  (FM cite their [13, Remark 2.13], which is not local), and `RΓ(X̄, ℝ(n))` is the fibre of
  `RΓ(X, ℝ(n)) → τ_{<2n} RΓ_D`.
* Prop. 4.14 (p. 534), (i) and (iii): `H^i_ar(X̄, ℂ̃(n)) = 0` for `i ∉ {2n, 2n+1}` and
  `ord_{s=n} ζ(X̄, s) = -dim CH^n(X̄)_ℂ`.

## Which twists give a nontrivial retraction when `X(ℂ)` is finite

For `X = Spec 𝒪_K`, `X(ℂ) = Hom(K, ℂ)` is finite, so `Ω^p_{X(ℂ)} = 0` for `p ≥ 1` and
`Ω^0 = ℂ^{X(ℂ)}`. Hence (cohomology of the displayed complexes, then `G_ℝ`-invariants):

* `n ≥ 1`: `ℝ(n)_D = ((2πi)^n ℝ → ℂ)` per point, injective, so `H^*_D` sits in degree `1 < 2n`:
  `τ_{<2n}` truncates nothing and the retraction is the identity (round 56, `n = 1`).
* `n = 0`: `ℝ(0)_D = ℝ` in degree `0 = 2n`, so `H^0_D = ℝ^{X(ℂ)}^{G_ℝ} = ℝ^{InfinitePlace K}` is
  killed by `τ_{<0}`: the retraction is **not** the identity (`compactZero_adj_not_surjective`).
* `n < 0`: `H^0_D = ((2πi)^n ℝ)^{X(ℂ)}^{G_ℝ}` sits in degree `0 ≥ 2n` and is also killed; there
  `RΓ(X, ℝ(n)) = 0`, so all groups of `X̄_K` vanish (not formalized here).

So the twists with `H^{≥2n}_D ≠ 0` are exactly `n ≤ 0`. This file formalizes `n = 0`. In every case
for `X̄_K` the retraction is **forced** (the truncation of a complex concentrated in one degree): a
retraction that genuinely depends on the Kähler metric needs `dim X(ℂ) > 0`, e.g. `ℙⁿ_{𝒪_K}`,
which needs analytic input Mathlib lacks.

## Main results

* `zeroDatum K`: the `n = 0` Deligne datum of `X_K`: `H^0(X_K, ℝ(0)) = ℝ`,
  `H^0_D = ℝ^{InfinitePlace K}`, the regulator is the diagonal, `H^1_c = ℝ^{places}/ℝ`, all else 0.
  `finrank_Hc_one`: `dim H^1_c(X_K, ℝ(0)) = r₁ + r₂ - 1`.
* `compactZero K`: the `CompactifiedDatum` at `n = 0`: `τ_{<0} RΓ_D = 0`, the retraction is the zero
  map, `RΓ(X̄_K, ℝ(0)) = RΓ(X_K, ℝ(0))`. `compactZero_adj_not_surjective`: the adjunction is not
  surjective in degree `0` — the truncation is nontrivial.
* `harZero i := H^i(X̄_K, ℝ(0)) ⊕ H^{i-1}(X̄_K, ℝ(0))`: `prop414_zero_shape` — zero for `i ∉ {0, 1}`,
  one-dimensional in degrees `0, 1`.
* `fm414_zero`: **FM Prop. 4.14 (i), (iii) at `n = 0` for `X̄_K`**:
  `ord_{s=0} ζ(X̄_K, s) = -1 = -dim H^0_ar(X̄_K, ℝ̃(0))` (round 58's order theorem). This agrees
  with `CH^0(X̄_K) = ℤ` (`X̄_K` connected), whose real dimension is `1`.

## Fidelity

* Modelled by definition: `H^0(X_K, ℝ(0)) = ℝ` (Bloch's `ℤ(0) = ℤ` on a connected scheme,
  standard, not in FM), `H^0_D = ℝ^{InfinitePlace K}` (the `G_ℝ`-invariant functions on `X(ℂ)`,
  identified with functions on places), other groups `0`. Computed: the exactness, `H^*_c`,
  `H^*(X̄_K)`, the Weil–Arakelov groups and their dimensions.
* `CH^0(X̄_K)_ℝ = ℝ` is not formalized; only `dim H^0(X̄_K, ℝ(0)) = 1` is.
* Cohomology groups only, as in rounds 54–56.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace WeilRH.Arakelov

open NumberField NumberField.InfinitePlace NumberField.Units Module
open NumberField.Units.dirichletUnitTheorem
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

namespace TwistZero

/-- The regulator `H^0(X_K, ℝ(0)) = ℝ → H^0_D = ℝ^{InfinitePlace K}`: the diagonal (constants). -/
noncomputable def diag : ℝ →ₗ[ℝ] (InfinitePlace K → ℝ) := LinearMap.pi fun _ => LinearMap.id

theorem diag_injective : Function.Injective (diag K) := by
  intro a b h
  simpa [diag] using congr_fun h w₀

/-- `H^1_c(X_K, ℝ(0))`: the cokernel of the diagonal. -/
abbrev Coker : Type _ := (InfinitePlace K → ℝ) ⧸ LinearMap.range (diag K)

/-- **The `n = 0` Deligne datum of `X_K`** (FM §3.1). `H^0 = ℝ`, `H^0_D = ℝ^{InfinitePlace K}`,
regulator the diagonal, `H^1_c = ℝ^{places}/ℝ`; all other groups vanish. -/
noncomputable def zeroDatum :
    DeligneDatum ℝ (fun i => degSub ℝ 0 i) (fun i => degSub (InfinitePlace K → ℝ) 0 i)
      (fun i => degSub (Coker K) 1 i) where
  reg i := degMap (diag K) 0 0 i i id
  toMot _ := 0
  conn i := degMap (LinearMap.range (diag K)).mkQ 0 1 i (i + 1) (fun h => by omega)
  exact_toMot i := by
    rw [LinearMap.range_zero]
    symm
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply diag_injective K
    simpa using congrArg Subtype.val hx
  exact_reg i := by
    ext y
    by_cases hi : i = 0
    · subst hi
      constructor
      · rintro ⟨x, rfl⟩
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        simp only [degMap_apply, ZeroMemClass.coe_zero, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact ⟨x, rfl⟩
      · intro hy
        have hy' : (y : InfinitePlace K → ℝ) ∈ LinearMap.range (diag K) := by
          have := congrArg Subtype.val hy
          simpa [Submodule.Quotient.mk_eq_zero] using this
        obtain ⟨x, hx⟩ := hy'
        exact ⟨⟨x, mem_degSub_self 0 x⟩, Subtype.ext hx⟩
    · have : (y : InfinitePlace K → ℝ) = 0 := eq_zero_of_mem_degSub hi y.2
      have hy0 : y = 0 := Subtype.ext this
      subst hy0
      simp only [Submodule.zero_mem]
  exact_conn i := by
    rw [LinearMap.ker_zero, LinearMap.range_eq_top]
    intro z
    by_cases hi : i = 0
    · subst hi
      obtain ⟨f, hf⟩ := (LinearMap.range (diag K)).mkQ_surjective (z : Coker K)
      exact ⟨⟨f, mem_degSub_self 0 f⟩, Subtype.ext hf⟩
    · have hz : (z : Coker K) = 0 := eq_zero_of_mem_degSub (by omega) z.2
      exact ⟨0, Subtype.ext (by simp [hz])⟩

/-- `dim H^1_c(X_K, ℝ(0)) = #places - 1 = r₁ + r₂ - 1`. -/
theorem finrank_Hc_one :
    finrank ℝ (degSub (Coker K) 1 1) = Fintype.card (InfinitePlace K) - 1 := by
  rw [LinearEquiv.finrank_eq ((LinearEquiv.ofEq _ _ (degSub_self (Coker K) 1)).trans
    Submodule.topEquiv)]
  have h : finrank ℝ (Coker K) + 1 = Fintype.card (InfinitePlace K) := by
    have h0 := (LinearMap.range (diag K)).finrank_quotient_add_finrank
    rwa [LinearMap.finrank_range_of_inj (diag_injective K), finrank_self,
      finrank_fintype_fun_eq_card] at h0
  omega

/-- **FM §3.2 at `n = 0` for `X̄_K`.** `τ_{<0} RΓ_D = 0`, the adjunction and the retraction are
zero, and `RΓ(X̄_K, ℝ(0))` is the fibre of `RΓ(X_K, ℝ(0)) → 0`, i.e. `H^i(X̄_K, ℝ(0)) = H^i(X_K, ℝ(0))`.
-/
noncomputable def compactZero :
    CompactifiedDatum ℝ (fun i => degSub ℝ 0 i) (fun i => degSub (InfinitePlace K → ℝ) 0 i)
      (fun i => degSub (Coker K) 1 i) (fun _ => PUnit) (fun i => degSub ℝ 0 i) where
  toDeligneDatum := zeroDatum K
  n := 0
  adj _ := 0
  ret _ := 0
  ret_adj _ := Subsingleton.elim _ _
  adj_bijective i hi := by
    have : Subsingleton (degSub (InfinitePlace K → ℝ) 0 i) :=
      degSub_subsingleton _ (by omega)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩
  trunc_trivial _ _ := inferInstance
  toMotBar _ := LinearMap.id
  connBar _ := 0
  exact_toMotBar i := by rw [LinearMap.range_id, LinearMap.zero_comp, LinearMap.ker_zero]
  exact_regBar i := Subsingleton.elim _ _
  exact_connBar i := by rw [LinearMap.range_zero, LinearMap.ker_id]

/-- The retraction at `n = 0` is the zero map. -/
theorem compactZero_ret (i : ℤ) : (compactZero K).ret i = 0 := rfl

/-- **The truncation is nontrivial**: `H^0_D(X_K/ℝ, ℝ(0)) = ℝ^{InfinitePlace K} ≠ 0`, but
`τ_{<0}` kills it, so the adjunction `H^0(τ_{<0} RΓ_D) → H^0_D` is not surjective (in contrast with
round 56's `compactOne_ret`, the identity). -/
theorem compactZero_adj_not_surjective : ¬ Function.Surjective ((compactZero K).adj 0) := by
  intro h
  obtain ⟨_, hx⟩ := h ⟨Pi.single w₀ 1, mem_degSub_self 0 _⟩
  have := congr_fun (congrArg Subtype.val hx) w₀
  simp [compactZero] at this

/-! ## Weil–Arakelov groups at `n = 0` -/

/-- `H^i(X̄_K, ℝ(0))` as a family of types. -/
abbrev hBar0 : ℤ → Type := fun i => degSub ℝ 0 i

/-- **FM (2) at `n = 0`.** `H^i_ar(X̄_K, ℝ̃(0)) = H^i(X̄_K, ℝ(0)) ⊕ H^{i-1}(X̄_K, ℝ(0))`. -/
abbrev harZero (i : ℤ) := WeilArakelov.Har hBar0 i

theorem finrank_hBar0_zero : finrank ℝ (hBar0 0) = 1 := by
  rw [LinearEquiv.finrank_eq ((LinearEquiv.ofEq _ _ (degSub_self ℝ 0)).trans Submodule.topEquiv),
    finrank_self]

theorem finrank_hBar0_of_ne {i : ℤ} (h : i ≠ 0) : finrank ℝ (hBar0 i) = 0 := by
  have := degSub_subsingleton ℝ h
  exact finrank_zero_of_subsingleton

theorem harZero_subsingleton {i : ℤ} (h0 : i ≠ 0) (h1 : i ≠ 1) : Subsingleton (harZero i) := by
  have := degSub_subsingleton ℝ h0
  have := degSub_subsingleton ℝ (show i - 1 ≠ 0 by omega)
  exact instSubsingletonProd

theorem finrank_harZero_zero : finrank ℝ (harZero 0) = 1 := by
  rw [finrank_prod, finrank_hBar0_zero, finrank_hBar0_of_ne (by norm_num)]

theorem finrank_harZero_one : finrank ℝ (harZero 1) = 1 := by
  rw [finrank_prod, finrank_hBar0_of_ne (by norm_num),
    LinearEquiv.finrank_eq (castEquiv ℝ hBar0 (show (1 : ℤ) - 1 = 0 by norm_num)),
    finrank_hBar0_zero]

/-- **The shape of FM Prop. 4.14 (i) at `n = 0`**: `H^i_ar(X̄_K, ℝ̃(0))` vanishes outside
`{2n, 2n+1} = {0, 1}` and is one-dimensional there. -/
theorem prop414_zero_shape :
    (∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (harZero i)) ∧
      finrank ℝ (harZero 0) = 1 ∧ finrank ℝ (harZero 1) = 1 :=
  ⟨fun _ h0 h1 => harZero_subsingleton h0 h1, finrank_harZero_zero, finrank_harZero_one⟩

/-- **FM Prop. 4.14 (iii) at `n = 0` for `X̄_K`**: `ord_{s=0} ζ(X̄_K, s) = -1
= -dim H^0_ar(X̄_K, ℝ̃(0)) = -dim H^0(X̄_K, ℝ(0))`. Uses only Hecke's simple poles. -/
theorem fm414_zero {C : DedekindContinuation K} (P : C.SimplePoles) :
    meromorphicOrderAt (zetaFMCont K C) 0 = (-(finrank ℝ (harZero 0) : ℤ) : ℤ) ∧
    meromorphicOrderAt (zetaFMCont K C) 0 = (-(finrank ℝ (hBar0 0) : ℤ) : ℤ) := by
  rw [ZetaOrder.meromorphicOrderAt_zetaFMCont_zero P, finrank_harZero_zero, finrank_hBar0_zero]
  simp

end TwistZero

end WeilRH.Arakelov
