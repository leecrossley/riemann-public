import Mathlib
import WeilRH.DeligneDegreeOne

/-!
# Cohomology of the Arakelov compactification and Weil–Arakelov groups of `X̄_K` (round 56)

Round 56 of `lean/ROADMAP-arakelov.md`, on the Flach–Morin path (decision D8): FM §3.2 and the
degree-one Weil–Arakelov cohomology of `X̄_K` (step E4). Source: Flach–Morin, *Deninger's
conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020), checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:

* §3.2 (p. 523): the Kähler metric gives a canonical morphism
  `RΓ_D(X/ℝ, ℝ(n)) → τ_{<2n} RΓ_D(X/ℝ, ℝ(n))`, a retract of the adjunction map
  `τ_{<2n} RΓ_D → RΓ_D`; `RΓ(X̄, ℝ(n))` is the mapping fibre of the composite
  `RΓ(X, ℝ(n)) → RΓ_D → τ_{<2n} RΓ_D`, giving the exact triangle
  `RΓ(X̄, ℝ(n)) → RΓ(X, ℝ(n)) → τ_{<2n} RΓ_D(X/ℝ, ℝ(n)) →`.
* §3.3, formula (2) (p. 524): `RΓ_ar(X̄, ℝ̃(n)) := RΓ(X̄, ℝ(n)) ⊕ RΓ(X̄, ℝ(n))[-1]`.
* Prop. 4.14 (p. 534), assuming Conj. 4.1, for `X̄` projective regular of pure dimension `d`:
  (i) `H^i_ar(X̄, ℂ̃(n))` is finite-dimensional and vanishes for `i ≠ 2n, 2n+1`;
  its proof (p. 535) gives `H^{2n}_ar ≅ H^{2n+1}_ar ≅ CH^n(X̄)_ℂ`, and (iii)
  `ord_{s=n} ζ(X̄, s) = -dim CH^n(X̄)_ℂ`.

## Main results

* `CompactifiedDatum`: an interface on cohomology groups for FM §3.2, extending `DeligneDatum` by
  the truncation `TDel i` (`= H^i(τ_{<2n} RΓ_D)`), the adjunction `adj : TDel → Del` and the Kähler
  retraction `ret : Del → TDel` with `ret ∘ adj = id`, `adj` bijective in degrees `< 2n` and
  `TDel` zero in degrees `≥ 2n`, and the long exact sequence of the triangle
  `H^i(X̄) → H^i(X) → H^i(τ_{<2n} RΓ_D) → H^{i+1}(X̄)` whose middle map is `ret ∘ reg`.
* `compactOne K`: the instance for `X̄_K` and `n = 1`, built from round 55's `degreeOne K`. Since
  `H^i_D(X_K/ℝ, ℝ(1)) = 0` for `i ≥ 2`, the truncation `τ_{<2}` changes nothing and the retraction is
  the identity, so `H^i(X̄_K, ℝ(1)) = H^i_c(X_K, ℝ(1))`. `compactOne_Hbar_one`:
  `H¹(X̄_K, ℝ(1)) = 0`; `compactOne_Hbar_two : H²(X̄_K, ℝ(1)) ≃ ℝ`.
* **E4, the Weil–Arakelov groups.** `harBar K i := Har (Hbar) i = H^i(X̄_K) ⊕ H^{i-1}(X̄_K)`:
  `harBar_subsingleton` (zero for `i ∉ {2, 3}`), `finrank_harBar_two`, `finrank_harBar_three`
  (both `1`). `prop414_shape` packages these: **the shape of FM Prop. 4.14 (i) holds for `X̄_K`,
  `n = 1`**, with `2n = 2`, `2n + 1 = 3`.
* For contrast, the non-compactified groups `harOpen K i := H^i(X_K) ⊕ H^{i-1}(X_K)`:
  `finrank_harOpen_one = finrank_harOpen_two = rank K = r₁ + r₂ - 1`, in degrees `1, 2` rather than
  `2, 3` (`finrank_unitsR`).

## Comparison with FM Prop. 4.14 / the `BT_n` hypothesis (finding)

For `X̄_K`, `n = 1`, `d = 1`: the compactified Weil–Arakelov cohomology is `ℝ` in degrees `2` and
`3` and zero elsewhere (`prop414_shape`). This agrees with Prop. 4.14 (i) and with
`dim H^{2n}_ar = dim CH^1(X̄_K)_ℝ = 1 = -ord_{s=1} ζ̂_K(s)` (the simple pole at `s = 1`; round 50's
`DedekindContinuation.SimplePoles.xi_one_ne_zero` gives `ξ_K(1) ≠ 0` with `ξ_K = s(s-1)Λ_K`). The
order of the pole is *not* stated in Lean as an `analyticOrderAt`/meromorphic-order equation here,
and the identification `H²(X̄_K, ℝ(1)) ≅ CH^1(X̄_K)_ℝ` (the degree map, round 48's
`chowDegree`) is not formalized. The non-compactified groups `H^i_ar(X_K, ℝ̃(1))` are
`(r₁ + r₂ - 1)`-dimensional in degrees `1, 2`: Prop. 4.14 does not apply to `(Spec 𝒪_K, ∅)` (it is
not "projective regular" in FM's Notation 2.2), so this is not a counterexample, but it shows that
the compactification (here: the cokernel of the regulator) is what moves the groups into degrees
`2n, 2n+1`.

## Fidelity

* Cohomology groups only, not complexes; FM's fibre and retraction are recorded through the long
  exact sequence and the identities `ret ∘ adj = id`.
* The instance inherits round 55's modelled groups (`H¹ = Λ_K ⊗ ℝ`, `H¹_D = ℝ^{InfinitePlace K}`,
  others `0`); given those, `τ_{<2} RΓ_D = RΓ_D` and `ret = adj = id` are forced, and everything
  else is computed. The Kähler metric plays no role in this case because `X_K(ℂ)` is finite.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace WeilRH.Arakelov

open NumberField NumberField.InfinitePlace NumberField.Units Module

/-! ## The compactified datum (FM §3.2) -/

/-- **FM §3.2 (p. 523), interface on cohomology.** A Deligne datum together with the truncation
`TDel i = H^i(τ_{<2n} RΓ_D)`, its adjunction map `adj` and the Kähler retraction `ret`
(`ret ∘ adj = id`), and the long exact sequence of the triangle
`RΓ(X̄, ℝ(n)) → RΓ(X, ℝ(n)) → τ_{<2n} RΓ_D →` whose middle map is `ret ∘ reg`. -/
structure CompactifiedDatum (R : Type*) [CommRing R] (Mot Del Hc TDel Hbar : ℤ → Type*)
    [∀ i, AddCommGroup (Mot i)] [∀ i, Module R (Mot i)]
    [∀ i, AddCommGroup (Del i)] [∀ i, Module R (Del i)]
    [∀ i, AddCommGroup (Hc i)] [∀ i, Module R (Hc i)]
    [∀ i, AddCommGroup (TDel i)] [∀ i, Module R (TDel i)]
    [∀ i, AddCommGroup (Hbar i)] [∀ i, Module R (Hbar i)]
    extends DeligneDatum R Mot Del Hc where
  /-- The twist `n`. -/
  n : ℤ
  /-- The adjunction map `τ_{<2n} RΓ_D → RΓ_D` on cohomology. -/
  adj : ∀ i, TDel i →ₗ[R] Del i
  /-- The Kähler retraction `RΓ_D → τ_{<2n} RΓ_D` on cohomology. -/
  ret : ∀ i, Del i →ₗ[R] TDel i
  ret_adj : ∀ i, (ret i).comp (adj i) = LinearMap.id
  /-- The truncation does not change cohomology below degree `2n`. -/
  adj_bijective : ∀ i, i < 2 * n → Function.Bijective (adj i)
  /-- The truncation kills cohomology in degrees `≥ 2n`. -/
  trunc_trivial : ∀ i, 2 * n ≤ i → Subsingleton (TDel i)
  /-- `H^i(X̄, ℝ(n)) → H^i(X, ℝ(n))`. -/
  toMotBar : ∀ i, Hbar i →ₗ[R] Mot i
  /-- The connecting map `H^i(τ_{<2n} RΓ_D) → H^{i+1}(X̄, ℝ(n))`. -/
  connBar : ∀ i, TDel i →ₗ[R] Hbar (i + 1)
  exact_toMotBar : ∀ i, LinearMap.range (toMotBar i) = LinearMap.ker ((ret i).comp (reg i))
  exact_regBar : ∀ i, LinearMap.range ((ret i).comp (reg i)) = LinearMap.ker (connBar i)
  exact_connBar : ∀ i, LinearMap.range (connBar i) = LinearMap.ker (toMotBar (i + 1))

/-! ## The instance for `X̄_K`, `n = 1` -/

theorem degSub_subsingleton (M : Type*) [AddCommGroup M] [Module ℝ M] {k i : ℤ} (h : i ≠ k) :
    Subsingleton (degSub M k i) :=
  ⟨fun a b => Subtype.ext ((eq_zero_of_mem_degSub h a.2).trans (eq_zero_of_mem_degSub h b.2).symm)⟩

variable (K : Type*) [Field K] [NumberField K]

/-- **FM §3.2 for `X̄_K`, `n = 1`.** Built from round 55's `degreeOne K`. `H^i_D(X_K/ℝ, ℝ(1))`
vanishes for `i ≥ 2`, so `τ_{<2} RΓ_D = RΓ_D`, the adjunction and the retraction are the identity,
and `RΓ(X̄_K, ℝ(1))` is the fibre of the regulator: `H^i(X̄_K, ℝ(1)) = H^i_c`. -/
noncomputable def compactOne :
    CompactifiedDatum ℝ (fun i => degSub (unitsR K) 1 i) (fun i => degSub (InfinitePlace K → ℝ) 1 i)
      (fun i => degSub ℝ 2 i) (fun i => degSub (InfinitePlace K → ℝ) 1 i)
      (fun i => degSub ℝ 2 i) where
  toDeligneDatum := degreeOne K
  n := 1
  adj _ := LinearMap.id
  ret _ := LinearMap.id
  ret_adj _ := rfl
  adj_bijective _ _ := Function.bijective_id
  trunc_trivial i hi := degSub_subsingleton _ (by omega)
  toMotBar i := (degreeOne K).toMot i
  connBar i := (degreeOne K).conn i
  exact_toMotBar i := by rw [LinearMap.id_comp]; exact (degreeOne K).exact_toMot i
  exact_regBar i := by rw [LinearMap.id_comp]; exact (degreeOne K).exact_reg i
  exact_connBar i := (degreeOne K).exact_conn i

/-- The Kähler retraction of `X̄_K` (`n = 1`) is the identity: nothing is truncated. -/
theorem compactOne_ret (i : ℤ) : (compactOne K).ret i = LinearMap.id := rfl

/-- `H¹(X̄_K, ℝ(1)) = 0`. -/
theorem compactOne_Hbar_one : Subsingleton (degSub ℝ 2 1) := degSub_subsingleton ℝ (by norm_num)

/-- `H²(X̄_K, ℝ(1)) ≅ ℝ`, the cokernel of the regulator. -/
noncomputable def compactOne_Hbar_two : degSub ℝ 2 2 ≃ₗ[ℝ] ℝ := degreeOne_Hc_two

/-- In degree `2` the long exact sequence ends with the surjection `H¹_D → H²(X̄_K, ℝ(1))`, which
is `∑_w` (the connecting map is nonzero). -/
theorem compactOne_connBar_ne_zero : (compactOne K).connBar 1 ≠ 0 := degreeOne_conn_ne_zero K

/-! ## E4: Weil–Arakelov groups of `X̄_K` (`n = 1`) -/

/-- The cohomology `H^i(X̄_K, ℝ(1))` as a family of types. -/
abbrev hBar : ℤ → Type := fun i => degSub ℝ 2 i

/-- **FM (2) for `X̄_K`, `n = 1`.** `H^i_ar(X̄_K, ℝ̃(1)) = H^i(X̄_K) ⊕ H^{i-1}(X̄_K)`. -/
abbrev harBar (i : ℤ) := WeilArakelov.Har hBar i

/-- `H^i_ar(X̄_K, ℝ̃(1)) = 0` for `i ∉ {2, 3}`. -/
theorem harBar_subsingleton {i : ℤ} (h2 : i ≠ 2) (h3 : i ≠ 3) : Subsingleton (harBar i) := by
  have := degSub_subsingleton ℝ h2
  have := degSub_subsingleton ℝ (show i - 1 ≠ 2 by omega)
  exact instSubsingletonProd

theorem finrank_hBar_two : finrank ℝ (hBar 2) = 1 := by
  rw [LinearEquiv.finrank_eq compactOne_Hbar_two, finrank_self]

theorem finrank_hBar_of_ne {i : ℤ} (h : i ≠ 2) : finrank ℝ (hBar i) = 0 := by
  have := degSub_subsingleton ℝ h
  exact finrank_zero_of_subsingleton

/-- `dim H²_ar(X̄_K, ℝ̃(1)) = 1`. -/
theorem finrank_harBar_two : finrank ℝ (harBar 2) = 1 := by
  rw [finrank_prod, finrank_hBar_two, finrank_hBar_of_ne (by norm_num)]

/-- `dim H³_ar(X̄_K, ℝ̃(1)) = 1`. -/
theorem finrank_harBar_three : finrank ℝ (harBar 3) = 1 := by
  rw [finrank_prod, finrank_hBar_of_ne (by norm_num),
    LinearEquiv.finrank_eq (castEquiv ℝ hBar (show (3 : ℤ) - 1 = 2 by norm_num)), finrank_hBar_two]

/-- **The shape of FM Prop. 4.14 (i) for `X̄_K`, `n = 1`.** The Weil–Arakelov cohomology
`H^i_ar(X̄_K, ℝ̃(1))` vanishes outside `{2n, 2n+1} = {2, 3}` and is one-dimensional in those two
degrees (`= -ord_{s=1} ζ̂_K`; the pole order is not stated in Lean here). -/
theorem prop414_shape :
    (∀ i : ℤ, i ≠ 2 → i ≠ 3 → Subsingleton (harBar i)) ∧
      finrank ℝ (harBar 2) = 1 ∧ finrank ℝ (harBar 3) = 1 :=
  ⟨fun _ h2 h3 => harBar_subsingleton h2 h3, finrank_harBar_two, finrank_harBar_three⟩

/-! ## Contrast: the non-compactified groups -/

instance : Module.Finite ℝ (unitsR K) := Module.Finite.of_basis (basisR K)

/-- `dim (𝒪_K^× ⊗ ℝ) = rank K = r₁ + r₂ - 1` (Dirichlet). -/
theorem finrank_unitsR : finrank ℝ (unitsR K) = rank K := by
  rw [finrank_eq_card_basis (basisR K), Fintype.card_fin]

/-- `H^i(X_K, ℝ(1))` as a family of types. -/
abbrev hOpen : ℤ → Type _ := fun i => degSub (unitsR K) 1 i

/-- `H^i_ar(X_K, ℝ̃(1)) = H^i(X_K) ⊕ H^{i-1}(X_K)` for the non-compactified `(Spec 𝒪_K, ∅)`. -/
abbrev harOpen (i : ℤ) := WeilArakelov.Har (hOpen K) i

theorem finrank_hOpen_one : finrank ℝ (hOpen K 1) = rank K := by
  rw [LinearEquiv.finrank_eq ((LinearEquiv.ofEq _ _ (degSub_self (unitsR K) 1)).trans
    Submodule.topEquiv), finrank_unitsR]

theorem finrank_hOpen_of_ne {i : ℤ} (h : i ≠ 1) : finrank ℝ (hOpen K i) = 0 := by
  have := degSub_subsingleton (unitsR K) h
  exact finrank_zero_of_subsingleton

/-- Non-compactified: `dim H¹_ar(X_K, ℝ̃(1)) = r₁ + r₂ - 1`. -/
theorem finrank_harOpen_one : finrank ℝ (harOpen K 1) = rank K := by
  rw [finrank_prod, finrank_hOpen_one, finrank_hOpen_of_ne K (by norm_num), add_zero]

/-- Non-compactified: `dim H²_ar(X_K, ℝ̃(1)) = r₁ + r₂ - 1`. -/
theorem finrank_harOpen_two : finrank ℝ (harOpen K 2) = rank K := by
  rw [finrank_prod, finrank_hOpen_of_ne K (by norm_num),
    LinearEquiv.finrank_eq (castEquiv ℝ (hOpen K) (show (2 : ℤ) - 1 = 1 by norm_num)),
    finrank_hOpen_one, zero_add]

end WeilRH.Arakelov
