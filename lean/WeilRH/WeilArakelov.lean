import Mathlib

/-!
# Deligne data and Weil–Arakelov cohomology (FM path, step E3)

Round 54 of `lean/ROADMAP-arakelov.md`, on the Flach–Morin path (decision D8). Source:
Flach–Morin, *Deninger's conjectures and Weil–Arakelov cohomology*, Münster J. Math. 13 (2020),
§3.1–3.4, pp. 523–524, checked in the local PDF
`refs/citation-tree/weil-etaile/flach-morin-2020-deninger-conjectures-weil-arakelov.pdf`:

* §3.1 (p. 523): `RΓ_c(X, ℝ(n))` is the mapping fibre of the regulator
  `RΓ(X, ℝ(n)) → RΓ_D(X/ℝ, ℝ(n))`, giving an exact triangle
  `RΓ_c → RΓ → RΓ_D →`; Deligne cohomology is `RΓ_D(X/ℝ, ℝ(n)) := RΓ(G_ℝ, X(ℂ), ℝ(n)_D)`.
* §3.3, formula (2) (p. 524): `RΓ_ar,c(X, ℝ̃(n)) := RΓ_c(X, ℝ(n)) ⊕ RΓ_c(X, ℝ(n))[-1]`.
* §3.4 (p. 524): `∪θ` is "the projection on the first direct summand followed by the inclusion of
  the second direct summand"; it induces the acyclic complex (3), with (4)
  `Ker(∪θ : H^i_ar,c → H^{i+1}_ar,c) ≅ H^{i-1}_c` and (5) `Coker(∪θ) ≅ H^{i+1}_c`.

## Main results

* `DeligneDatum`: an interface for the long exact sequence of FM's fibre triangle (§3.1): graded
  `R`-modules `Mot i` (motivic cohomology `H^i(X, ℝ(n))`), `Del i` (Deligne cohomology
  `H^i_D(X/ℝ, ℝ(n))`), `Hc i` (`H^i_c(X, ℝ(n))`), the regulator `reg i : Mot i → Del i` given as
  data, and maps `Hc i → Mot i`, `Del i → Hc (i+1)` with exactness at every spot.
  `DeligneDatum.idDatum`: a nonzero instance (`Mot = Del = R`, `reg = id`, `Hc = 0`).
* `WeilArakelov.Har H i := H i × H (i-1)` and `WeilArakelov.theta`: the cohomology-level form of
  FM (2) and of `∪θ` (§3.4), `(a, b) ↦ (0, a)`.
* `theta_comp`: `∪θ ∘ ∪θ = 0`; `ker_theta_succ`: `ker (∪θ) = range (∪θ)` in every degree —
  the acyclicity of FM (3).
* `kerThetaEquiv`: `ker(∪θ : Har i → Har (i+1)) ≃ H (i-1)` — FM (4).
* `cokerThetaEquiv`: `Har (i+1) ⧸ range(∪θ) ≃ H (i+1)` — FM (5).
* `regulatorMap K`: the Dirichlet regulator `𝒪_K^× → ℝ^{InfinitePlace K}`,
  `u ↦ (mult w · log w(u))_w`, the degree-one piece of `reg` for `X̄_K` with `n = 1`.
  `sum_regulatorMap`: its image lies in the sum-zero hyperplane; `regulatorMap_eq_zero_iff`: its
  kernel is the torsion subgroup `μ(K)`.

## Not formalized (fidelity)

* Everything here is at the level of **cohomology groups**, not complexes. FM define
  `RΓ_ar,c` as a direct sum of complexes; its cohomology is `H^i_c ⊕ H^{i-1}_c`, which is what
  `Har` encodes, and `∪θ` on cohomology is the map in `theta`.
* `DeligneDatum` is an **interface**: Bloch's cycle complex, Deligne cohomology of `X(ℂ)` and the
  regulator are not constructed (Mathlib has none of them); FM's fibre is recorded only through its
  long exact sequence. The identification `H^1(X̄_K, ℝ(1)) ≅ 𝒪_K^× ⊗ ℝ`,
  `H^1_D(X_K/ℝ, ℝ(1)) ≅ ℝ^{InfinitePlace K}` behind `regulatorMap` is standard but not formalized;
  `regulatorMap` is stated on `𝒪_K^×` itself, without `⊗ ℝ`.
* The compactified version `RΓ(X̄, ℝ(n))` (§3.2, using the Kähler retraction) is not encoded.
-/

namespace WeilRH.Arakelov

section Shift

variable (R : Type*) [CommRing R] (H : ℤ → Type*) [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]

/-- Transport along an equality of degrees (used to identify `H ((i+1)-1)` with `H i`). -/
def castEquiv {i j : ℤ} (h : i = j) : H i ≃ₗ[R] H j := by
  subst h; exact LinearEquiv.refl R (H i)

end Shift

/-! ## The Deligne datum (FM §3.1) -/

/-- **FM §3.1 (p. 523), interface.** The long exact sequence of the fibre triangle
`RΓ_c(X, ℝ(n)) → RΓ(X, ℝ(n)) → RΓ_D(X/ℝ, ℝ(n)) →`: motivic cohomology `Mot`, Deligne cohomology
`Del`, compactly supported cohomology `Hc`, the regulator `reg` (given as data), and exactness at
every term. -/
structure DeligneDatum (R : Type*) [CommRing R] (Mot Del Hc : ℤ → Type*)
    [∀ i, AddCommGroup (Mot i)] [∀ i, Module R (Mot i)]
    [∀ i, AddCommGroup (Del i)] [∀ i, Module R (Del i)]
    [∀ i, AddCommGroup (Hc i)] [∀ i, Module R (Hc i)] where
  /-- The regulator `H^i(X, ℝ(n)) → H^i_D(X/ℝ, ℝ(n))`. -/
  reg : ∀ i, Mot i →ₗ[R] Del i
  /-- `H^i_c → H^i`. -/
  toMot : ∀ i, Hc i →ₗ[R] Mot i
  /-- The connecting map `H^i_D → H^{i+1}_c`. -/
  conn : ∀ i, Del i →ₗ[R] Hc (i + 1)
  exact_toMot : ∀ i, LinearMap.range (toMot i) = LinearMap.ker (reg i)
  exact_reg : ∀ i, LinearMap.range (reg i) = LinearMap.ker (conn i)
  exact_conn : ∀ i, LinearMap.range (conn i) = LinearMap.ker (toMot (i + 1))

namespace DeligneDatum

variable (R : Type*) [CommRing R]

/-- A nonzero instance: `Mot = Del = R` in every degree, `reg = id`, `Hc = 0` (the fibre of an
isomorphism vanishes). -/
def idDatum : DeligneDatum R (fun _ => R) (fun _ => R) (fun _ => PUnit) where
  reg _ := LinearMap.id
  toMot _ := 0
  conn _ := 0
  exact_toMot _ := by rw [LinearMap.range_zero, LinearMap.ker_id]
  exact_reg _ := by rw [LinearMap.range_id, LinearMap.ker_zero]
  exact_conn _ := Subsingleton.elim _ _

/-- `idDatum` is nonzero: its regulator is the identity of `R ≠ 0`. -/
theorem idDatum_reg_ne_zero [Nontrivial R] (i : ℤ) : (idDatum R).reg i ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h 1
  simp [idDatum] at this

end DeligneDatum

/-! ## Weil–Arakelov groups and `∪θ` (FM §3.3–3.4) -/

namespace WeilArakelov

variable (R : Type*) [CommRing R] (H : ℤ → Type*) [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]

/-- **FM (2), on cohomology.** `H^i_ar = H^i ⊕ H^{i-1}`, the cohomology of
`RΓ ⊕ RΓ[-1]`. -/
abbrev Har (i : ℤ) := H i × H (i - 1)

/-- **FM §3.4.** `∪θ : H^i_ar → H^{i+1}_ar`, projection on the first summand followed by the
inclusion of the second: `(a, b) ↦ (0, a)`. -/
def theta (i : ℤ) : Har H i →ₗ[R] Har H (i + 1) :=
  LinearMap.inr R (H (i + 1)) (H (i + 1 - 1)) ∘ₗ
    (castEquiv R H (show i = i + 1 - 1 by omega)).toLinearMap ∘ₗ
      LinearMap.fst R (H i) (H (i - 1))

@[simp] theorem theta_apply (i : ℤ) (x : Har H i) :
    theta R H i x = (0, castEquiv R H (show i = i + 1 - 1 by omega) x.1) := rfl

/-- `∪θ ∘ ∪θ = 0`. -/
theorem theta_comp (i : ℤ) : (theta R H (i + 1)).comp (theta R H i) = 0 := by
  ext x <;> simp

/-- The kernel of `∪θ` is the second summand. -/
theorem ker_theta (i : ℤ) :
    LinearMap.ker (theta R H i) = LinearMap.ker (LinearMap.fst R (H i) (H (i - 1))) := by
  ext ⟨a, b⟩
  simp [Prod.ext_iff]

/-- The image of `∪θ` is the second summand. -/
theorem range_theta (i : ℤ) :
    LinearMap.range (theta R H i) =
      LinearMap.ker (LinearMap.fst R (H (i + 1)) (H (i + 1 - 1))) := by
  ext ⟨c, d⟩
  constructor
  · rintro ⟨x, hx⟩
    rw [theta_apply] at hx
    show c = 0
    exact (congrArg Prod.fst hx).symm
  · intro hc
    have hc' : c = 0 := hc
    refine ⟨((castEquiv R H (show i = i + 1 - 1 by omega)).symm d, 0), ?_⟩
    simp [hc']

/-- **FM (3): the Weil–Arakelov complex is acyclic.** `ker(∪θ) = range(∪θ)` in every degree. -/
theorem ker_theta_succ (i : ℤ) :
    LinearMap.ker (theta R H (i + 1)) = LinearMap.range (theta R H i) := by
  rw [ker_theta, range_theta]

/-- **FM (4).** `ker(∪θ : H^i_ar → H^{i+1}_ar) ≅ H^{i-1}`. -/
def kerThetaEquiv (i : ℤ) : LinearMap.ker (theta R H i) ≃ₗ[R] H (i - 1) where
  toFun x := x.1.2
  invFun b := ⟨(0, b), by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    obtain ⟨⟨a, b⟩, hx⟩ := x
    have ha : a = 0 := by
      rw [LinearMap.mem_ker, theta_apply] at hx
      simpa using congrArg Prod.snd hx
    subst ha
    rfl
  right_inv _ := rfl

/-- **FM (5).** `coker(∪θ : H^i_ar → H^{i+1}_ar) ≅ H^{i+1}`. -/
noncomputable def cokerThetaEquiv (i : ℤ) :
    (Har H (i + 1) ⧸ LinearMap.range (theta R H i)) ≃ₗ[R] H (i + 1) :=
  (Submodule.quotEquivOfEq _ _ (range_theta R H i)).trans
    ((LinearMap.fst R (H (i + 1)) (H (i + 1 - 1))).quotKerEquivOfSurjective
      LinearMap.fst_surjective)

end WeilArakelov

/-! ## The regulator of `X̄_K` in degree one -/

section Regulator

open NumberField NumberField.InfinitePlace NumberField.Units

variable (K : Type*) [Field K]

/-- The Dirichlet regulator `𝒪_K^× → ℝ^{InfinitePlace K}`, `u ↦ (mult w · log w(u))_w`: the
degree-one regulator of `X̄_K` with `n = 1` (FM §3.1), before `⊗ ℝ`. -/
noncomputable def regulatorMap : Additive ((𝓞 K)ˣ) →+ (InfinitePlace K → ℝ) where
  toFun x w := mult w * Real.log (w ↑x.toMul)
  map_zero' := by ext w; simp
  map_add' _ _ := by ext w; simp [Real.log_mul, mul_add]

@[simp] theorem regulatorMap_apply (x : (𝓞 K)ˣ) (w : InfinitePlace K) :
    regulatorMap K (Additive.ofMul x) w = mult w * Real.log (w x) := rfl

variable [NumberField K]

/-- The regulator lands in the sum-zero hyperplane (product formula). -/
theorem sum_regulatorMap (x : (𝓞 K)ˣ) : ∑ w, regulatorMap K (Additive.ofMul x) w = 0 := by
  simpa using sum_mult_mul_log x

/-- The kernel of the regulator is the torsion `μ(K)`. -/
theorem regulatorMap_eq_zero_iff (x : (𝓞 K)ˣ) :
    regulatorMap K (Additive.ofMul x) = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion, funext_iff]
  refine forall_congr' fun w => ?_
  rw [regulatorMap_apply, Pi.zero_apply]
  exact dirichletUnitTheorem.mult_log_place_eq_zero

end Regulator

end WeilRH.Arakelov
