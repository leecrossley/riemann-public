/-
Copyright (c) 2026 Taylor Dupuy. All rights reserved.
Released under Apache 2.0 license.
-/
import WeilRH.NLines
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Field-valued points of a product (`prop:N-lines`)

For schemes `X` and `Y` over a field `k`, the `K`-points of `X ×ₖ Y` are pairs of `K`-points.
This supplies the geometric multiplicativity of point counts used in `latex/notes.tex`,
`prop:N-lines` (i), where `X = E` and `Y = ℙ¹`.

The point definition models the `fieldValuedPoints` interface used by AxiomMath/Weil in
`Weil/Defs/AlgebraicGeometry/EtaleCohomology/Trace/FieldValuedPointCount.lean` (defined upstream
in Stacks). It is stated locally because that project uses different Lean/Mathlib versions.
Mathlib supplies the `#K + 1` count for the abstract projectivization `ℙ K (K²)` and a concrete
family of finite-field extensions with `#Kₙ = (#k)^n` for `n > 0`. Identifying those points
with scheme `ℙ¹(Kₙ)` and convergence remain explicit inputs to the analytic bridge.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped LinearAlgebra.Projectivization

namespace WeilRH.NLinesGeometry

universe u

variable {k : Type u} [Field k]

/-- The morphism `Spec K → Spec k` associated with an extension `K/k`. -/
noncomputable def extensionMap (K : Type u) [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- Morphisms `Spec K → X` over `Spec k`. -/
def KPoints {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : Type u :=
  {p : Spec (CommRingCat.of K) ⟶ X // p ≫ f = extensionMap K}

/-- The functor of points sends a scheme pullback over `Spec k` to a product of point sets. -/
noncomputable def pointsPullbackEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] :
    KPoints (pullback.fst f g ≫ f) K ≃ KPoints f K × KPoints g K where
  toFun p :=
    (⟨p.1 ≫ pullback.fst f g, by simpa only [Category.assoc] using p.2⟩,
      ⟨p.1 ≫ pullback.snd f g, by
        calc
          (p.1 ≫ pullback.snd f g) ≫ g =
              p.1 ≫ (pullback.snd f g ≫ g) := by rw [Category.assoc]
          _ = p.1 ≫ (pullback.fst f g ≫ f) := by rw [← pullback.condition]
          _ = extensionMap K := p.2⟩)
  invFun xy :=
    ⟨pullback.lift xy.1.1 xy.2.1 (xy.1.2.trans xy.2.2.symm),
      by
        rw [← Category.assoc, pullback.lift_fst]
        exact xy.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  right_inv xy := by
    apply Prod.ext
    · apply Subtype.ext
      exact pullback.lift_fst _ _ _
    · apply Subtype.ext
      exact pullback.lift_snd _ _ _

/-- Cardinality of the field-valued point set; agrees with finite cardinality when finite. -/
noncomputable def pointCount {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] : ℕ := Nat.card (KPoints f K)

/-- Geometric point counts multiply under the product over the base field. -/
theorem pointCount_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] :
    pointCount (pullback.fst f g ≫ f) K = pointCount f K * pointCount g K := by
  unfold pointCount
  rw [Nat.card_congr (pointsPullbackEquiv f g K), Nat.card_prod]

/-- The abstract projective line over a finite field has `#K + 1` points. This is Mathlib's
cardinality theorem for a two-dimensional projectivization. -/
theorem projectiveLine_card (K : Type u) [Field K] [Finite K] :
    Nat.card (ℙ K (Fin 2 → K)) = Nat.card K + 1 := by
  exact Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)

/-- A scheme whose `K`-points are identified with the abstract projective line has the expected
count. The identification is a separate geometric obligation for a chosen model of `ℙ¹`. -/
theorem pointCount_projectiveLine_of_equiv {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) (K : Type u) [Field K] [Algebra k K] [Finite K]
    (e : KPoints g K ≃ ℙ K (Fin 2 → K)) :
    pointCount g K = Nat.card K + 1 := by
  rw [pointCount, Nat.card_congr e, projectiveLine_card]

/-- The complex-valued sequence of counts over a chosen family of field extensions. -/
noncomputable def countSequence {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (K : ℕ → Type u) [∀ n, Field (K n)] [∀ n, Algebra k (K n)] : ℕ → ℂ :=
  fun n => pointCount f (K n)

/-- `prop:N-lines` (i): the geometric product count and the projective-line count in positive
degrees imply the analytic zeta product formula, provided the two defining series converge.
The degree-zero count is arbitrary because its series term vanishes. -/
theorem zetaOfCounts_product_of_geometry {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (K : ℕ → Type u) [∀ n, Field (K n)] [∀ n, Algebra k (K n)]
    (q : ℕ) (hq : 0 < (q : ℝ))
    (hP : ∀ n, 0 < n → pointCount g (K n) = q ^ n + 1)
    {s : ℂ}
    (h1 : Summable fun n : ℕ => countSequence f K n * NLines.qpow q (-s) ^ n / n)
    (h2 : Summable fun n : ℕ =>
      countSequence f K n * NLines.qpow q (-(s - 1)) ^ n / n) :
    NLines.zetaOfCounts q (countSequence (pullback.fst f g ≫ f) K) s =
      NLines.zetaOfCounts q (countSequence f K) s *
        NLines.zetaOfCounts q (countSequence f K) (s - 1) := by
  apply NLines.zetaOfCounts_product_pos hq
  · intro n hn
    simp only [countSequence]
    rw [pointCount_pullback, hP n hn]
    norm_cast
    ring
  · exact h1
  · exact h2

/-- The `E × ℙ¹` product formula from a scheme realization of the abstract projective line and
field extensions of cardinality `qⁿ` for `n > 0`. The remaining assumptions are the
scheme-point equivalences and convergence of the `E` series. -/
theorem zetaOfCounts_product_of_projectiveLine {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (K : ℕ → Type u) [∀ n, Field (K n)] [∀ n, Algebra k (K n)] [∀ n, Finite (K n)]
    (q : ℕ) (hq : 0 < (q : ℝ))
    (e : ∀ n, 0 < n → KPoints g (K n) ≃ ℙ (K n) (Fin 2 → K n))
    (hK : ∀ n, 0 < n → Nat.card (K n) = q ^ n)
    {s : ℂ}
    (h1 : Summable fun n : ℕ => countSequence f K n * NLines.qpow q (-s) ^ n / n)
    (h2 : Summable fun n : ℕ =>
      countSequence f K n * NLines.qpow q (-(s - 1)) ^ n / n) :
    NLines.zetaOfCounts q (countSequence (pullback.fst f g ≫ f) K) s =
      NLines.zetaOfCounts q (countSequence f K) s *
        NLines.zetaOfCounts q (countSequence f K) (s - 1) := by
  apply zetaOfCounts_product_of_geometry f g K q hq
  · intro n hn
    rw [pointCount_projectiveLine_of_equiv g (K n) (e n hn), hK n hn]
  · exact h1
  · exact h2

/-! ### A concrete finite-field extension family -/

variable (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- A family indexed by all natural numbers: degree zero is assigned `F` because it does not
contribute to the zeta series; positive index `n` is Mathlib's degree-`n` extension of `F`. -/
noncomputable def finiteExtensionFamily : ℕ → Type
  | 0 => F
  | n + 1 => FiniteField.Extension F p (n + 1)

noncomputable instance finiteExtensionFamilyField : ∀ n, Field (finiteExtensionFamily F p n)
  | 0 => by change Field F; infer_instance
  | n + 1 => by change Field (FiniteField.Extension F p (n + 1)); infer_instance

noncomputable instance finiteExtensionFamilyAlgebra :
    ∀ n, Algebra F (finiteExtensionFamily F p n)
  | 0 => by change Algebra F F; infer_instance
  | n + 1 => by change Algebra F (FiniteField.Extension F p (n + 1)); infer_instance

noncomputable instance finiteExtensionFamilyFinite : ∀ n, Finite (finiteExtensionFamily F p n)
  | 0 => by change Finite F; infer_instance
  | n + 1 => by change Finite (FiniteField.Extension F p (n + 1)); infer_instance

/-- The family has `(#F)^n` elements in each positive degree. No field has cardinality
`(#F)^0 = 1`, so this assertion cannot hold at degree zero. -/
theorem card_finiteExtensionFamily (n : ℕ) (hn : 0 < n) :
    Nat.card (finiteExtensionFamily F p n) = Nat.card F ^ n := by
  cases n with
  | zero => omega
  | succ n =>
    exact FiniteField.natCard_extension F p (n + 1)

/-- The zeta product formula over the actual degree-`n` finite extensions of `F`, conditional
only on identifying a chosen projective-line scheme's points with abstract projective points
and on convergence of the two series. The term at `n = 0` uses `F` and vanishes in the series. -/
theorem zetaOfCounts_product_finiteExtensions {X Y : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F)) (g : Y ⟶ Spec (CommRingCat.of F))
    (e : ∀ n, 0 < n → KPoints g (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n))
    {s : ℂ}
    (h1 : Summable fun n : ℕ => countSequence f (finiteExtensionFamily F p) n *
      NLines.qpow (Nat.card F) (-s) ^ n / n)
    (h2 : Summable fun n : ℕ => countSequence f (finiteExtensionFamily F p) n *
      NLines.qpow (Nat.card F) (-(s - 1)) ^ n / n) :
    NLines.zetaOfCounts (Nat.card F)
        (countSequence (pullback.fst f g ≫ f) (finiteExtensionFamily F p)) s =
      NLines.zetaOfCounts (Nat.card F) (countSequence f (finiteExtensionFamily F p)) s *
        NLines.zetaOfCounts (Nat.card F) (countSequence f (finiteExtensionFamily F p))
          (s - 1) := by
  apply zetaOfCounts_product_of_projectiveLine f g (finiteExtensionFamily F p)
    (Nat.card F) (by exact_mod_cast (Nat.card_pos (α := F)))
  · exact e
  · exact card_finiteExtensionFamily F p
  · exact h1
  · exact h2

/-- On `Re s > 2`, the zeta function of a scheme product `E ×_F ℙ¹` equals the rational
expression in `prop:N-lines`, once the scheme projective-line points are identified with abstract
projective points and the elliptic Frobenius count is supplied in positive degree. -/
theorem zetaOfCounts_finiteExtensions_eq_zetaX {X Y : Scheme}
    (f : X ⟶ Spec (CommRingCat.of F)) (g : Y ⟶ Spec (CommRingCat.of F))
    (e : ∀ n, 0 < n → KPoints g (finiteExtensionFamily F p n) ≃
      ℙ (finiteExtensionFamily F p n) (Fin 2 → finiteExtensionFamily F p n))
    {α β : ℂ}
    (hα : ‖α‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2))
    (hβ : ‖β‖ = (Nat.card F : ℝ) ^ ((1 : ℝ) / 2))
    (hE : ∀ n, 0 < n → countSequence f (finiteExtensionFamily F p) n =
      (Nat.card F : ℂ) ^ n + 1 - α ^ n - β ^ n)
    {s : ℂ} (hs : 2 < s.re) :
    NLines.zetaOfCounts (Nat.card F)
        (countSequence (pullback.fst f g ≫ f) (finiteExtensionFamily F p)) s =
      NLines.zetaX (Nat.card F) α β s := by
  have hq : 1 < (Nat.card F : ℝ) := by exact_mod_cast (Finite.one_lt_card (α := F))
  apply NLines.zetaOfCounts_eq_zetaX hq hα hβ _ ?_ hs
  intro n hn
  have hprod :
      countSequence (pullback.fst f g ≫ f) (finiteExtensionFamily F p) n =
        countSequence f (finiteExtensionFamily F p) n *
          ((Nat.card F : ℂ) ^ n + 1) := by
    simp only [countSequence]
    rw [pointCount_pullback,
      pointCount_projectiveLine_of_equiv g (finiteExtensionFamily F p n) (e n hn),
      card_finiteExtensionFamily F p n hn]
    norm_cast
  rw [hprod, hE n hn]
  push_cast
  ring

end WeilRH.NLinesGeometry
