import YM.Integration.LocalComparisonForcedDecomposition

/-!
Restore product kernel envelopes in the complete original marked density.
All regular, forced and mixed products, the unmarked gas and the actual
exponent remain present.  The inverse price normalization is an algebraic
coordinate change only; it is not a new physical source or vacuum.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}

theorem restoreEnvelope_product_finset {I : Type*} (s : Finset I)
    (cost : V → ℝ) (hcost : ∀ v, 0 < cost v) (F : I → Poly R) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (∏ i ∈ s, F i) =
      ∏ i ∈ s, restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty] using restoreEnvelope_product_one cost hcost
  | @insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi, restoreEnvelope_product_mul cost hcost, ih]

private theorem restore_vacuum (cost : V → ℝ) (hcost : ∀ v, 0 < cost v) (z : ℂ) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (Poly.send R.quiet z) = Poly.send R.quiet z := by
  ext s
  change (envelopeProduct cost s : ℂ) * (Poly.send R.quiet z).part s =
    (Poly.send R.quiet z).part s
  rw [Poly.part_send]
  by_cases hs : s = R.quiet
  · subst s
    simp [envelopeProduct, Census.quiet]
  simp [hs]

variable {G : Gauge} {n : Side} {X : Type*} {P : Rep G n}
    {o : V → Site n} (T : Taste X o P R)
    (cost : V → ℝ) (hcost : ∀ v, 0 < cost v)

include hcost

/-- Each forced alternative is restored on its original support/index. -/
theorem restoreEnvelope_each (x : X) (i : ℕ) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.each i U) =
      (T.leaf x).contents.each i U := by
  let E : Poly R ≃L[ℂ] Poly R :=
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
  change E (Poly.send R.quiet (P.activities.K i U : ℂ) +
    ∑' j, Poly.send (T.menu.marks i j)
      ((envelopeProduct cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U)) =
    Poly.send R.quiet (P.activities.K i U : ℂ) +
      ∑' j, Poly.send (T.menu.marks i j) (T.menu.force x i j U)
  rw [map_add, E.map_tsum]
  congr 1
  · exact restore_vacuum cost hcost _
  exact tsum_congr (fun j => restoreEnvelope_send _ _ _ _)

/-- An admissible forced packet retains every original marked product. -/
theorem restoreEnvelope_packet (x : X) (s : Finset ℕ) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.packet s U) =
      (T.leaf x).contents.packet s U := by
  unfold Bands.packet
  split
  · rw [restoreEnvelope_product_finset s cost hcost]
    exact prod_congr rfl (fun i _ => restoreEnvelope_each T cost hcost x i U)
  exact map_zero _

/-- The entire compulsory-cover gas, including its unmarked part, is
restored exactly; no isolated reciprocal of a gas term is introduced. -/
theorem restoreEnvelope_cluster (x : X) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.cluster U) =
      (T.leaf x).contents.cluster U := by
  unfold Bands.cluster
  rw [ContinuousLinearEquiv.map_tsum]
  exact tsum_congr (fun s => restoreEnvelope_packet T cost hcost x s U)

section Density
variable [Fintype V]

/-- Exact envelope restoration of the full original unnormalized density. -/
theorem restoreEnvelope_density (x : X) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (((priceNormalized (envelopeProduct cost) T).leaf x).density U) =
      (T.leaf x).density U := by
  unfold Deck.density
  rw [map_smul, restoreEnvelope_product_mul cost hcost,
    restoreEnvelope_product_pass cost hcost,
    restoreEnvelope_log T (envelopeProduct cost) (envelopeProduct_positive hcost),
    restoreEnvelope_cluster T cost hcost]

/-- The normalized coordinate of every full-density coefficient is the
original physical coefficient divided by its complete input-envelope product. -/
theorem priceNormalized_density_part (x : X) (U : Config G n) (s : R.Mode) :
    (((priceNormalized (envelopeProduct cost) T).leaf x).density U).part s =
      (envelopeProduct cost s)⁻¹ • ((T.leaf x).density U).part s := by
  have h := congrArg (fun A : Poly R => A.part s) (restoreEnvelope_density T cost hcost x U)
  change (envelopeProduct cost s : ℂ) * _ = _ at h
  rw [Complex.real_smul, Complex.ofReal_inv, ← h, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (envelopeProduct_positive hcost s).ne'), one_mul]

/-- The full physical density retains exactly its relative marker price. -/
theorem density_product_price (w : V → ℝ) (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) ((T.leaf x).density U) =
      Poly.price w (((priceNormalized (envelopeProduct cost) T).leaf x).density U) := by
  rw [← restoreEnvelope_density T cost hcost x U,
    restoreEnvelope_product_price cost w hcost]

/-- Subtracting the actual unmarked density commutes with the same envelope
restoration, so the comparison concerns the full marked residual. -/
theorem density_error_product_price (w : V → ℝ) (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) ((T.leaf x).density U - (P.eval U : ℂ) • 1) =
      Poly.price w (((priceNormalized (envelopeProduct cost) T).leaf x).density U -
        (P.eval U : ℂ) • 1) := by
  have he : restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (((priceNormalized (envelopeProduct cost) T).leaf x).density U - (P.eval U : ℂ) • 1) =
      (T.leaf x).density U - (P.eval U : ℂ) • 1 := by
    rw [map_sub, map_smul, restoreEnvelope_density T cost hcost,
      restoreEnvelope_product_one cost hcost]
  rw [← he, restoreEnvelope_product_price cost w hcost]

end Density

/-- The same exact coordinate change restores the explicit forced-error
numerator used by the scalar integration consumer. -/
theorem restoreEnvelope_forcedClusterError (x : X) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
      (forcedClusterError ((priceNormalized (envelopeProduct cost) T).leaf x) U) =
      forcedClusterError (T.leaf x) U := by
  unfold forcedClusterError
  rw [map_sub, map_smul, restoreEnvelope_cluster T cost hcost,
    restoreEnvelope_product_one cost hcost]

/-- The actual forced numerator has precisely the weighted price of its
announced coordinate normalization, including all mixed envelopes. -/
theorem forcedClusterError_product_price (w : V → ℝ) (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) (forcedClusterError (T.leaf x) U) =
      Poly.price w (forcedClusterError ((priceNormalized (envelopeProduct cost) T).leaf x) U) := by
  rw [← restoreEnvelope_forcedClusterError T cost hcost x U,
    restoreEnvelope_product_price cost w hcost]

end YM.Integration.LocalComparison
