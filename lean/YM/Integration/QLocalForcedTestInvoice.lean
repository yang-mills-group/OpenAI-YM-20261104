import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.QLocalBarcodeDifference
import YM.Overlay.Pays

/-! A test-uniform physical forced budget gives a complete support-hit
invoice for every original marked entry. Division by products of kernel
costs can be moved exactly into the polydisc radii on the same source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalForcedTestInvoice
open Function Finset Lattice Wilson RG Marker Overlay
open RG3.Script.Picnic LocalComparison LocalComparison.Global MergeProof MergeProof.Accent
open Push.AbsoluteSums Push.GridApprox.Nil
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
  {X : Type*} {o : V → Site n} {P : Rep G n} (p : BudgetPoint) (T : Taste X o P Γ)
  {w : V → ℝ} {d u : ℝ}

/-- Restore the original force functions by moving precisely their mode's
positive envelope product into the original marker radii. -/
def restore (cost : V → ℝ) (hc : ∀ i, 0 < cost i)
    (B : ForcedBudget p (priceNormalized (envelopeProduct cost) T) w d u) :
    ForcedBudget p T (fun i => w i / cost i) d u := by
  let c (q : Γ.Mode) := envelopeProduct cost q
  have pos (q : Γ.Mode) : 0 < c q := Finset.prod_pos (fun i _ => hc i)
  have scale (q : Γ.Mode) : Poly.toll (fun i => w i/cost i) q * c q = Poly.toll w q := by
    change (∏ i ∈ q.val, w i/cost i) * (∏ i ∈ q.val, cost i) = ∏ i ∈ q.val, w i
    rw [Finset.prod_div_distrib]
    exact div_mul_cancel₀ _ (show (∏ i ∈ q.val, cost i) ≠ 0 from (pos q).ne')
  refine ⟨fun k => c (T.menu.marks k.1 k.2) * B.black k,
    fun k => mul_nonneg (pos _).le (B.black_nonnegative k), ?_, ?_⟩
  · intro x i j U
    have h := B.forced x i j U
    change ‖(c (T.menu.marks i j))⁻¹ • T.menu.force x i j U‖ ≤ B.black (i,j) at h
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pos _))] at h
    have hh := mul_le_mul_of_nonneg_left h (pos (T.menu.marks i j)).le
    rwa [← mul_assoc, mul_inv_cancel₀ (pos (T.menu.marks i j)).ne', one_mul] at hh
  · intro v
    convert B.total v using 1
    funext k
    change (if v ∈ (T.menu.marks k.1 k.2).val then Poly.toll (fun i => w i/cost i) _ *
      p.mass (P.activities.forced k.1).support (c (T.menu.marks k.1 k.2)*B.black k) else 0) =
      if v ∈ (T.menu.marks k.1 k.2).val then Poly.toll w _ *
        p.mass (P.activities.forced k.1).support (B.black k) else 0
    split
    · unfold BudgetPoint.mass
      rw [show Poly.toll (fun i => w i/cost i) (T.menu.marks k.1 k.2) *
          (Real.exp _ * (c (T.menu.marks k.1 k.2) * B.black k)) =
          (Poly.toll (fun i => w i/cost i) (T.menu.marks k.1 k.2) * c (T.menu.marks k.1 k.2)) *
          (Real.exp _ * B.black k) from by ring, scale]
      rfl
    · rfl

def entry (k : ℕ × ℕ) (z : X × Config G n) : Poly Γ :=
  Poly.send (T.menu.marks k.1 k.2) (T.menu.force z.1 k.1 k.2 z.2)

variable [Fintype V]

theorem tagged (B : ForcedBudget p T w d u) (hw : ∀ i, 0 < w i)
    (ho : ∀ i j, (T.menu.marks i j).val.Nonempty) :
    Towed w (fun k : ℕ × ℕ => (P.activities.forced k.1).support) (entry T) p.B p.supportExponent
      ((Fintype.card V : ℝ)*(d*u)) := by
  let f (k : ℕ × ℕ) := Poly.toll w (T.menu.marks k.1 k.2) *
    p.mass (P.activities.forced k.1).support (B.black k)
  let b (k : ℕ × ℕ) := Poly.toll w (T.menu.marks k.1 k.2) * B.black k
  have hb k : 0 ≤ b k := mul_nonneg (Poly.worth hw _).le (B.black_nonnegative _)
  have hle k : b k ≤ f k := mul_le_mul_of_nonneg_left
    (p.loMass _ _ (B.black_nonnegative _)) (Poly.worth hw _).le
  have H : SumBudget f ((Fintype.card V : ℝ)*(d*u)) :=
    Overlay.per_system (fun k => (hb k).trans (hle k)) (fun k => ho k.1 k.2) B.total
  refine ⟨b,H.2.1.of_nonneg_of_le hb hle,?_,?_⟩
  · intro x
    apply budget_mono H
    · intro k
      split
      · exact mul_nonneg (hb k) (Real.exp_nonneg _)
      · exact le_rfl
    · intro k
      split
      · exact le_of_eq (by unfold f b BudgetPoint.mass; ring)
      · exact (hb k).trans (hle k)
  · intro k
    exact satin (fun z : X × Config G n => T.menu.force z.1 k.1 k.2 z.2)
      (T.menu.marks k.1 k.2) (B.black k) (B.black_nonnegative k) (fun z => B.forced z.1 k.1 k.2 z.2)

/-- The same finite barcode simultaneously majorizes independently chosen
source tests and configurations. Its fibers are the original marked entries
and its price depends on the number of named markers. -/
theorem barcode (B : ForcedBudget p T w d u) (hw : ∀ i, 0 < w i)
    (ho : ∀ i j, (T.menu.marks i j).val.Nonempty) :
    Towed w Prod.fst (tally (fun k : ℕ × ℕ => MergeProof.barcode P.activities k.1) (entry T))
      p.B p.supportExponent ((Fintype.card V : ℝ)*(d*u)) :=
  towing _ _ (tagged p T B hw ho) hw

end YM.Integration.QLocalForcedTestInvoice
