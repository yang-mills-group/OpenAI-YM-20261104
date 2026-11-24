import YM.UVExt.SubBound
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lambent
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Splay
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hem

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay
open RG Wilson Lattice Tree Pressure ConnectedActivityE6 Coat Raw Mask Pulse Itinerary Poll Pond Gaussian MeasureTheory Measure
open Filter Set Function Metric Push.AbsoluteSums Matter
open scoped Topology BigOperators Classical ENNReal

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (X:Coat T F) (R:Rep G f) (t:ℝ) (Ñ:Precision.ChartRatio G) (l : Finset ℕ) (d:ℕ) (W:ℝ) (p:Molecule S)
variable {μ cst:ℝ} {L:Side} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {o:Target.Order G W}
open Finset

variable (hk:X.width=o.K)
    (I:Set ℝ) (hI:IsOpen I) (hd:I⊆Ioi 0)

variable (admitReal: ∀ r∈I,Nonempty (allow X R W (μ:=μ) (cst:=cst) (Q:=Q) (L:=L) (o:=o) r))
local notation "zone" => (Complex.re⁻¹' I)

def electric (z:ℂ) :=
  if (standsIn X R d p) then subtotal (Matter.planted X p) R t Ñ l d W p z
  else 0 -- need taggedL before: caller does average

def feeL (S:StepData c f) (G:Gauge) := Itinerary.density S.patch.L*Fintype.card G.ColorIndex
def pricing (S:StepData c f) (G:Gauge) (b:ℕ):ℝ := 1+2*((feeL S G:ℝ)*Animals.ballCost b)
lemma pricing_pos {b} : 0<pricing S G b := by unfold pricing; positivity

namespace Shape
variable (H:Cash W X.x μ L Q o cst T R)
include H
lemma lens : ((slice X R Q.halo p).card:ℝ) ≤ ((feeL S G:ℝ) * (Animals.ballCost X.B:ℝ))*H.shapeW p := by
 let Y:= H.unionP p; let A:=univ.filter fun z:Tubular f G=> Census.along S z∈Y
 have hp : slice X R Q.halo p ⊆ A := fun i hi=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 (Census.along S i) (by simp only [separation_self]; omega)⟩
 have he:= Census.withType G.ColorIndex (Census.perch S) Y
 change (univ.filter (fun i:Bond f × G.ColorIndex=> Shell.atEdge S i.1∈ Y)).card ≤ Y.card * (feeL S G) at he
 have hv : ((slice X R Q.halo p).card:ℝ) ≤ (Y.card:ℝ)*(feeL S G:ℝ):= by exact_mod_cast (Finset.card_le_card hp |>.trans he)
 apply hv.trans ((mul_le_mul_of_nonneg_right (Blaze.Flux.spaces H p) (Nat.cast_nonneg _)).trans (le_of_eq ?_)); ring

lemma brand (hT:troupe T R Q.halo X.B p) (i:Head S) (hi : i∈p) : (markTax X i:ℝ) ≤ (1+(feeL S G:ℝ)*(Animals.ballCost X.B:ℝ))*coverNumber X.B (H.supportP i) := by
  rcases i with A|j
  · let q:=H.supportP (Sum.inl A)
    have hb : 10*X.B+1≤ Q.halo*X.B := by have := Q.buys; have hb:=H.laws.data.room.sight.1; change 100 ≤ X.B at hb; nlinarith
    have hn : A.dome (10*X.B+1) ⊆ q := Lattice.Corona.halo_mono hb (Finset.Subset.refl _)
    have hp : X.pens A ⊆ (univ.filter fun i:Bond f=> Shell.atEdge S i∈q) := fun i hi=> mem_filter.mpr ⟨mem_univ _, hn (Coat.lives_in i A (mem_filter.mp (mem_filter.mp hi).1).2)⟩
    have hf := Finset.card_le_card hp |>.trans ((Census.perch S q).trans (Nat.mul_le_mul_right _ (Blaze.brood q X.B)))
    dsimp only [markTax,seedPower]; unfold feeL
    push_cast
    apply (le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hf) (Nat.cast_nonneg _))) _
    push_cast; dsimp [q,Itinerary.density] at *; push_cast
    nlinarith only [show 0≤(coverNumber X.B (H.supportP (Sum.inl A)) :ℝ) from Nat.cast_nonneg _]
  have hg:= Blaze.Silica.Utopia.lengthP (H:=H) p hT (Sum.inr j) hi
  simp only [markTax,Nat.cast_one]
  exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (by exact_mod_cast hg)

lemma pays_geometry (hT:troupe T R Q.halo X.B p) : (fees X R Q.halo p:ℝ) ≤ pricing S G X.B * H.shapeW p := by
  have hs : ∑ i∈p, (coverNumber X.B (H.supportP i):ℝ) ≤ H.shapeW p := by
    apply sum_le_sum; intro i hi
    apply le_add_of_nonneg_right; rcases i with i|i
    · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
    exact Nat.cast_nonneg _
  unfold fees pricing; push_cast
  have hh:= Finset.sum_le_sum (brand X R W p H hT); rw [←Finset.mul_sum] at hh
  nlinarith [lens X R W p H, hh, mul_nonneg ((Nat.cast_nonneg (feeL S G)) : (0:ℝ) ≤ _) (Nat.cast_nonneg (Animals.ballCost X.B))]
end Shape
end YM.UVExt.EnergyRay
