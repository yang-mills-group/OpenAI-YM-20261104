import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskLayer
import YM.Integration.WilsonVacuumPreResetPeriodField

/-! The original covered packet has a single numbered absolutely summable
display. Its signed seats partition that display on every configuration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice RG Wilson PhysicalNext PhysicalNext.Repeat Extra.Iteration
open AnalyticBridge VerifiedReset Collection Quotes IterationFour.Vacuum
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonLimitConstruction Comparison.Density Comparison.Density.Render
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side}

theorem mask_amount_sites (P:Payload G n) (B:BudgetPoint) {A:ℝ} (invoice:P.Invoice B A)
    (U:Config G n) :
    ∑x:Site n,∑s:Signed,maskedSeat P B.threshold (Song.splay n (s,x)) U=P.amount B U := by
  let f (i:ℕ):=masked B.threshold (P.labels i).support (P.action i) U
  let base:=Pane.pale n G
  let lift (i:ℕ):=Payload.coding.symm (Sum.inr i)
  have summable:Summable (fun i=>(P.attach 1 base).regularOccurrence B i U):=
    (Activities.ESeries (Payload.payment 1 invoice (Pane.whey n G B))).summable U
  have taken:=summable.comp_injective (show Function.Injective lift from Payload.coding.symm.injective.comp Sum.inr_injective)
  have same (i) : (P.attach 1 base).regularOccurrence B (lift i) U=f i := by
    simp [f,base,lift,Activities.regularOccurrence,Payload.attach]
  have keep:Summable f:=taken.congr same
  let e:=numbering (Cycle n)
  have total:Summable (fun i:Cycle n=>f (e.symm i)):=keep.comp_injective e.symm.injective
  calc
    _=∑v:Seat n,maskedSeat P B.threshold v U:=spring_mask_seats (fun v=>maskedSeat P B.threshold v U)
    _=∑'v:Seat n,∑'i:ℕ,f (e.symm (v,i)):=by rw [tsum_fintype];rfl
    _=∑'k:Cycle n,f (e.symm k):=total.tsum_prod.symm
    _=P.amount B U:=e.symm.tsum_eq f

theorem mask_packet_sites (B:BudgetPoint) (σ C:ℝ) (a:PrismA G) {D:ℝ}
    (invoice:(FundedCorrectedPeriod.piece n (Song.headline B) σ C a).packet.Invoice (Song.headline B) D)
    (U:Config G n) :
    ∑x:Site n,maskedPrismAt a B σ C B.threshold x U=
      (FundedCorrectedPeriod.piece n (Song.headline B) σ C a).packet.amount B U :=
  mask_amount_sites _ (Song.headline B) invoice U

end YM.Integration.OriginalMarkedRunAction
