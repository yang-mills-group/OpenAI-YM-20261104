import YM.Integration.WilsonIndependentMovingFittedCapital
import YM.Integration.WilsonIndependentMovingRosterMarginLedger

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedEpoch
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentFittedStoppedWage (numerical)
open WilsonIndependentFittedPivotCash (gross)
open WilsonIndependentFittedMixedCash (embed bill)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentEvenPassport (count old)
open WilsonIndependentExactPlate (Requests)
open RegulatorIR RegulatorIR.Ledger
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

open WilsonIndependentFittedHomeReserve (receipt)
open WilsonIndependentFittedStoppedWage (window)
open WilsonOriginalPublicPlantedStableCredit (span)

open WilsonCoeffUV.Mer
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMovingRosterMarginLedger (source_age)

def debit (F:Labels.Frame G h)(q:ℕ)(δ fee:ℝ):ℝ:=(Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*δ^(-(h:ℝ))*fee

lemma space (S:Schedule)(t N:ℕ):S.scale N-S.scale t= -Real.log (paceT S t N):=by
  unfold Schedule.scale paceT
  rw [Real.log_inv,Real.log_inv,Real.log_div (S.a_pos _).ne' (S.a_pos _).ne']
  ring

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃A:Credit,∀(R:Realm G (e+1) E)(X:CutsP H T p v E W K U)(s N q:ℕ)(a fee:ℝ),
      X.vesselsC=R → R.anchor ≤ s → s ≤ X.m → X.N=N → X.N=X.ceilC → q ≤ e →
      0<a → X.fuel=a*fee →
      receipt X s q (dose X a⁻¹) ≤ debit F q (paceT R.draws.S X.m N) fee*A.buy (epoch R s N):=by
  obtain ⟨C,V,sold⟩:=WilsonIndependentMovingFittedCapital.original H T p v E W K U
  refine ⟨C.prodC V,?_⟩
  intro R X s N q a fee same live older ended ceil cap amp salary
  have joined:X.m+X.i=N:=ceil.symm.trans ended
  have last:X.m ≤ N:=(Nat.le_add_right _ _).trans joined.le
  have active:X.vesselsC.anchor ≤ s:=by rw [same];exact live
  let δ:=paceT R.draws.S X.m N
  have positive:0<δ:=div_pos (R.draws.S.a_pos _) (R.draws.S.a_pos _)
  have mesh:span X X.i= -Real.log δ:=by rw [span,same,joined];exact space _ _ _
  have measured:=WilsonIndependentMovingFittedCapital.posted X s q δ a fee C V active older positive amp mesh salary
    (sold X s a⁻¹ active older q cap)
  let w:=window X s active older
  have price:w.Age ≤ epoch R s N:=by
    change X.vesselsC.y s+(X.vesselsC.draws.S.scale (s+(X.m-s))-X.vesselsC.draws.S.scale s)+((X.m-s:ℕ):ℝ) ≤ _
    rw [Nat.add_sub_of_le older,same]
    have bound:Compar R.draws.S R.y s X.m ≤ epoch R s X.m:=
      (WilsonSeparatedPrefixMovingCalendar.window R s s X.m live le_rfl older).2.2.1
    have later:epoch R s X.m ≤ epoch R s N:=by unfold WilsonSeparatedPrefixMovingCalendar.epoch;linarith only [scales R.draws.S last]
    exact bound.trans later
  have atX:=source_age R s N live X same older ended ceil
  have charges:=mul_le_mul (C.elder w.warm price) (V.elder atX.1 atX.2)
    (zero_le_one.trans (V.purchase atX.1)) (zero_le_one.trans (C.purchase (w.warm.trans price)))
  have nonneg:0 ≤ fee:=by
    have nn:=X.hf
    rw [salary] at nn
    exact nonneg_of_mul_nonneg_right nn amp
  rw [Credit.products]
  apply measured.trans
  calc
    _=debit F q δ fee*(C.buy w.Age*V.buy X.Age):=by unfold debit;ring
    _ ≤ _:=mul_le_mul_of_nonneg_left charges (by unfold debit;positivity)

end YM.Integration.WilsonIndependentMovingFittedEpoch
