import YM.Integration.WilsonIndependentFittedHomeReserve
import YM.Integration.WilsonIndependentMovingFittedCash

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedCapital
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

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C V:Credit,∀(X:CutsP H T p v E W K U)(s:ℕ)(a:ℝ)(live:X.vesselsC.anchor ≤ s)(older:s ≤ X.m)
      (q:ℕ)(_cap:q ≤ e),
      receipt X s q (dose X a) ≤ (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
        (C.buy (window X s live older).Age*((Real.exp (span X X.i))^h*V.buy X.Age*(|a| * X.fuel))):=by
  obtain ⟨C,V,sold⟩:=WilsonIndependentFittedStoppedWage.original H T p v E W K U
  exact ⟨C,V,fun X s a live older q cap=>WilsonIndependentFittedHomeReserve.reserve X s q (dose X a) _
    (sold X s a 1 live older q cap)⟩

theorem posted (X:CutsP H T p v E W K U)(s q:ℕ)(δ a fee:ℝ)(C V:Credit)
    (live:X.vesselsC.anchor ≤ s)(older:s ≤ X.m)(positive:0<δ)(amplitude:0<a)
    (mesh:span X X.i= -Real.log δ)(realized:X.fuel=a*fee)
    (earned:receipt X s q (dose X a⁻¹) ≤ (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
      (C.buy (window X s live older).Age*((Real.exp (span X X.i))^h*V.buy X.Age*(|a⁻¹| * X.fuel)))):
    receipt X s q (dose X a⁻¹) ≤ (Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
      (C.buy (window X s live older).Age*(δ^(-(h:ℝ))*V.buy X.Age*fee)):=by
  have g:(Real.exp (span X X.i))^h=δ^(-(h:ℝ)):=by
    rw [mesh,Real.exp_neg,Real.exp_log positive,Real.rpow_neg positive.le,Real.rpow_natCast,inv_pow]
  simpa only [g,realized,abs_of_pos (inv_pos.mpr amplitude),←mul_assoc,inv_mul_cancel₀ amplitude.ne',one_mul] using earned

end YM.Integration.WilsonIndependentMovingFittedCapital
