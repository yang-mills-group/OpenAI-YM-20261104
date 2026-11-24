import YM.Integration.WilsonIndependentMatchedRosterLane

/-! Each slot is the actual full stable displacement or a genuinely
registered coarse basis column on the common marked Wilson schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterSlots
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedCutBudget WilsonIndependentMatchedFittedSeat

open WilsonIndependentMatchedMixBudget WilsonIndependentMatchedCoverReception

open WilsonIndependentMatchedProxyIncome (tariff cost)
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open WilsonIndependentMatchedCoverPairBudget (Bought)
open WilsonIndependentMatchedPivotSeat (axis ticket)

open WilsonIndependentMatchedRosterLane (Lane)

def degree (flag:Bool)(k h:ℕ):ℕ:=if flag then k else h
def count (flag:Bool):ℕ:=if flag then 1 else 0
def entry (flag:Bool)(X:CutsP H T p v E W K U)(a:ℝ)(c:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR):ℕ→Era G ℝ:=
  if flag then seat X a φ y o else printed X.vesselsC (sectionSeal T p) φ c X.m X.N y o

def wallet (flag:Bool)(X:CutsP H T p v E W K U)(c:Verse F)(A:ℝ)(u b:ℕ):ℝ:=
  if flag then A else (tariff H T p e u b E W U).buy X.Age*cost e c

lemma source (flag:Bool)(X:CutsP H T p v E W K U)(a:ℝ)(c:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ A B:ℝ)(paid:Bought X a δ A)(test:Amplitude φ B)(u b:ℕ)(room:u+b ≤ u₀):
    Lane X.vesselsC (degree flag k h) h X.m X.i X.N u b φ y o δ ((count flag:ℝ)/4)
      (wallet flag X c A u b) B (entry flag X a c φ y o):=by
  cases flag
  · simpa only [degree,count,wallet,entry,Bool.false_eq_true,if_false,Nat.cast_zero,zero_div] using
      WilsonIndependentMatchedRosterLane.filed X φ c y o δ B test u b
  · simpa only [degree,count,wallet,entry,if_true,Nat.cast_one] using
      WilsonIndependentMatchedRosterLane.stable X a φ y o δ A B paid test u b room

lemma money (flag:Bool)(X:CutsP H T p v E W K U)(c:Verse F){A:ℝ}(hA:0 ≤ A)(u b:ℕ):
    0 ≤ wallet flag X c A u b:=by
  cases flag
  · exact mul_nonneg (zero_le_one.trans ((tariff H T p e u b E W U).purchase X.windowC.warm)) (WilsonIndependentMatchedProxyIncome.nn c)
  · exact hA

end YM.Integration.WilsonIndependentMatchedRosterSlots
