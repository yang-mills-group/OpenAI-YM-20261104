import YM.Integration.WilsonIndependentMatchedMixBudget

/-! One normalized reporting pivot, funded as a positive, fully continued
peer without charging the size of a fitted complete coefficient array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPivotSeat
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

open WilsonIndependentMatchedReportedProxy WilsonIndependentMatchedProxyIncome

def axis (j:Alma F)(q:ℕ):Verse F:=fun i=>PowerSeries.mk fun l=>if i=j ∧ l=q then 1 else 0

lemma ticket (j:Alma F)(q:ℕ)(hq:q ≤ e):cost e (axis j q)=1:=by
  classical
  have value (i:ℕ)(b:Alma F):‖coeff i (axis j q b)‖=(if b=j then if i=q then (1:ℝ) else 0 else 0):=by
    by_cases a:b=j <;> by_cases d:i=q <;> simp [axis,a,d,PowerSeries.coeff_mk]
  unfold cost
  simp_rw [value]
  simp [Finset.mem_range.mpr (show q<e+1 by omega)]

def film (X:CutsP H T p v E W K U)(j:Alma F)(q:ℕ)(φ:Rarity D)(y:ℝ)(o:CellR):ℕ → Era G ℝ:=
  printed X.vesselsC (sectionSeal T p) φ (axis j q) X.m X.N y o

theorem sponsored (X:CutsP H T p v E W K U)(j:Alma F)(q:ℕ)(hq:q ≤ e)
    (φ:Rarity D)(y:ℝ)(o:CellR)(δ B:ℝ)(test:Amplitude φ B)(u b:ℕ):
    Funds X.vesselsC h h X.m X.i u b φ y o δ 0 ((tariff H T p e u b E W U).buy X.Age) B
      (film X j q φ y o):=by
  have paid:=WilsonIndependentMatchedProxyIncome.original X φ (axis j q) y o δ B test u b
  rw [ticket j q hq,mul_one] at paid
  exact paid

theorem along (X:CutsP H T p v E W K U)(a:ℝ)(j:Alma F)(q:ℕ)(φ ψ:Rarity D)(y:ℝ)(o:CellR):
    Posted X.vesselsC k h X.m X.N X.i (seat X a φ y o) (film X j q ψ y o) ∧
    Posted X.vesselsC h k X.m X.N X.i (film X j q ψ y o) (seat X a φ y o):=
  mixed X (sectionSeal T p) (passport X) a φ ψ (axis j q) y o

end YM.Integration.WilsonIndependentMatchedPivotSeat
