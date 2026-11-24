import YM.Integration.WilsonIndependentConditionedMovingLane
import YM.Integration.WilsonIndependentConditionedMovingSalary
import YM.Integration.WilsonIndependentMovingRosterNormalizedInputs
/-! An actual stable cut or a submitted fitted direction from a separately funded field section, at the same marked birth and on the original N-dated quiet. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedMovingSeat
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterSlots (degree count wallet entry)
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}


open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedReportedProxy (sectionSeal)

def pupil {E':Credit}(R:Realm G (e+1) E')(φ:Rarity D)(c:Verse F)(home birth N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  locale o ((sectionSeal T p).spins R.draws R.paid φ home birth N y c)

theorem original (X:CutsP H T p v E W K U){E':Credit}(R:Realm G (e+1) E')
    (files:X.ax=R.draws)(reset:X.tx=R.paid){home birth N:ℕ}(origin:X.m=home)(atBirth:X.ceilC=birth)(quiet:X.N=N)
    (flag:Bool)(a:ℝ)(c:Verse F)(φ:Rarity D)(y:ℝ)(o:CellR)(A B:ℝ)(test:Amplitude φ B)
    (u b:ℕ)(room:u+b ≤ u₀)(pos:0≤A)(bought:WilsonIndependentMatchedCoverPairBudget.Bought X a
      (paceT X.ax.S X.m X.ceilC) A):
    let paths:=entry flag X a c φ y o
    let amount:=wallet flag X c A u b
    0≤amount ∧ Lane R (degree flag k h) h home (birth-home) N u b φ y o
      (paceT R.draws.S home birth) ((count flag:ℝ)/4) amount B paths ∧
      paths (birth-home)=(if flag then seat X a φ y o X.i else pupil (T:=T) (p:=p) R φ c home birth N y o):=by
  intro paths amount
  have top:X.m+X.i=birth:=atBirth
  have index:birth-home=X.i:=by omega
  refine ⟨WilsonIndependentMatchedRosterSlots.money flag X c pos u b,?_,?_⟩
  · have source:=WilsonIndependentMatchedRosterSlots.source flag X a c φ y o _ A B bought test u b room
    have actual:=WilsonIndependentConditionedMovingLane.on_draws (R':=R) files reset source
    simpa only [←index,quiet,origin,atBirth,files] using actual
  · rw [index]
    cases flag
    · change locale o ((sectionSeal T p).spins X.ax X.tx φ X.m (X.m+X.i) X.N y c)=_
      rw [top,origin,quiet,files,reset]
      rfl
    · rfl

end YM.Integration.WilsonIndependentConditionedMovingSeat
