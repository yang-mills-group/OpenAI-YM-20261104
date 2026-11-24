import YM.Integration.WilsonOriginalObservedRoseBornChiralUnary
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! The genuine one-point values on an original filed leg, with its
unmarked history and its proper fitted and stable contributions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralProper
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Filter Function Matrix Lattice RG Laurent
open Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power Embroider Precision Exterior Fountain
open Soil Gauge Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedCoveredSeats WilsonIndependentMatchedFittedSeat
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open scoped Topology BigOperators Classical
open WilsonIndependentMatchedRosterLane (chargeBelow)
open WilsonIndependentMatchedProxyIncome (tariff cost)
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U:Credit}

def submitted (X:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  cruises X.ax X.tx X.N h X.ceilC X.m (WilsonIndependentNotebookCubicCut.raw X 1 φ y o)

def atGrade (P:Era G ℝ)(q:ℕ)(ω:Fin 0→YForest G):ℝ:=P.2 q 0 ω

def stableFee (X:CutsP H T p v E W K U)(C:Credit)(φ:Rarity D)(B y:ℝ):ℝ:=
  chargeBelow φ 0 h 1 y ((C.buy X.Age*X.fuel)*(paceT X.ax.S X.m X.ceilC)^(1/4:ℝ)) B

def fittedFee (X:CutsP H T p v E W K U)(φ:Rarity D)(B y:ℝ):ℝ:=
  chargeBelow φ 0 h 1 y ((tariff H T p e 0 0 E W U).buy X.Age*cost e (dose X 1)) B

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(φ:Rarity D)(B y:ℝ)(o:CellR),On h X.pt →
    Amplitude φ B → ∀q ≤ e,∀ω:Fin 0→YForest G,
    let A:=atGrade (submitted X φ y o) q ω
    let K₀:=atGrade (receiving X 1 φ y o 0) q ω
    A-K₀=atGrade (seat X 1 φ y o 0) q ω ∧ ‖A-K₀‖ ≤ stableFee X C φ B y ∧ ‖K₀‖ ≤ fittedFee X φ B y:=by
  obtain ⟨C,spent⟩:=WilsonOriginalObservedRoseBornChiralUnary.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X φ B y o live test q hq ω A K₀
  obtain ⟨same,stable,fit⟩:=spent X φ B y o live test
  have booked:A=atGrade (seat X 1 φ y o 0) q ω+K₀:=congrArg (fun f:Era G ℝ=>f.2 q 0 ω) same
  have eq:=sub_eq_iff_eq_add.mpr booked
  refine ⟨eq,?_,?_⟩
  · rw [eq]
    exact WilsonIndependentMatchedCoverJoined.unit stable q hq ω
  · exact WilsonIndependentMatchedCoverJoined.unit fit q hq ω

end YM.Integration.WilsonOriginalObservedRoseBornChiralProper
end
