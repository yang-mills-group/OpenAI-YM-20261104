import YM.Integration.WilsonIndependentFittedExteriorRung
import YM.Integration.WilsonIndependentMatchedRosterSlots

/-! Every signed return is priced from its marked birth. The vacuum can have an earlier ultraviolet history. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedMovingSalary
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverPairBudget (Bought)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u₀ e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(a:ℝ),
      Bought X a (paceT X.ax.S X.m X.ceilC) (C.buy X.Age*(|a| * X.fuel)):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X a i before j degree r u moment
  have base:=(((paid X).2.2 j degree i before r).slice zero_le_one moment).μ a
  have spacing:Real.exp (-(X.vesselsC.draws.S.scale X.ceilC-X.vesselsC.draws.S.scale (X.m+i))/4)=
      (paceT X.ax.S X.m X.ceilC/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ):=by
    unfold paceT
    rw [WilsonIndependentFittedExteriorRung.mesh]
    exact WilsonIndependentFittedExteriorRung.gain X.ax.S (X.m+i) X.ceilC
  rw [spacing] at base
  convert base using 1
  · rfl
  · ring

end YM.Integration.WilsonIndependentConditionedMovingSalary
