import YM.Integration.WilsonIndependentFittedExteriorRung
import YM.Integration.WilsonIndependentMatchedRosterSlots

/-! Every retained tensor of a moved stable source at its own reporter.
The cofunded moisture credit is chosen before its date, physical
coefficient vector and cell. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterLaneSalary
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverPairBudget (Bought)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u₀ e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U),X.N=X.ceilC → ∀a fee:ℝ,0 < a → X.fuel=a*fee →
      Bought X a⁻¹ (paceT X.ax.S X.m X.N) (C.buy X.Age*fee):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X top a fee positive fuel i before j degree r u moment
  have base:=(((paid X).2.2 j degree i before r).slice zero_le_one moment).μ a⁻¹
  have spacing:Real.exp (-(X.vesselsC.draws.S.scale X.ceilC-X.vesselsC.draws.S.scale (X.m+i))/4)=
      (paceT X.ax.S X.m X.N/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ):=by
    rw [←top]
    unfold paceT
    rw [WilsonIndependentFittedExteriorRung.mesh]
    exact WilsonIndependentFittedExteriorRung.gain X.ax.S (X.m+i) X.N
  rw [spacing,fuel,abs_of_pos (inv_pos.mpr positive)] at base
  convert base using 1
  · rfl
  · field_simp [positive.ne']

end YM.Integration.WilsonIndependentMovingRosterLaneSalary

