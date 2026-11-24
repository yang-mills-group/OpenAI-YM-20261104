import YM.Integration.WilsonIndependentMatchedRosterSlots
import YM.Integration.WilsonIndependentMatchedCutBudget
/-! Each arm keeps its own section and deposits. A receiver with the same levels and kinetic
ratio hears its full hem and forecast on the original physical dates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalArm
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W V A:Credit}
theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W V A:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W V A)(a:ℝ),
    Bought X a (paceT X.ax.S X.m X.ceilC) (|a| *(C.buy X.Age*X.fuel)):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W V A
  refine ⟨C,?_⟩
  intro X a i hi j hj r t ht
  have row:=(((paid X).2.2 j hj i hi r).slice zero_le_one ht).μ a
  have span:Real.exp (-(X.ax.S.scale X.ceilC-X.ax.S.scale (X.m+i))/4)=
      (paceT X.ax.S X.m X.ceilC/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ):=by
    change _ = (paceT X.ax.S X.m (X.m+X.i)/paceT X.ax.S X.m (X.m+i))^(1/4:ℝ)
    rw [←WilsonIndependentMatchedCoverSum.spacing,←WilsonIndependentMatchedCoverSum.spacing]
    dsimp only [WilsonOriginalPublicPlantedFirstJoinScale.radius]
    rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.exp_pos _)),
      Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
    congr 1
    change -(X.ax.S.scale (X.m+X.i)-X.ax.S.scale (X.m+i))/4=_
    ring
  rw [span] at row
  apply row.more
  apply le_of_eq
  ring

theorem lane {R R':Realm G (e+1) E}{l d m n N b w dim:ℕ}{φ:Rarity dim}{y:ℝ}{o:CellR}
    {δ a B P:ℝ}{f:ℕ→Era G ℝ}(levels:R.draws=R'.draws)(clock:R.paid=R'.paid)
    (hired:Lane R l d m n N b w φ y o δ a B P f):Lane R' l d m n N b w φ y o δ a B P f:=by
  refine ⟨⟨hired.accounts.head,?_,?_,hired.accounts.home⟩,?_,?_⟩
  · intro i hi
    simpa only [levels] using hired.accounts.cash i hi
  · intro i hi
    simpa only [levels] using hired.accounts.empty i hi
  · intro i hi
    simpa only [levels] using hired.billed i hi
  · intro i hi
    simpa only [levels,clock] using hired.pushed i hi
end YM.Integration.WilsonIndependentMatchedPhysicalArm
