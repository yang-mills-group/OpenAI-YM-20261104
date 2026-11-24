import YM.Integration.WilsonIndependentConditionedGramSpatialCourse

/-! The actual before-regulator reporting page admits the entire reflected
compact test at every sufficiently fine K corner, on its physical ruler. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedOptics
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonIndependentConditionedGramSpatialHost (date)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem original (simple:G.Simple){n:ℕ}(live:0<n){cap:ℝ}(cp:0<cap):
    ∀ᶠr in trail,∀{m f K U p:ℕ}{ε:ℝ},m=date R simple r →
    WilsonIndependentConditionedGramSpatialCourse.Page R r m f K n U p ε →
      4*2*(a K/r) < cap:=by
  have hot:=Station.hat_rate R.family.path.levels simple
  have cool:Tendsto (thermal R) atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hot)
  have melt:Tendsto (fun f=> (8:ℝ)*(thermal R f)^(2*n)) atTop (𝓝 0):=by
    simpa [zero_pow (by omega : 2*n≠0)] using (cool.pow (2*n)).const_mul 8
  obtain ⟨floor,fit⟩:=eventually_atTop.mp (melt.eventually_lt_const cp)
  filter_upwards [(WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop floor]
    with r grown
  intro m f K U p ε name page
  have bill:=fit f ((name ▸ grown).trans page.before)
  have size:=div_le_div_of_nonneg_left (R.family.S.a_pos K).le (R.family.S.a_pos m) page.covers
  linarith [size.trans page.upper]

end YM.Integration.WilsonIndependentConditionedLocatedOptics
end
