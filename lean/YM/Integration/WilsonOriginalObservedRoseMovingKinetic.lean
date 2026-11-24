import YM.Integration.WilsonOriginalTwoFlatRoseMerClock
import YM.Integration.WilsonOriginalObservedRosePublicGross
/-! The actual original kinetic clock at the moving Rose stop, purchased uniformly before the two regulators on the elected physical run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseMovingKinetic
open Function Filter Finset Lattice RG RG.Supply Org PhysicalNext.Repeat Legato
open Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth QuadraticLocal.Sunrise.Aviary
open AllOrder.Transit AllOrder.Transit.WheelP
open WilsonOlderFreshGraphAward WilsonThermometerDeclaredSeeds
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe
open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{T:Campaign R}
  {W:Campaign.Pillars R T}{a:Axis}{simple:G.Simple}{ε:ℝ}

open Pert.Asymptotics WilsonReportingAbsoluteInletForecastBooks WilsonOlderFreshSoftSocketKinetic
open WilsonSeparatedPrefixKineticGeometry
local notation "V" => R.family.path.levels
local notation "g" => regulatorRun R.family

open WilsonInvariantActionPosition
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "α" => R.family.S.a
local notation "σ" => R.family.S.scale


open WilsonOriginalTwoFlatRoseMerClock (Charged)
open WilsonOriginalObservedRoseVanePurse (ages)

theorem original (color:G.ColorIndex)(funded:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(Q target L:ℕ)(enough:7+target+2≤Q):
    ∀ᶠv:ℕ in Filter.atTop,∀N per K:ℕ,v≤K→K≤N→σ K-σ v≤L*Real.log (H v)→
      Charged R N per v K Q target 7:=by
  obtain ⟨⟨room⟩,school⟩:=WilsonOriginalCensusPhysicalAttendance.original funded
  let ask:=WilsonOriginalCensusFundedAttendance.quote (Q+3) 0 ages
  have hz:Q+1≤Burn.horizon ask.vac:=by
    have cash:=ask.load.expense
    have depth:=ask.load.qfit
    change Q+3≤ask.order at depth
    omega
  obtain ⟨_,dates⟩:=WilsonOriginalTwoFlatRoseMerClock.original color funded paths room ask.vac Q target 7 L hz enough
  filter_upwards [dates,school ask.vac ask.school ask.deep] with v paid seated
  intro N per K vk kn span
  obtain ⟨_,_,sale⟩:=paid N (vk.trans kn)
  obtain ⟨day⟩:=WilsonOriginalCensusAttendanceStation.choose_day seated (vk.trans kn)
  apply (sale ask.school day).2 per v K le_rfl vk kn
  have high:0<H v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have pos:0<α v/α K:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have time:Real.log (α v/α K)=σ K-σ v:=by
    rw [Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne']
    simp only [Schedule.scale,Real.log_inv]
    ring
  apply (Real.log_le_log_iff pos (pow_pos high _)).mp
  simpa only [time,Real.log_pow] using span

end YM.Integration.WilsonOriginalObservedRoseMovingKinetic
end
