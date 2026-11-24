import YM.Integration.WilsonOlderFreshSoftSocketPaidRose
import YM.Integration.WilsonSeparatedPrefixKineticSocket

/-! One measured vacuum and the terminal comparison at every purchased phase and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketDay
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

open WilsonSeparatedPrefixKineticTruncation

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)
    (vac p target A:ℕ)(enough:p+1≤Burn.horizon vac)(crop:7+target+2≤p):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃τ:ℝ,0<τ ∧ τ⁻¹≤zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per v K,m≤v→v≤K→K≤N→α v/α K≤(H v)^A→
        WilsonOlderFreshSoftSocketPaidRose.Sold R p target N per K v:=by
  obtain ⟨P,calendar⟩:=WilsonSeparatedPrefixKineticSocket.original u paid paths room vac p target 7 A enough crop
  obtain ⟨b,late⟩:=eventually_atTop.mp (WilsonSeparatedPrefixKineticGeometry.spend R simple 1 0)
  have cold {j N per:ℕ}(bj:b≤j)(live:j≤N):g N per j≤1:=by
    have pos:=ActualRunKernelPackets.regulator_pos R N per j live
    have one:1≤(g N per j)⁻¹:=by simpa only [pow_zero,mul_one] using late j bj N per live
    exact (one_le_inv₀ pos).mp one
  refine ⟨P,?_⟩
  filter_upwards [calendar,eventually_ge_atTop b] with m sale after N mN
  obtain ⟨Z,given,dates⟩:=sale N mN
  refine ⟨Z,given,?_⟩
  intro school day
  obtain ⟨exactCoin,tuned⟩:=dates school day
  refine ⟨exactCoin,?_⟩
  intro per v K mv vk live span
  have fiscal:=(tuned per v K mv vk live span).2
  exact WilsonOlderFreshSoftSocketPaidRose.original R p target N per K v live
    (cold (after.trans mv) (vk.trans live)) (cold ((after.trans mv).trans vk) live) (by omega) fiscal

end YM.Integration.WilsonOlderFreshSoftSocketDay
end
