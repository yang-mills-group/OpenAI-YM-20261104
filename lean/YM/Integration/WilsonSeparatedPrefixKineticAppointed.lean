import YM.Integration.WilsonSeparatedPrefixKineticOptics
import YM.Integration.WilsonOriginalCensusAttendanceVacuum

/-! The finite-order clock change belongs to the already chosen marked semester.
Its own layout, genealogy and received prior serve every subsequent physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticAppointed
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

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)(vac q A:ℕ)(enough:q+1 ≤ Burn.horizon vac):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃σ:ℝ,0<σ ∧ σ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) σ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),
        Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
        ∀per b K,m ≤ b→b ≤ K→K ≤ N→span R A b K→
          |g N per K-g N per b*value q (kinetic V R.metals.O N K b) (g N per b)| ≤ (g N per b)^(q+1):=by
  let seller:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have fund:FundedMarkedCoverRows.prices seller R.kit:=paid.billsPaid.1
  obtain ⟨P,dates⟩:=WilsonSeparatedPrefixKineticForecast.original R u simple seller fund paths vac q enough (by norm_num:0<(1:ℝ))
  obtain ⟨b₀,charts⟩:=eventually_atTop.mp (WilsonSeparatedPrefixKineticOptics.window R simple seller fund q vac A (by omega))
  refine ⟨P,?_⟩
  filter_upwards [dates,eventually_ge_atTop b₀] with m atM bm N mN
  obtain ⟨Z,gross,issued⟩:=atM N mN
  refine ⟨Z,gross,?_⟩
  intro school day
  obtain ⟨clock,real⟩:=issued (roots s R simple) (tab s R simple) room.ticket day.π day.Γ day.path
  refine ⟨clock,?_⟩
  intro per b K mb bK KN admissible
  apply charts b (bm.trans mb) K N per bK KN admissible
  intro i bi iK
  have bet:=(real per (day.Ψ per) (day.seen per).1 i (mb.trans bi) (iK.trans_le KN)).2.1
  simpa only [one_mul] using bet

end YM.Integration.WilsonSeparatedPrefixKineticAppointed
end
