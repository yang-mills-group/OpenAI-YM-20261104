import YM.Integration.WilsonOriginalCensusAttendanceStation
import YM.Integration.WilsonOriginalPrimerCourseTariff

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusAttendanceVacuum
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

theorem legal {vac m N:ℕ}{school:Syl.School vac}
    (day:Day s R simple school m N)(i:ℕ)(lo:m ≤ i)(live:i < N) :
    Legal (Step.tape (Burn.horizon vac+2)) (day.π (i+1)) :=by
  let lesson:=day.lessons i lo live
  rw [lesson.ticket]
  exact Step.PlanV.audited R.rolls (roots s R simple) _ _ _ lesson.entry

/-- The unmarked series and every issued radius are common to all periods,
root choices and test ballots at this cutoff. The measured reset on the
actual attendance path includes every occupied Gaussian forest. -/
theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)(vac:ℕ) :
    ∃price:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N → ∃Z:ℕ → SeriesA G,
      (∀i,m ≤ i → i ≤ N → ∃σ:ℝ,0 < σ ∧ σ⁻¹ ≤ zz (levels R) i ∧
        Issued R N i (Burn.horizon vac) (Z i) σ
          (price.buy (zz (levels R) i)+zz (levels R) i*(levels R).clock.loopCap i)) ∧
      Prescription R (fun i=>bank (Z i)) (coin R N) N m (Burn.horizon vac) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),
        Read R N m (Burn.horizon vac) Z day.π day.Γ ∧
        ∀i,m ≤ i → i < N → Legal (Step.tape (Burn.horizon vac+2)) (day.π (i+1)) :=by
  let salary:ℕ → Gear G → ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  obtain ⟨price,opened⟩:=WilsonOriginalMeasuredOccupiedForest.original R simple salary
    paid.billsPaid.1 paths (Burn.horizon vac)
  refine ⟨price,?_⟩
  filter_upwards [opened] with m ready
  intro N cut
  obtain ⟨Z,fares,reset,courses⟩:=ready N cut
  refine ⟨Z,fares,reset,?_⟩
  intro school day
  exact ⟨courses _ _ day.π day.Γ day.path room.pass.formal,legal day⟩

end YM.Integration.WilsonOriginalCensusAttendanceVacuum
end
