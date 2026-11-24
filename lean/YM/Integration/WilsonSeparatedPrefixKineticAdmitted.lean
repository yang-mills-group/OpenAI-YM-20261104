import YM.Integration.WilsonSeparatedPrefixKineticBerth

/-! The measured receiver and trial date may be any two dates on the purchased
optical interval. The full Laurent multiplier uses the original coupling ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticAdmitted
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

include simple in
theorem admissible (A b K:ℕ)(bK:b ≤ K)(size:α b/α K ≤ (H b)^A):WilsonSeparatedPrefixKineticGeometry.span R A b K:=by
  have hp:0<H b:=zero_lt_one.trans ((V).fits.delayed b)
  have bound:=Real.log_le_log (div_pos (R.family.S.a_pos b) (R.family.S.a_pos K)) size
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hp (WilsonReflectedOpticalStock.monotone R simple bK)) (Nat.cast_nonneg A))

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)
    (vac q h A:ℕ)(enough:q+2 ≤ Burn.horizon vac):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃τ:ℝ,0<τ ∧ τ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per b K,m ≤ b→b ≤ K→K ≤ N→α b/α K ≤ (H b)^A→let μ:=kinetic V R.metals.O N K b
       |g N per K-g N per b*value (q+1) μ (g N per b)| ≤ (g N per b)^(q+2) ∧
       |(g N per b/g N per K)^h*value (q+1) (μ^h) (g N per b)-1| ≤ (g N per b)^q ∧
       |(g N per K)⁻¹^h*value (h+(q+1)) (clock V R.metals.O N K b (PowerSeries.X^h)) (g N per b)-1| ≤ (g N per b)^q:=by
  let seller:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have fund:FundedMarkedCoverRows.prices seller R.kit:=paid.billsPaid.1
  obtain ⟨P,schoolOpens⟩:=WilsonSeparatedPrefixKineticAppointed.original u paid paths room vac (q+1) A enough
  obtain ⟨p,analytic⟩:=eventually_atTop.mp (WilsonSeparatedPrefixKineticPole.window R simple seller fund q h A)
  refine ⟨P,?_⟩
  filter_upwards [schoolOpens,eventually_ge_atTop p] with m elect late N mN
  obtain ⟨Z,wages,attend⟩:=elect N mN
  refine ⟨Z,wages,?_⟩;intro school day
  obtain ⟨actual,clocked⟩:=attend school day
  refine ⟨actual,?_⟩;intro per b K mb bK live size μ
  have admitted:=admissible (R:=R) (simple:=simple) A b K bK size
  have raw:=clocked per b K mb bK live admitted
  have poleCost:=analytic b (by omega) K N per bK live admitted raw
  refine ⟨raw,poleCost,?_⟩
  rw [WilsonOlderFreshSoftSocketKinetic.pole _ _ _ _ _ _ bK,WilsonSeparatedPrefixKineticBerth.shifted]
  convert poleCost using 2; rw [div_pow,div_eq_mul_inv,inv_pow]; ring

end YM.Integration.WilsonSeparatedPrefixKineticAdmitted
end
