import YM.Integration.WilsonSeparatedPrefixKineticAdmitted

/-! The measured receiver and trial date may be any two dates on the purchased
optical interval. The full Laurent multiplier uses the original coupling ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticDegree
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

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)
    (vac p target maxDebt A:ℕ)(enough:p+1 ≤ Burn.horizon vac)(crop:maxDebt+target+1 ≤ p):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃τ:ℝ,0<τ ∧ τ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per b K,m ≤ b→b ≤ K→K ≤ N→α b/α K ≤ (H b)^A→let μ:=kinetic V R.metals.O N K b
       |g N per K-g N per b*value p μ (g N per b)| ≤ (g N per b)^(p+1) ∧
       ∀h ≤ maxDebt,|(g N per K)⁻¹^h*value p (clock V R.metals.O N K b (PowerSeries.X^h)) (g N per b)-1| ≤ (g N per b)^target:=by
  let remaining (i:Fin (maxDebt+1)):=p-i.val-1
  have each (i:Fin (maxDebt+1)):=WilsonSeparatedPrefixKineticAdmitted.original u paid paths room vac (remaining i) i.val A
    (by dsimp [remaining];omega)
  choose _ earns using each
  obtain ⟨P,sale⟩:=WilsonSeparatedPrefixKineticAppointed.original u paid paths room vac p A enough
  obtain ⟨t,inverse⟩:=eventually_atTop.mp (spend R simple 1 0)
  refine ⟨P,?_⟩
  filter_upwards [sale,eventually_all.mpr earns,eventually_ge_atTop t] with m schoolGoods all late
  intro N live
  obtain ⟨Z,wages,buy⟩:=schoolGoods N live
  refine ⟨Z,wages,?_⟩;intro school day
  obtain ⟨genuine,clocked⟩:=buy school day
  refine ⟨genuine,?_⟩;intro per b K mb bK KN size μ
  have range:=WilsonSeparatedPrefixKineticAdmitted.admissible (R:=R) (simple:=simple) A b K bK size
  refine ⟨clocked per b K mb bK KN range,?_⟩;intro h included
  let i:Fin (maxDebt+1):=⟨h,by omega⟩
  obtain ⟨_,_,states⟩:=all i N live
  have charged:=((states school day).2 per b K mb bK KN size).2.2
  have degrees:(i:ℕ)+(remaining i+1)=p:=by dsimp [i,remaining];omega
  rw [degrees] at charged
  have pos:0<g N per b:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (bK.trans KN)))
  have le:1 ≤ (g N per b)⁻¹:=by simpa only [pow_zero,mul_one] using inverse b (late.trans mb) N per (bK.trans KN)
  have small:g N per b ≤ 1:=by
    have z:=mul_le_mul_of_nonneg_right le pos.le
    rwa [one_mul,inv_mul_cancel₀ pos.ne'] at z
  exact charged.trans (pow_le_pow_of_le_one pos.le small (by dsimp [remaining,i];omega))

end YM.Integration.WilsonSeparatedPrefixKineticDegree
end
