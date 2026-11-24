import YM.Integration.WilsonSeparatedPrefixKineticPole

/-! The registered berth and the same earlier receiver have a uniformly
priced physical change of coupling, including the weight of a Laurent seed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticBerth
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

lemma shifted (p h:ℕ)(A:Cost)(x:ℝ):value (h+p) (PowerSeries.X^h*A) x=x^h*value p A x:=by
  unfold WilsonReportingAbsoluteInletForecastBooks.value
  rw [show h+p+1=h+(p+1) by omega,Finset.sum_range_add,Finset.mul_sum]
  have low:(∑i∈Finset.range h,x^i*PowerSeries.coeff i (PowerSeries.X^h*A))=0:=by
    apply Finset.sum_eq_zero;intro i hi
    rw [PowerSeries.coeff_X_pow_mul',if_neg (Nat.not_le.mpr (Finset.mem_range.mp hi)),mul_zero]
  rw [low,zero_add];apply Finset.sum_congr rfl;intro l _
  rw [PowerSeries.coeff_X_pow_mul',if_pos (by omega),Nat.add_sub_cancel_left,pow_add];ring

include simple in
lemma geometry (slow:WilsonWindowReportingPace.Slow R.kit)(B t:ℕ):∀ᶠ f:ℕ in atTop,
    let K:=berth R t f
    f<K ∧ ∀b,b ≤ f→α b/α f ≤ (H f)^B→span R (B+t+1) b K:=by
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t (by norm_num:0<(1:ℝ))] with f bill
  let K:=berth R t f
  have fp:0<H f:=zero_lt_one.trans ((V).fits.delayed f)
  have upper:=Real.log_le_log (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)) bill.2.2
  rw [WilsonReflectedRelativeDate.ratio,Real.log_mul (pow_pos fp _).ne' (Real.rpow_pos_of_pos fp _).ne',Real.log_pow,Real.log_rpow fp,one_mul] at upper
  have high:=Real.log_le_log fp (WilsonReflectedOpticalStock.monotone R simple bill.1.le)
  refine ⟨bill.1,?_⟩
  intro b _ window
  have near:=Real.log_le_log (div_pos (R.family.S.a_pos b) (R.family.S.a_pos f)) window
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at near
  unfold WilsonSeparatedPrefixKineticGeometry.span;push_cast
  refine le_trans ?_ (mul_le_mul_of_nonneg_left high (by positivity:0 ≤ (B:ℝ)+t+1))
  linarith only [near,upper]

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (vac q h B t:ℕ)(enough:q+2 ≤ Burn.horizon vac):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃τ:ℝ,0<τ ∧ τ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per b f,m ≤ b→b ≤ f→α b/α f ≤ (H f)^B→let K:=berth R t f
       K ≤ N→let μ:=kinetic V R.metals.O N K b
       |g N per K-g N per b*value (q+1) μ (g N per b)| ≤ (g N per b)^(q+2) ∧
       |(g N per b/g N per K)^h*value (q+1) (μ^h) (g N per b)-1| ≤ (g N per b)^q ∧
       |(g N per K)⁻¹^h*value (h+(q+1)) (clock V R.metals.O N K b (PowerSeries.X^h)) (g N per b)-1| ≤ (g N per b)^q:=by
  let seller:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have fund:FundedMarkedCoverRows.prices seller R.kit:=paid.billsPaid.1
  obtain ⟨P,schoolOpens⟩:=WilsonSeparatedPrefixKineticAppointed.original u paid paths room vac (q+1) (B+t+1) enough
  obtain ⟨p,analytic⟩:=eventually_atTop.mp (WilsonSeparatedPrefixKineticPole.window R simple seller fund q h (B+t+1))
  obtain ⟨l,sizes⟩:=eventually_atTop.mp (geometry (R:=R) (simple:=simple) slow B t)
  refine ⟨P,?_⟩
  filter_upwards [schoolOpens,eventually_ge_atTop (max p l)] with m elect late N mN
  obtain ⟨Z,wages,attend⟩:=elect N mN
  refine ⟨Z,wages,?_⟩;intro school day
  obtain ⟨actual,clocked⟩:=attend school day
  refine ⟨actual,?_⟩;intro per b f mb bf near K live μ
  obtain ⟨fK,spanK⟩:=sizes f (by omega)
  have admitted:=spanK b bf near
  have bK:b ≤ K:=bf.trans fK.le
  have raw:=clocked per b K mb bK live admitted
  have poleCost:=analytic b (by omega) K N per bK live admitted raw
  refine ⟨raw,poleCost,?_⟩
  rw [WilsonOlderFreshSoftSocketKinetic.pole _ _ _ _ _ _ bK,shifted]
  convert poleCost using 2; rw [div_pow,div_eq_mul_inv,inv_pow]; ring

end YM.Integration.WilsonSeparatedPrefixKineticBerth
end
