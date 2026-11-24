import YM.Integration.WilsonSeparatedPrefixKineticCharge

/-! The measured receiver and trial date may be any two dates on the purchased
optical interval. The full Laurent multiplier uses the original coupling ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticSocket
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

include simple in
theorem window (seller:ℕ→Gear G→ℝ)(sources:FundedMarkedCoverRows.prices seller R.kit)
    (p h target A:ℕ)(enough:h+target+2 ≤ p):
    ∀ᶠ b:ℕ in atTop,∀K N per,b ≤ K→K ≤ N→span R A b K→
    let M:=kinetic V R.metals.O N K b
    let x:=g N per b
    let y:=g N per K
    |y-x*value p M x| ≤ x^(p+1)→
    (y^h)⁻¹*(x^(p+1)*((h:ℝ)+2)*(mass p M)^h+|(x*value p M x)^h-y^h|) ≤ x^target:=by
  obtain ⟨B,B1,geometry⟩:=corridor R simple A
  obtain ⟨C,gross⟩:=WilsonSeparatedPrefixKineticMarket.original R simple seller sources p
  let L:=((p:ℝ)+2)*C.x*B^C.d
  let fee:=(2:ℝ)^h*((h:ℝ)+2)
  filter_upwards [geometry,gross,spend R simple (fee*L^h) (C.d*h),
    spend R simple (2*h*3^h) 0,spend R simple 2 0] with b geo wealth base speed endSale K N per bK live admit M x y actual
  have x0:0<x:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (bK.trans live)))
  have y0:0<y:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  obtain ⟨⟨z1,a1,ap,_⟩,clocks⟩:=geo K N per bK live admit
  let z:=wage R b
  have bound:mass p M ≤ L*z^C.d:=by
    have funds:=(wealth N K bK live).1 b le_rfl bK
    refine (funds.trans (mul_le_mul_of_nonneg_left (C.elder a1 ap) (by positivity))).trans_eq ?_
    dsimp [L,z];unfold Credit.buy;rw [mul_pow];ring
  have payload:fee*(mass p M)^h ≤ x⁻¹:=by
    calc
      _ ≤ fee*(L*z^C.d)^h:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg ..) bound h) (by dsimp [fee];positivity)
      _ = (fee*L^h)*z^(C.d*h):=by rw [mul_pow,pow_mul];ring
      _ ≤ _:=base N per (bK.trans live)
  have twice:2 ≤ x⁻¹:=by simpa only [pow_zero,mul_one] using endSale N per (bK.trans live)
  have small:x ≤ 1:=by
    have cap:=mul_le_mul_of_nonneg_right twice x0.le
    rw [inv_mul_cancel₀ x0.ne'] at cap
    linarith
  have lb:3/4*x ≤ y:=(le_div_iff₀ x0).mp ((clocks K bK le_rfl).1)
  exact WilsonSeparatedPrefixKineticCharge.numerical p h target M x0 small y0
    ((div_le_iff₀ y0).mpr (by linarith)) enough payload
    (by simpa only [pow_zero,mul_one] using speed N per (bK.trans live)) twice actual

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)
    (vac p target maxDebt A:ℕ)(enough:p+1 ≤ Burn.horizon vac)(crop:maxDebt+target+2 ≤ p):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃τ:ℝ,0<τ ∧ τ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per b K,m ≤ b→b ≤ K→K ≤ N→α b/α K ≤ (H b)^A→let μ:=kinetic V R.metals.O N K b
       let x:=g N per b
       let y:=g N per K
       |y-x*value p μ x| ≤ x^(p+1) ∧
       ∀h ≤ maxDebt,(y^h)⁻¹*(x^(p+1)*((h:ℝ)+2)*(mass p μ)^h+|(x*value p μ x)^h-y^h|) ≤ x^target:=by
  let seller:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  have fiscal:FundedMarkedCoverRows.prices seller R.kit:=paid.billsPaid.1
  have analytics:=eventually_all.mpr fun i:Fin (maxDebt+1)=>window (R:=R) (simple:=simple) seller fiscal p i.val target A (by omega)
  obtain ⟨t,priced⟩:=eventually_atTop.mp analytics
  obtain ⟨P,course⟩:=WilsonSeparatedPrefixKineticAppointed.original u paid paths room vac p A enough
  refine ⟨P,?_⟩
  filter_upwards [course,eventually_ge_atTop t] with m schoolOpens late N mN
  obtain ⟨Z,wages,buy⟩:=schoolOpens N mN
  refine ⟨Z,wages,?_⟩;intro school day
  obtain ⟨real,forecast⟩:=buy school day
  refine ⟨real,?_⟩;intro per b K mb bK KN size μ x y
  have enrolled:=WilsonSeparatedPrefixKineticAdmitted.admissible (R:=R) (simple:=simple) A b K bK size
  have due:=forecast per b K mb bK KN enrolled
  refine ⟨due,?_⟩;intro h hh
  exact priced b (late.trans mb) ⟨h,by omega⟩ K N per bK KN enrolled due

end YM.Integration.WilsonSeparatedPrefixKineticSocket
end
