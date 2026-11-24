import YM.Integration.WilsonSeparatedPrefixKineticSocket
import YM.Integration.WilsonOlderFreshSoftSocketGross
import YM.Integration.WilsonOlderFreshSoftSocketTotal

/-! The before-cutoff kinetic election pays the Laurent factor of every
occupied return on the same Wilson clock. Its second factor is the entire
ordinary field on the independently issued two finite intervals. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseMerClock
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


def Charged (R:Run G)(N per b K p target maxDebt:ℕ):Prop:=
  let μ:=kinetic R.family.path.levels R.metals.O N K b
  let x:=regulatorRun R.family N per b
  let y:=regulatorRun R.family N per K
  ∀h ≤ maxDebt,(y^h)⁻¹*(x^(p+1)*((h:ℝ)+2)*(WilsonReportingAbsoluteInletForecastBooks.mass p μ)^h+
      |(x*value p μ x)^h-y^h|)≤x^target

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room s R simple)
    (vac p target maxDebt A:ℕ)(enough:p+1 ≤ Burn.horizon vac)(crop:maxDebt+target+2 ≤ p):
    ∃P:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m ≤ N→∃Z:ℕ→SeriesA G,
      (∀j,m ≤ j→j ≤ N→∃τ:ℝ,0<τ ∧ τ⁻¹ ≤ zz V j ∧
        Issued R N j (Burn.horizon vac) (Z j) τ (P.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(school:Syl.School vac)(day:Day s R simple school m N),Agrees R N m (Burn.horizon vac) Z day.π day.Γ ∧
      ∀per b K,m ≤ b→b ≤ K→K ≤ N→α b/α K ≤ (H b)^A→
        Charged R N per b K p target maxDebt:=by
  obtain ⟨P,course⟩:=WilsonSeparatedPrefixKineticSocket.original u paid paths room vac p target maxDebt A enough crop
  refine ⟨P,?_⟩
  filter_upwards [course] with m opening
  intro N booked
  obtain ⟨Z,emitted,hearing⟩:=opening N booked
  refine ⟨Z,emitted,?_⟩
  intro school day
  obtain ⟨registered,wallet⟩:=hearing school day
  exact ⟨registered,fun per b K mb bk kn span=>(wallet per b K mb bk kn span).2⟩

open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftSocketRestored (stopped coin)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonCoeffUV.Winding

open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOlderFreshSoftSocketTotal (cost)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark

variable {I:Type}[Fintype I][DecidableEq I](D d:I→ℕ)(p:ℕ)

theorem costed (S:Finset I)(occupied:S.Nonempty)(realm:Realm G (p+1) Credit.leanC)
    (draw:realm.draws=R.family.path.levels)(paid:realm.paid=R.metals.O)
    (dorm:Dormitory realm (WilsonCoeffUV.Wheel.Mark.mass d S) 0 Credit.leanC)
    (N per K c v:ℕ)(first:realm.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank realm c K A)(march:PadRank realm v c B)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:Selection R d S)
    (cells:Digits realm.draws I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(fn:‖f‖≤1)
    (target cap:ℕ)(forecast:Charged R N per v K p target cap)
    (lag:degree R d S (fill R d S q)≤cap):
    cost R d κ pt N per K c v (cast (congrArg (fun l=>Digits l I) draw) cells) S y f p (g N per v) q
      ≤ (g N per v)^target*gross R D d p S A B:=by
  let P:=stopped R d N K c v (cast (congrArg (fun l=>Digits l I) draw) cells) y S f (start R d κ pt (fill R d S q))
  have amount:=WilsonOlderFreshSoftSocketGross.original R D d p S occupied realm draw paid dorm N K c v
    first vc ck live A B front march κ pt (fill R d S q) cells y f fn
  have cash:=forecast (degree R d S (fill R d S q)) lag
  exact (mul_le_mul_of_nonneg_right cash (show 0≤WilsonReportingAbsoluteInletForecastBooks.mass p (coin P) from sum_nonneg fun _ _=>abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left amount (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))

end YM.Integration.WilsonOriginalTwoFlatRoseMerClock
