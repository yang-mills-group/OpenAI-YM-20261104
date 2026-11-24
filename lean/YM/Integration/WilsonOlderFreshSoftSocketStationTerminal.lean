import YM.Integration.WilsonOlderFreshSoftSocketFigureCurve
import YM.Integration.WilsonOlderFreshSoftSocketStationBook
import YM.Integration.WilsonOlderFreshSoftSocketStationMass
import YM.Integration.WilsonOlderFreshSoftSocketStationUnits
import YM.Integration.WilsonOlderFreshSoftSocketFigurePower

/-! The funded measured station, including its cutoff field, is heard on the true shifted planting cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationTerminal
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor
open WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {crop:Campaign R} {W:Campaign.Pillars R crop}

open WilsonOlderFreshSoftRoseCourse (grade seat Hearing)
open WilsonOlderFreshSoftTrialCharge (power bill)


open WilsonOlderFreshSoftRoseMarket (Probe row scaled)
open WilsonOlderFreshSoftRoseSecant (deficit actual)
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (atOrigin)

variable (R) (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "Faces" => Finset (Fin 3)
local notation "Sites" N:max per:max => Site (R.family.side N per)


open WilsonOriginalPublicFixedCourse (sites digits home)
open WilsonOlderFreshSoftRoseMesh (filed table fare)
open WilsonMaxwellThermometerNominatedSecant (bill)

open WilsonOlderFreshSoftRoseNodes (TestAt enrolled Covered)
open WilsonOlderFreshSoftTrialCut (source)
open WilsonOlderFreshSoftMoment (mixed)

open WilsonOlderFreshSoftRoseIncome (Stock)
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonVacuumPreResetDatedDeposit (Issued)
open PertExtension.Series WilsonCoeffUV.Blue.Cameo
open WilsonOriginalAllOrderCourse
open WilsonOriginalOccupiedForestIntegral
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDatedCourse
open WilsonReportingAbsoluteInletForecastBooks
open WilsonOlderFreshSoftSocketFitted (residual)
open WilsonOlderFreshSoftSocketOptical (fixed)
open WilsonOlderFreshSoftSocketCensus (fee)
open WilsonOriginalPublicTrialInput (fitted)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonIndependentCollarCensusCourse
open Filter


open WilsonOlderFreshSoftSocketFigureCurve (Bought)
open WilsonOlderFreshSoftSocketVane (quotaFare)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOriginalPublicTrialInput (fitted)
open WilsonPositionThermometerCapStation (Group)
open Cells Extraction Climb Trace Trace.Pilot PhysMS

def degree (width:ℕ)(ξ η:ℝ)(t:Faces):ℝ:=
  power R grade (seat t) (fun _=>3*ξ/2) η (fun _=>3*(width:ℝ)) (fun _=>3*((width:ℝ)+ξ))

def invoice (D:Fin 3→ℕ)(p:ℕ)(C:Fin 3→ℝ)(t:Faces):ℝ:=
  WilsonOlderFreshSoftTrialCharge.bill R grade (seat t) C*fee R (grade ∘ seat t) (univ:Finset t)*
    fixed R (D ∘ seat t) (grade ∘ seat t) p (univ:Finset t)

variable {ord:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}{hier:(Bel R.family.book).Hierarchy}{S:Table R.family.book}

def Face (D:Fin 3→ℕ)(p target start age width:ℕ)(opt ξ δ η:ℝ)(C:Fin 3→ℝ)
    (A₀:Group R.family 6)(r:ℝ)(order:ℕ)
    (printed:Finished R grade (fun _=>A₀.station.k) order η (quotaFare R A₀) (filed R A₀)):Prop:=
  ∀(v N per K c w₀:ℕ),age≤v→v≤A₀.station.k→∀(kK:A₀.station.k≤K),v≤w₀→w₀≤c→
    ∀(ck:c≤K)(live:K<N),v+1≤K→8≤R.family.path.levels.clock.hatBeta K→
    R.family.S.a v/R.family.S.a K≤R.family.path.levels.clock.hatBeta v^width→
    R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels),
    Bought R D p target start v N per K V draw opt δ→∀(t:Faces),t.Nonempty→
    ∀(y:Sites N per×Sites N per)(trial:TestAt D t)(q:ℕ)(_outside:(q:ℝ)+degree R width ξ η t+δ≤target),
    let probe:=enrolled R D V draw N per c (ck.trans live.le) y t trial
    let w:=fitted R grade (fun _=>A₀.station.k) K order η (quotaFare R A₀) (filed R A₀)
      (fun _=>kK) printed.1 N per
    (∏z:t,(r/R.family.S.a K)^grade (seat t z))*‖residual R p D V t draw N per K c w₀ v probe w‖≤
      invoice R D p C t*‖probe.test‖*((4/3:ℝ)^(degree R width ξ η t+δ)*(regulatorRun R.family N per v)^q)

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤(R.family.path.levels.budget j).supportExponent)(quote:OPE.Therm.Poetry R.family.path.levels)
    (A:ℝ→Group R.family 6)(P:ℝ→PhysMS.tower S)
    (book:WilsonPositionCapTransport.Book (f:=ord) (l:=l) (H:=hier) A P)
    (D:Fin 3→ℕ)(p target start order width:ℕ)(opt ξ δ η:ℝ)(xp:0<ξ)(dp:0<δ)(ep:0<η):
    ∃C:Fin 3→ℝ,∃age:ℕ,∀ᶠr in trail,∃printed:Finished R grade (fun _=>(A r).station.k) order η
        (quotaFare R (A r)) (filed R (A r)),Face R D p target start age width opt ξ δ η C (A r) r order printed:=by
  obtain ⟨C,C0,wages⟩:=WilsonOlderFreshSoftSocketStationMass.original R simple A P book xp
  obtain ⟨gate,guard⟩:=WilsonOlderFreshSoftSocketStationBook.original (f:=ord) (H:=hier) R simple shop cap quote order ep
  obtain ⟨age,restore⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketFigurePower.original R simple width)
  have dates:Tendsto (fun r=>(A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun k=>(book k).mono fun _ h=>h.1
  refine ⟨C,age,?_⟩
  filter_upwards [wages,book (max gate start),dates.eventually (WilsonOlderFreshSoftSocketStationUnits.original R simple width xp)]
    with r charged active units
  let k:=(A r).station.k
  obtain ⟨printed,M0⟩:=guard (A r) ((le_max_left ..).trans active.1) active.2.1
  refine ⟨printed,?_⟩
  unfold Face
  intro v N per K c w₀ older vk kK first second ck live away warm band span V draw bought t occupied y trial q outside probe w
  let θ:=regulatorRun R.family N per v
  let x:=regulatorRun R.family N per K
  let s:=Real.log x⁻¹
  let income (i:Fin 3):=(r/R.family.S.a K)^grade i
  let E:=degree R width ξ η t
  have rr:(A r).station.wheel.r=r:=active.2.2.1
  have rpos:0<r:=rr ▸ (A r).station.wheel.rad
  have pos i:0 ≤ income i:=pow_nonneg (div_nonneg rpos.le (R.family.S.a_pos _).le) _
  have cash i:quotaFare R (A r) i≤C i*Real.exp ((2*(3*ξ/2))*s):=by
    have rate:=WilsonOlderFreshSoftSocketStationScale.heated R N per K live.le warm ξ xp.le
    have h:2*(3*ξ/2)=3*ξ:=by ring
    rw [h]
    exact (charged K kK i).trans (mul_le_mul_of_nonneg_left rate (C0 i))
  have edges:=units (A r).station.b active.2.1.high.2 v K N per vk kK live.le warm band
  have inc i:income i≤Real.exp ((grade i:ℝ)*(3*((width:ℝ)+ξ))*s):=by
    change (r/R.family.S.a K)^_≤_
    rw [←rr]
    exact edges.2 (grade i)
  have heard:=bought t occupied (fun _=>k) (fun _=>(le_max_right ..).trans active.1)
    c w₀ first second ck live away (by linarith only [warm]) span (A r) order η (quotaFare R (A r))
    (fun _=>kK) printed.1 ep.le M0 income (fun _=>3*ξ/2) C (fun _=>3*(width:ℝ)) (fun _=>3*((width:ℝ)+ξ))
    y trial pos cash (fun _=>edges.1) inc
  have E0:0≤E:=by
    unfold E degree power
    apply Finset.sum_nonneg
    intro i _
    unfold WilsonOlderFreshSoftTrialPower.exposure
    positivity
  have spending:=restore v older N per K (vk.trans kK) live.le band E δ target q (add_nonneg E0 dp.le) outside
  let b:=WilsonOlderFreshSoftTrialCharge.bill R grade (seat t) C
  let g:=fee R (grade ∘ seat t) (univ:Finset t)
  let h:=fixed R (D ∘ seat t) (grade ∘ seat t) p (univ:Finset t)
  have b0:0≤b:=by
    unfold b WilsonOlderFreshSoftTrialCharge.bill
    apply Finset.prod_nonneg
    intro i _
    unfold WilsonOlderFreshSoftTrialSalary.base WilsonOlderFreshSoftTrialSalary.wrap
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (C0 _)
  have g0:0≤g:=sum_nonneg fun _ _=>prod_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have h0:0≤h:=WilsonOlderFreshSoftSocketOptical.fixed_nonneg R _ _ _ _
  have test0:0≤‖probe.test‖:=probe.test.opNorm_nonneg
  calc
    _≤(b*Real.exp (E*s))*(g*(θ^target*(‖probe.test‖*(h*x⁻¹^δ)))):=heard
    _=(b*g*h*‖probe.test‖)*(Real.exp (E*s)*(θ^target*x⁻¹^δ)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left spending (by positivity)

end YM.Integration.WilsonOlderFreshSoftSocketStationTerminal
end
