import YM.Integration.WilsonOlderFreshSoftSocketStationTerminal

/-! The measured moving-stop bill for a declared original salary on the checked station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationSale
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

open WilsonOlderFreshSoftSocketStationTerminal (invoice)

def rent (width:ℕ)(ξ η:ℝ)(m:Fin 3→ℝ)(t:Faces):ℝ:=
  power R grade (seat t) (fun i=>3*m i/2) η (fun _=>3*(width:ℝ)) (fun _=>3*((width:ℝ)+ξ))

def overhead (width:ℕ)(ξ η δ:ℝ)(m:Fin 3→ℝ):ℕ:=
  univ.sup (fun t:Faces=>⌈rent R width ξ η m t+δ⌉₊)

theorem covers (width:ℕ)(ξ η δ:ℝ)(m:Fin 3→ℝ)(q:ℕ)(t:Faces):
    (q:ℝ)+rent R width ξ η m t+δ≤((q+overhead R width ξ η δ m:ℕ):ℝ):=by
  have lo:=Nat.le_ceil (rent R width ξ η m t+δ)
  have hi:⌈rent R width ξ η m t+δ⌉₊≤overhead R width ξ η δ m:=
    Finset.le_sup (f:=fun t:Faces=>⌈rent R width ξ η m t+δ⌉₊) (mem_univ t)
  push_cast
  linarith only [lo,Nat.cast_le (α:=ℝ) |>.mpr hi]

def Hearing (D:Fin 3→ℕ)(p q width:ℕ)(ξ δ η:ℝ)(m C:Fin 3→ℝ)
    (A₀:Group R.family 6)(r:ℝ)(order:ℕ)(M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c w₀:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N):Prop:=
  ∀(t:Faces),t.Nonempty→∀(y:Sites N per×Sites N per)(trial:TestAt D t),
    let probe:=enrolled R D V draw N per c (ck.trans live.le) y t trial
    let w:=fitted R grade (fun _=>A₀.station.k) K order η M (filed R A₀) (fun _=>kK) reg N per
    (∏z:t,(r/R.family.S.a K)^grade (seat t z))*‖residual R p D V t draw N per K c w₀ v probe w‖≤
      invoice R D p C t*‖probe.test‖*((4/3:ℝ)^(rent R width ξ η m t+δ)*(regulatorRun R.family N per v)^q)

variable {ord:Extraction.Order}{hier:(Bel R.family.book).Hierarchy}
theorem original (simple:G.Simple)(width:ℕ){ξ δ η:ℝ}(xp:0<ξ)(dp:0<δ)(ep:0<η):
    ∀ᶠv:ℕ in atTop,∀(D:Fin 3→ℕ)(p q start order N per K c w₀:ℕ)(opt:ℝ)
    (A₀:Group R.family 6)(_checked:A₀.station.checked ord hier A₀.horizon)(r:ℝ),
    A₀.station.wheel.r=r→v≤A₀.station.k→start≤A₀.station.k→∀(kK:A₀.station.k≤K),
    v≤w₀→w₀≤c→∀(ck:c≤K)(live:K<N),v+1≤K→8≤R.family.path.levels.clock.hatBeta K→
    R.family.S.a v/R.family.S.a K≤R.family.path.levels.clock.hatBeta v^width→
    R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(m C M:Fin 3→ℝ)
      (reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀)),
      (∀i,0 ≤ m i)→(∀i,0≤C i)→(∀i,0≤M i)→(∀i,M i≤C i*(R.family.path.levels.clock.hatBeta K)^(m i))→
      Bought R D p (q+overhead R width ξ η δ m) start v N per K V draw opt δ→
      Hearing R D p q width ξ δ η m C A₀ r order M reg v N per K c w₀ V draw kK ck live:=by
  obtain ⟨age,unit⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketStationUnits.original R simple width xp)
  filter_upwards [WilsonOlderFreshSoftSocketFigurePower.original R simple width,eventually_ge_atTop age] with v restore older
  intro D p q start order N per K c w₀ opt A₀ checked r rr vk startk kK first second ck live away warm band span V draw m C M reg m0 C0 M0 salary bought
    t occupied y trial probe w
  let k:=A₀.station.k
  let θ:=regulatorRun R.family N per v
  let x:=regulatorRun R.family N per K
  let s:=Real.log x⁻¹
  let income (i:Fin 3):=(r/R.family.S.a K)^grade i
  let E:=rent R width ξ η m t
  let target:=q+overhead R width ξ η δ m
  have rpos:0<r:=rr ▸ A₀.station.wheel.rad
  have pos i:0 ≤ income i:=pow_nonneg (div_nonneg rpos.le (R.family.S.a_pos _).le) _
  have cash i:M i≤C i*Real.exp ((2*(3*m i/2))*s):=by
    have rate:=WilsonOlderFreshSoftSocketStationScale.heated R N per K live.le warm (m i) (m0 i)
    have h:2*(3*m i/2)=3*m i:=by ring
    rw [h]
    exact (salary i).trans (mul_le_mul_of_nonneg_left rate (C0 i))
  have edges:=unit A₀.station.k (older.trans vk) A₀.station.b checked.high.2 v K N per vk kK live.le warm band
  have inc i:income i≤Real.exp ((grade i:ℝ)*(3*((width:ℝ)+ξ))*s):=by
    change (r/R.family.S.a K)^_≤_
    rw [←rr]
    exact edges.2 (grade i)
  have heard:=bought t occupied (fun _=>k) (fun _=>startk)
    c w₀ first second ck live away (by linarith only [warm]) span A₀ order η M
    (fun _=>kK) reg ep.le M0 income (fun i=>3*m i/2) C (fun _=>3*(width:ℝ)) (fun _=>3*((width:ℝ)+ξ))
    y trial pos cash (fun _=>edges.1) inc
  have E0:0≤E:=by
    unfold E rent power
    apply Finset.sum_nonneg
    intro i _
    have mi:0 ≤ m (seat t i):=m0 _
    unfold WilsonOlderFreshSoftTrialPower.exposure
    positivity
  have spending:=restore N per K (vk.trans kK) live.le band E δ target q (add_nonneg E0 dp.le) (covers R width ξ η δ m q t)
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

end YM.Integration.WilsonOlderFreshSoftSocketStationSale
end
