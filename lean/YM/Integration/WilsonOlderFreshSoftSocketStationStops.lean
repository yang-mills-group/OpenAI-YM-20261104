import YM.Integration.WilsonOlderFreshSoftSocketStationCampaign

/-! The genuine seven-face Wilson secant at the second independent stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationStops
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

open WilsonOlderFreshSoftSocketStationSale (rent overhead)
open WilsonOlderFreshSoftRoseSecant (deficit actual)
open WilsonOlderFreshSoftRoseMesh (table fare)
open WilsonOlderFreshSoftRoseNodes (Covered)

def depth (width:ℕ)(ξ η τ δ:ℝ)(m:Fin 3→ℝ)(q:ℕ):ℝ:=
  4*((overhead R width ξ η δ m:ℝ)+τ+(q:ℝ))

def ticket (t:Faces)(C:Fin 3→ℝ):ℝ:=
  if t.Nonempty then WilsonOlderFreshSoftTrialCharge.bill R grade (seat t) C else 0

theorem money (t:Faces)(C:Fin 3→ℝ)(q:ℕ){g:ℝ}(pos:0<g):
    fare R t C q (Real.log g⁻¹)=ticket R t C*g^q:=by
  have heat:Real.exp (-(q:ℝ)*Real.log g⁻¹)=g^q:=by
    rw [Real.log_inv,neg_mul_neg,Real.exp_nat_mul,Real.exp_log pos]
  by_cases filed:t.Nonempty
  · simp only [fare,ticket,if_pos filed,heat]
  · simp only [fare,ticket,if_neg filed,zero_mul]

def Paired (D:Fin 3→ℕ)(p surface order:ℕ)(η:ℝ)(C:Fin 3→ℝ)(A₀:Group R.family 6)(r:ℝ)
    (M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c w:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N):Prop:=
  ∀(tests:Sites N per×Sites N per→(t:Faces)→TestAt D t)(q:ℕ),q≤p→∀φ:YM.Test 3,
    let g:=regulatorRun R.family N per K
    let θ:=regulatorRun R.family N per v
    let probes:=fun y t=>enrolled R D V draw N per c (ck.trans live.le) y t (tests y t)
    let x:=vector R grade (fun _=>A₀.station.k) K order η M (filed R A₀) (fun _=>kK) reg N per
    let paid:=fun i=>(r/R.family.S.a K)^(grade i)
    let Q:=table R D V N per K c w v probes g x paid q θ true
    let F:=table R D V N per K c w v probes g x paid q θ false
    ‖deficit R A₀ φ r F Q‖≤
      (∑y:Sites N per×Sites N per,‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*
        ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (actual R A₀ y) (Q y) t‖*ticket R t C)*g^surface

variable {ord:Extraction.Order}{hier:(Bel R.family.book).Hierarchy}
theorem original (simple:G.Simple)(width:ℕ){ξ δ η τ:ℝ}(xp:0<ξ)(dp:0<δ)(ep:0<η):
    ∀ᶠv:ℕ in atTop,∀(D:Fin 3→ℕ)(p surface start order N per K c w:ℕ)(opt:ℝ)
    (A₀:Group R.family 6),A₀.station.checked ord hier A₀.horizon→∀r:ℝ,
    A₀.station.wheel.r=r→v≤A₀.station.k→start≤A₀.station.k→∀(kK:A₀.station.k≤K),
    v≤w→w≤c→∀(ck:c≤K)(live:K<N),v+1≤K→8≤R.family.path.levels.clock.hatBeta K→
    R.family.S.a v/R.family.S.a K≤R.family.path.levels.clock.hatBeta v^width→
    R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(m C M:Fin 3→ℝ)
      (reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀)),
      (∀i,0 ≤ m i)→(∀i,0≤C i)→(∀i,0≤M i)→(∀i,M i≤C i*(R.family.path.levels.clock.hatBeta K)^(m i))→
      R.family.S.a c/R.family.S.a w≤Real.exp (-(depth R width ξ η τ δ m surface)*Real.log (regulatorRun R.family N per K)⁻¹)→
      Covered R D p v start V draw opt τ→Paired R D p surface order η C A₀ r M reg v N per K c w V draw kK ck live:=by
  obtain ⟨age,unit⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketStationUnits.original R simple width xp)
  filter_upwards [WilsonSeparatedPrefixKineticGeometry.spend R simple 1 0,eventually_ge_atTop age] with v cold older
  intro D p surface start order N per K c w opt A₀ checked r rr vk startk kK first second ck live away warm band span
    V draw m C M reg m0 C0 M0 salary gap covered tests q cut φ g θ probes x paid Q F
  let s:=Real.log g⁻¹
  have rpos:0<r:=rr ▸ A₀.station.wheel.rad
  have gpos:0<g:=ActualRunKernelPackets.regulator_pos R N per K live.le
  have θpos:0<θ:=ActualRunKernelPackets.regulator_pos R N per v ((vk.trans kK).trans live.le)
  have θ1:|θ|≤1:=by
    rw [abs_of_pos θpos]
    apply (one_le_inv₀ θpos).mp
    simpa only [pow_zero,mul_one] using cold N per ((vk.trans kK).trans live.le)
  have pos i:0 ≤ paid i:=pow_nonneg (div_nonneg rpos.le (R.family.S.a_pos _).le) _
  have cash i:M i≤C i*Real.exp ((2*(3*m i/2))*s):=by
    have rate:=WilsonOlderFreshSoftSocketStationScale.heated R N per K live.le warm (m i) (m0 i)
    have h:2*(3*m i/2)=3*m i:=by ring
    rw [h]
    exact (salary i).trans (mul_le_mul_of_nonneg_left rate (C0 i))
  have edges:=unit A₀.station.k (older.trans vk) A₀.station.b checked.high.2 v K N per vk kK live.le warm band
  have inc i:paid i≤Real.exp ((grade i:ℝ)*(3*((width:ℝ)+ξ))*s):=by
    change (r/R.family.S.a K)^_≤_
    rw [←rr]
    exact edges.2 (grade i)
  have tall(t:Faces):rent R width ξ η m t+τ+(surface:ℝ)≤depth R width ξ η τ δ m surface/4:=by
    have pre:=WilsonOlderFreshSoftSocketStationSale.covers R width ξ η δ m 0 t
    simp only [Nat.cast_zero,zero_add] at pre
    unfold depth
    linarith only [pre,dp]
  have earned:=covered A₀ (fun _=>A₀.station.k) (fun _=>startk) N per K c w order first second ck live away
    (by linarith only [warm]) span η M (fun _=>kK) reg ep.le M0 paid (fun i=>3*m i/2) C (fun _=>3*(width:ℝ))
    (fun _=>3*((width:ℝ)+ξ)) (depth R width ξ η τ δ m surface) surface pos C0 cash (fun _=>edges.1) inc gap
    (fun t _=>tall t) tests q cut θ θ1 φ r
  apply earned.trans_eq
  change (∑ y:Sites N per×Sites N per,‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*
    ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (actual R A₀ y) (Q y) t‖*fare R t C surface (Real.log g⁻¹))=_
  simp only [money R _ C surface gpos,Finset.sum_mul,mul_assoc]

end YM.Integration.WilsonOlderFreshSoftSocketStationStops
end
