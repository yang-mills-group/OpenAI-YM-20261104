import YM.Integration.WilsonOlderFreshSoftSocketStationBerth
import YM.Integration.WilsonOlderFreshSoftSocketTrueNorm

/-! Price the complete normalized K-planted ordinary field on its indicated physical roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationDeposit
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

open WilsonOlderFreshSoftSocketStationSale (Hearing overhead)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonMovingForkWindowBooks (Priced)
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare


open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
open MS MS.Land FVA2 FVA2.Register


open WilsonOlderFreshSoftSocketStationSale (rent covers)
open WilsonOlderFreshSoftSocketStationStops (ticket money Paired depth)
open WilsonOlderFreshSoftSocketStationTerminal (invoice)
variable {ord:Extraction.Order}{hier:(Bel R.family.book).Hierarchy}
open WilsonOlderFreshSoftSocketTrueNorm (deposit)
private theorem pull {X:Type*}(F:X→Type*){a b:X}(h:a=b)(x:F b):
    cast (congrArg F h) (show F a from h.symm ▸ x)=x:=by cases h;rfl

theorem same (D:Fin 3→ℕ)(p:ℕ)(V V₁:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (hub:V₁.draws=R.family.path.levels)(N per K c v:ℕ)(stem:c≤N)(y:Sites N per×Sites N per)
    (t:Faces)(trial:TestAt D t)(w:(i:Fin 3)→R.family.label (grade i)):
    deposit R p D V t draw N per K c v (enrolled R D V draw N per c stem y t trial) w=
      deposit R p D V₁ t hub N per K c v (enrolled R D V₁ hub N per c stem y t trial) w:=by
  let tape:Digits R.family.path.levels t:=fun j i=>WilsonOriginalPublicFixedCourse.digits R per (atOrigin y) j (seat t i)
  have back (U:Realm G (p+1) Credit.leanC)(h:U.draws=R.family.path.levels):
      cast (congrArg (fun l=>Digits l t) h) (enrolled R D U h N per c stem y t trial).digit=tape:=
    pull (fun l=>Digits l t) h tape
  unfold deposit
  rw [back V draw,back V₁ hub]
  rfl

def Cleared (D:Fin 3→ℕ)(p width:ℕ)(ξ δ η:ℝ)(m C:Fin 3→ℝ)
    (A₀:Group R.family 6)(r:ℝ)(order:ℕ)(M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N):Prop:=
  ∀(t:Faces),t.Nonempty→∀(y:Sites N per×Sites N per)(trial:TestAt D t),
    let probe:=enrolled R D V draw N per c (ck.trans live.le) y t trial
    let w:=fitted R grade (fun _=>A₀.station.k) K order η M (filed R A₀) (fun _=>kK) reg N per
    (∏z:t,(r/R.family.S.a K)^grade (seat t z))*‖deposit R p D V t draw N per K c v probe w‖≤
      invoice R D p C t*‖probe.test‖*(regulatorRun R.family N per K)⁻¹^(rent R width ξ η m t+δ)

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(p width:ℕ)(opt:ℝ)(opt0:0≤opt){ξ δ η:ℝ}(xp:0<ξ)(dp:0<δ)(ep:0<η):
    ∀ᶠv:ℕ in atTop,∀(order N per K c:ℕ)(A₀:Group R.family 6)(_checked:A₀.station.checked ord hier A₀.horizon)(r:ℝ),
    A₀.station.wheel.r=r→v≤A₀.station.k→∀(kK:A₀.station.k≤K),v≤c→∀(ck:c≤K)(live:K<N),v+1≤K→
    8≤R.family.path.levels.clock.hatBeta K→
    R.family.S.a A₀.station.k/R.family.S.a K≤R.family.path.levels.clock.hatBeta A₀.station.k^width→
    R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)(m C M:Fin 3→ℝ)
      (reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀)),
      (∀i,0 ≤ m i)→(∀i,0≤C i)→(∀i,0≤M i)→(∀i,M i≤C i*(R.family.path.levels.clock.hatBeta K)^(m i))→
      Cleared R D p width ξ δ η m C A₀ r order M reg v N per K c V draw kK ck live:=by
  obtain ⟨start,panels⟩:=WilsonOlderFreshSoftSocketFigureRoom.original R paid D fit p opt 1 opt0 zero_lt_one
  obtain ⟨u₀,measurement⟩:=WilsonOlderFreshSoftSocketTrueNorm.original R simple (WilsonOlderFreshSoftRoseMarket.physical paid)
    D p opt δ opt0 dp
  obtain ⟨age,unit⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketStationUnits.original R simple width xp)
  filter_upwards [panels,eventually_ge_atTop u₀,eventually_ge_atTop age,(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 8] with v board late older hat
  intro order N per K c A₀ checked r rr vk kK vc ck live away warm planted span V draw m C M reg m0 C0 M0 salary t occupied y trial probe w
  obtain ⟨V₁,hub,scheme,heat,anchor,shelf,_,_⟩:=board
  let other:=enrolled R D V₁ hub N per c (ck.trans live.le) y t trial
  let k:=A₀.station.k
  let x:=regulatorRun R.family N per K
  let z:=Real.log x⁻¹
  let income(i:Fin 3):=(r/R.family.S.a K)^grade i
  let E:=rent R width ξ η m t
  have rpos:0<r:=rr ▸ A₀.station.wheel.rad
  have pos i:0 ≤ income i:=pow_nonneg (div_nonneg rpos.le (R.family.S.a_pos _).le) _
  have cash i:M i≤C i*Real.exp ((2*(3*m i/2))*z):=by
    have rate:=WilsonOlderFreshSoftSocketStationScale.heated R N per K live.le warm (m i) (m0 i)
    rw [show 2*(3*m i/2)=3*m i by ring]
    exact (salary i).trans (mul_le_mul_of_nonneg_left rate (C0 i))
  have hold:=unit A₀.station.k (older.trans vk) A₀.station.b checked.high.2 A₀.station.k K N per le_rfl kK live.le warm planted
  have inc i:income i≤Real.exp ((grade i:ℝ)*(3*((width:ℝ)+ξ))*z):=by
    change (r/R.family.S.a K)^_≤_
    rw [←rr]
    exact hold.2 (grade i)
  have cold {j:ℕ}(hj:8≤R.family.path.levels.clock.hatBeta j)(jn:j≤N):regulatorRun R.family N per j≤1:=by
    change (Real.sqrt (R.family.path.β N per j))⁻¹≤1
    apply inv_le_one_of_one_le₀
    apply Real.one_le_sqrt.mpr
    have band:=(R.makes.wilson.represents N per j jn).band.1
    change R.family.path.levels.clock.hatBeta j/2≤R.family.path.β N per j at band
    linarith
  have heard:=measurement t occupied v late (fun _=>k) (fun _=>late.trans vk) (fun _=>(paid.support k).le) N per K c vc ck live away
    (by linarith only [warm]) span (cold warm live.le) (cold hat ((vk.trans kK).trans live.le)) V₁ hub scheme heat anchor.le (shelf t)
    other order η M (filed R A₀) (fun _=>kK) reg ep.le M0 income (fun i=>3*m i/2) C (fun _=>3*(width:ℝ))
    (fun _=>3*((width:ℝ)+ξ)) pos cash (fun _=>hold.1) inc
  have xpos:0<x:=ActualRunKernelPackets.regulator_pos R N per K live.le
  rw [same R D p V V₁ draw hub N per K c v (ck.trans live.le) y t trial w]
  apply heard.trans_eq
  change _=invoice R D p C t*‖trial.test‖*x⁻¹^(E+δ)
  rw [Real.rpow_add (inv_pos.mpr xpos),Real.rpow_def_of_pos (inv_pos.mpr xpos) E]
  unfold WilsonOlderFreshSoftSocketStationTerminal.invoice
  change (_*Real.exp (E*z))*(_*(‖trial.test‖*(_*x⁻¹^δ)))=_*‖trial.test‖*(Real.exp (z*E)*x⁻¹^δ)
  ring

end YM.Integration.WilsonOlderFreshSoftSocketStationDeposit
end
