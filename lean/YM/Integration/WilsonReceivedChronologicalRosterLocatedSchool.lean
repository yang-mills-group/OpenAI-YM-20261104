import YM.Integration.WilsonReceivedChronologicalRosterAssay
import YM.Integration.WilsonReceivedChronologicalRosterWindow
import YM.Integration.WilsonReceivedChronologicalFixedRoseGridCampus
import YM.Integration.WilsonReceivedChronologicalRosterCourse

/-! One paid room and original marked clock for the measured pair, before the physical period and cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterLocatedSchool
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
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open Analysis XSpace Cells Table Spec Extraction
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonReceivedChronologicalFixedCellFee (capture factor)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics
open WilsonAddressedPublicFirstRoseSchedule (allowance)
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{U:Type}[Fintype U]

open Marker Multi QuadraticLocal QuadraticLocal.Earn

open WilsonOriginalCensusDatedSchools (Paired)
open WilsonOriginalCensusMeasuredStation (CreditAt)
open WilsonCoeffUV.Bank.Carp

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusAttendanceStation WilsonOriginalCensusPublicationClock

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

open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedCanonicalVerseBasis OriginalMarkedSourceComet
open Multi WilsonCoeffUV.Blue

open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedTariff (gross allowance)
open WilsonOriginalCensusFaceAdmission (housed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonOriginalCensusDatedPeriodOpening (Opened)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonOriginalFixedTestCensusPublicBase (base)
open WilsonOriginalCensusPublicationClock (Open)

open WilsonCenteredPhysicalPanel
open StressFlux.Matching Next.UVStress
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedPorts (Period)

open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonAddressedPublicSubmittedDates (grades positive)
open WilsonAddressedPublicFirstPeriod (appointment)
open WilsonAddressedPublicFirstRoseCampus (seller financed)
open WilsonOriginalReflectedFirstPanels (Sold)

def Seated (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity→ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (φ:Test arity)(requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):=
    let n:=arity
    let front:Fin n:=head
    let k:=subjects
    let κ:∀v:Fin arity,Knob (D v):=fun v=>contact (D v)
    let power:=fun _:Fin arity=>0
    let target:=WilsonOriginalReflectedFirstTerms.order R subjects requested
    let P:=target+1
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let firstPeriod:=appointment R simple k D pt (fun _=>4) tube ask.order ask.order menu.target menu.precision
      (seller G) (financed paid) (WilsonAddressedPublicFirstRanks.original k P).2.2.2.1
    fun (book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple) (B:ℝ)
      (o:ℕ) (resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N)
      (V:Realm G (menu.order+1) Credit.leanC) (draw:V.draws=L)
      (m j:ℕ) (old:o ≤ m) (mj:m+1 ≤ j) (per N:ℕ) (valid:j+1+1 ≤ N) =>
      let K:=j+1+1
      let δ:ℝ:=1
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^n
        let oldDay:=resident N (old.trans ((Nat.le_succ m).trans (mj.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid)))))
        ∃classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) power P book oldDay κ pt K m valid
          (fun j=>base B caps power (L.clock.hatBeta (j+1))) old φ caps A target η,
        Sold (R:=R) (simple:=simple) (d:=k) (P:=P) (m:=o) (first:=m) (j:=j) (N:=N) (per:=per)
          (schedule:=s) (A:=A) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) (φ:=φ) (caps:=caps) (promised:=target) (θ:=η)
          (school:=book) (day:=oldDay) (live:=valid) (lens:=D) (pt:=pt)
          (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (old:=old)
          (classroom:=classroom) (adult:=adult) η ∧
        WilsonIndependentConditionedLocatedFirstPanels.Sold (R:=R) (simple:=simple) (d:=k) (P:=P) (m:=o) (first:=m) (j:=j) (N:=N) (per:=per)
          (schedule:=s) (A:=A) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) (φ:=φ) (caps:=caps) (promised:=target) (θ:=η)
          (school:=book) (day:=oldDay) (live:=valid) (lens:=D) (pt:=pt)
          (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (old:=old)
          (classroom:=classroom) (adult:=adult) η ∧
        WilsonReceivedChronologicalRosterAssay.Sold (R:=R) (simple:=simple) (d:=k) (P:=P) (m:=o) (first:=m) (j:=j) (N:=N) (per:=per)
          (schedule:=s) (A:=A) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) (φ:=φ) (caps:=caps) (promised:=target) (θ:=η)
          (school:=book) (day:=oldDay) (live:=valid) (lens:=D) (pt:=pt)
          (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (old:=old)
          (classroom:=classroom) (adult:=adult) η ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k (Burn.horizon ask.vac) school δ tube pieces physical p span lag m ∧
        V.anchor ≤ m+1 ∧
        WilsonOriginalCensusSparseRosterOpening.first R simple tube k k (charges power) menu.order menu.order
          menu.target menu.precision menu.enough ≤ m+1 ∧
        Period (R:=R) (V:=V) (per:=per) (grades:=k) power P κ pt K m caps ∧
        WilsonOriginalOneArmCurrentClock.first R simple k power P (2*A) tol η tp ep (Nat.zero_lt_of_lt front.isLt) ≤ m ∧
        R.family.S.a (m+1)/R.family.S.a K ≤ (L.clock.hatBeta (m+1))^(2*A) ∧
        WilsonAddressedPublicFirstOrigin.ceiling R k ≤ menu.order ∧
        WilsonOriginalReflectedFirstTerms.At R simple k P (2*A) tol η tp ep (m+1) (K-2) ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k (Burn.horizon ask.vac) school δ tube
          pieces physical p span lag (K-2) ∧
        firstPeriod.first ≤ K-2+1 ∧
        firstPeriod.period (K-2+1)
          (WilsonAddressedPublicFirstExtent.extent V.draws (0:Fin arity → Cover) m (K-2-m)) ≤ per

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit){arity:ℕ}(head:Fin arity)(subjects:Fin arity→ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (φ:Test arity)(requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    let n:=arity
    let _front:Fin n:=head
    let k:=subjects
    let _κ:∀v:Fin arity,Knob (D v):=fun v=>contact (D v)
    let power:=fun _:Fin arity=>0
    let target:=WilsonOriginalReflectedFirstTerms.order R subjects requested
    let P:=target+1
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let _firstPeriod:=appointment R simple k D pt (fun _=>4) tube ask.order ask.order menu.target menu.precision
      (seller G) (financed paid) (WilsonAddressedPublicFirstRanks.original k P).2.2.2.1
    ∀(book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple) (B:ℝ)
      (o:ℕ) (resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N)
      (V:Realm G (menu.order+1) Credit.leanC) (draw:V.draws=L)
      (m j:ℕ) (old:o ≤ m) (mj:m+1 ≤ j) (per N:ℕ) (valid:j+1+1 ≤ N),
      WilsonSingleHardRadius.first R simple ≤ o → WilsonOriginalCensusCanonicalAppointedClock.opening R simple
        (seller G) (financed paid) paths (Burn.horizon ask.vac) ≤ o →
      WilsonReceivedChronologicalRosterWindow.Slot paid head subjects adult D pt caps φ requested A tol η tp ep school tube pieces physical p span lag book B o resident V draw m j old mj per N valid →
      Seated paid head subjects adult D pt caps φ requested A tol η tp ep school tube pieces physical p span lag book B o resident V draw m j old mj per N valid:=by
  intro n front k κ power target P menu ask L firstPeriod book B o resident V draw m j old mj per N valid floorOld activated given
  obtain ⟨classroom,named,placed,_base,venue,_sparse,_period,_current,geo,ranked,stages,atj,go,board⟩:=given
  refine ⟨classroom,named,placed,?_,_base,venue,_sparse,_period,_current,geo,ranked,stages,atj,go,board⟩
  have same:j+1+1-2=j:=by omega
  rw [same] at stages atj go board
  intro f fine
  exact WilsonReceivedChronologicalRosterAssay.original (R:=R) (simple:=simple) (d:=k) (P:=P)
    (school:=book) (day:=resident N _) (old:=old) (early:=by omega) (live:=valid) (lens:=D) (pt:=pt)
    (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (classroom:=classroom)
    (nonempty:=(Nat.zero_lt_of_lt head.isLt)) (adult:=adult) (seller:=seller G) (fund:=financed paid) (history:=paths)
    (tube:=tube) (ep:=ep) (tp:=tp) (authorized:=stages) (activated:=activated) (ranked:=ranked)
    (faculty:=atj) (venue:=venue.trans (by omega)) (go:=go) (board:=board) (floorOld:=floorOld)
    (geo:=geo) (support:=paid.support) fine


end YM.Integration.WilsonReceivedChronologicalRosterLocatedSchool
end
