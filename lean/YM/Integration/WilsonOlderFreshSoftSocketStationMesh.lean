import YM.Integration.WilsonOlderFreshSoftSocketStationSingleton
import YM.Integration.WilsonOlderFreshSoftSocketStationInverse

/-! The full signed connected return on the original tested relative mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationMesh
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
open WilsonOlderFreshSoftSocketStationDeposit (Cleared)
open WilsonOlderFreshSoftSocketStationRows (Compared)
open WilsonOlderFreshSoftSocketTrueNorm (deposit)
open WilsonOlderFreshSoftSocketFitted (residual)

open WilsonOlderFreshSoftSocketStationSingleton (reserve)
open WilsonOlderFreshSoftSocketStationInverse (budget total)
open WilsonOlderFreshSoftSocketStationStops (Paired)

def Charged (D:Fin 3→ℕ)(p q order width:ℕ)(ξ η δ:ℝ)(m C:Fin 3→ℝ)(A₀:Group R.family 6)(r:ℝ)
    (M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c w:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N):Prop:=
  ∀(tests:Sites N per×Sites N per→(t:Faces)→TestAt D t)(φ:YM.Test 3)(a:ℝ),
    let g:=regulatorRun R.family N per K
    let θ:=regulatorRun R.family N per v
    let probes:=fun y t=>enrolled R D V draw N per c (ck.trans live.le) y t (tests y t)
    let x:=vector R grade (fun _=>A₀.station.k) K order η M (filed R A₀) (fun _=>kK) reg N per
    let pay:=fun i=>(r/R.family.S.a K)^(grade i)
    let Q:=table R D V N per K c w v probes g x pay p θ true
    let F:=table R D V N per K c w v probes g x pay p θ false
    let O:=actual R A₀ (N:=N) (per:=per)
    let H:=overhead R width ξ η δ m
    let B:=reserve R D p H C
    (∀y,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y≠0→∀s:Faces,s.Nonempty→s≠Finset.univ→‖O y s‖≤a) →
      ‖deficit R A₀ φ r F Q‖≤(∫z:Points 3,‖φ z‖)*(total R C*budget a B)*g^q

theorem original (D:Fin 3→ℕ)(p q order width:ℕ)(ξ η δ:ℝ)(m C:Fin 3→ℝ)(A₀:Group R.family 6)(r:ℝ)(rp:0<r)
    (M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c w:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N)(vN:v≤N)
    (low:regulatorRun R.family N per v≤1)(cool:regulatorRun R.family N per K≤1):
    let H:=overhead R width ξ η δ m
    let surface:=q+2*H
    Hearing R D p surface width ξ δ η m C A₀ r order M reg v N per K c w V draw kK ck live →
    Paired R D p surface order η C A₀ r M reg v N per K c w V draw kK ck live →
    Cleared R D p width ξ δ η m C A₀ r order M reg v N per K c V draw kK ck live →
    Compared R D p surface C η A₀ r order M reg v N per K c w V draw kK ck live →
    Charged R D p q order width ξ η δ m C A₀ r M reg v N per K c w V draw kK ck live:=by
  intro H surface terms pair bank rows tests φ a g θ probes x pay Q F O H₁ B proper
  have norm:=WilsonOlderFreshSoftSocketStationSingleton.original R D p surface width ξ δ η m C A₀ r rp order M reg
    v N per K c w V draw kK ck live vN low cool terms bank rows
  apply WilsonOlderFreshSoftSocketStationInverse.paid R A₀ N per r φ F Q C a B g
    (ActualRunKernelPackets.regulator_pos R N per K live.le) cool q H proper _ (pair tests p le_rfl φ)
  intro y _ i
  have filled:({i}:Faces).Nonempty:=singleton_nonempty _
  change ‖if ({i}:Faces).Nonempty then _ else _‖≤_
  rw [if_pos filled]
  exact norm {i} filled y (tests y {i})

end YM.Integration.WilsonOlderFreshSoftSocketStationMesh
end
