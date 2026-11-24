import YM.Integration.WilsonOlderFreshSoftSocketStationBerth

/-! The tested seven-face inverse on the true finite regulator and the original relative cell mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationInverse
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
def total (C:Fin 3→ℝ):ℝ:=∑t:Faces,|ticket R t C|

def budget (proper base:ℝ):ℝ:=
  let A:=max 1 (max proper base)
  7*(A+2*A^2)

theorem inverse (O Q:Faces→ℂ)(a B X:ℝ)(one:1≤X)
    (proper:∀s:Faces,s.Nonempty→s≠Finset.univ→‖O s‖≤a)(single:∀i:Fin 3,‖Q {i}‖≤B*X):
    ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill O Q t‖≤budget a B*X^2:=by
  let A:=max 1 (max a B)
  let T:=max 1 (max a (B*X))
  have A0:0≤A:=zero_le_one.trans (le_max_left ..)
  have T0:0≤T:=zero_le_one.trans (le_max_left ..)
  have X0:0≤X:=zero_le_one.trans one
  have ax:A≤A*X:=le_mul_of_one_le_right A0 one
  have lim:T≤A*X:=max_le ((le_max_left ..).trans ax)
    (max_le (((le_max_left a B).trans (le_max_right ..)).trans ax)
      (mul_le_mul_of_nonneg_right ((le_max_right a B).trans (le_max_right ..)) X0))
  calc _≤7*(T+2*T^2):=WilsonMaxwellThermometerNominatedSecant.budget O Q a (B*X) proper single
       _≤7*(A*X+2*(A*X)^2):=by gcongr
       _≤budget a B*X^2:=by
         have sq:X≤X^2:=by rw [pow_two];exact le_mul_of_one_le_right X0 one
         have h:=mul_le_mul_of_nonneg_left sq A0
         change _≤(7*(A+2*A^2))*X^2
         nlinarith only [h]

theorem paid (A:Group R.family 6)(N per:ℕ)(r:ℝ)(φ:Test 3)(F Q:Sites N per×Sites N per→Faces→ℂ)
    (C:Fin 3→ℝ)(a B g:ℝ)(g0:0<g)(g1:g≤1)(q H:ℕ):
    let μ:=WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ
    let O:=actual R A (N:=N) (per:=per)
    (∀y,μ y≠0→∀s:Faces,s.Nonempty→s≠Finset.univ→‖O y s‖≤a) →
    (∀y,μ y≠0→∀i:Fin 3,‖Q y {i}‖≤B*g⁻¹^H) →
    ‖deficit R A φ r F Q‖≤(∑y:Sites N per×Sites N per,‖μ y‖*
      ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (O y) (Q y) t‖*ticket R t C)*g^(q+2*H) →
    ‖deficit R A φ r F Q‖≤(∫z:Points 3,‖φ z‖)*(total R C*budget a B)*g^q:=by
  intro μ O proper single full
  let X:=g⁻¹^H
  let fee:=total R C
  let T:=max 1 (max a B)
  have unit:1≤X:=one_le_pow₀ ((one_le_inv₀ g0).mpr g1)
  have X0:0≤X:=zero_le_one.trans unit
  have fee0:0≤fee:=sum_nonneg fun _ _=>abs_nonneg _
  have T0:0≤T:=zero_le_one.trans (le_max_left ..)
  have cost0:0≤budget a B:=by change 0≤7*(T+2*T^2);positivity
  have priced (t:Faces):ticket R t C≤fee:=(le_abs_self _).trans (single_le_sum (f:=fun u:Faces=>|ticket R u C|)
    (fun u _=>abs_nonneg _) (mem_univ t))
  have sum:(∑y:Sites N per×Sites N per,‖μ y‖*
       ∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (O y) (Q y) t‖*ticket R t C)≤
       (∫z:Points 3,‖φ z‖)*(fee*(budget a B*X^2)):=by
    calc _≤∑y:Sites N per×Sites N per,‖μ y‖*(fee*(budget a B*X^2)):=by
           apply sum_le_sum
           intro y _
           by_cases absent:μ y=0
           · simp [absent]
           apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
           calc _≤∑t:Faces,‖WilsonMaxwellThermometerNominatedSecant.bill (O y) (Q y) t‖*fee:=
                   sum_le_sum fun t _=>mul_le_mul_of_nonneg_left (priced t) (norm_nonneg _)
                _≤_:=by
                  rw [←sum_mul,mul_comm _ fee]
                  exact mul_le_mul_of_nonneg_left (inverse (O y) (Q y) a B X unit (proper y absent) (single y absent)) fee0
         _≤_:=by
           rw [←sum_mul]
           exact mul_le_mul_of_nonneg_right (WilsonThermometerAlignedCells.variation (R:=R) r (N,per) φ) (by positivity)
  apply full.trans ((mul_le_mul_of_nonneg_right sum (pow_nonneg g0.le _)).trans_eq ?_)
  change _= _*(fee*budget a B)*g^q
  dsimp only [X]
  rw [pow_add,Nat.mul_comm 2 H,pow_mul,inv_pow]
  field_simp [g0.ne']

end YM.Integration.WilsonOlderFreshSoftSocketStationInverse
end
