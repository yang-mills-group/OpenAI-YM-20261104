import YM.Integration.WilsonOriginalMicroscopicEntranceHeldAppointments
import YM.Integration.WilsonMeasuredPublicEntranceMasterRead
/-! Purchase the same occupied physical upper and its uncut lower programme on the original
pre-regulator school. Every permitted held field and angular node uses this one enrolled panel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterRead
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
open WilsonReceivedFirstTrace
open Pert.Asymptotics
open Filter WilsonThermometerMixedCollarSubpower
open WilsonThermometerMixedCollarSubpower
open Multi WilsonOriginalAlternativeTrialFunded
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG05Readout RG05Readout.Native RG05Readout.Address Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout.Many RG05Readout.Pantry Records WilsonThermometerUnitFilingCoarse
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation WilsonMeasuredPublicEntranceFaculty
open WilsonMeasuredPublicEntrancePanel WilsonOriginalMicroscopicEntranceHeldAppointments
open WilsonMeasuredPublicEntranceMasterRead (Opening)
open Push.Local WilsonCoeffUV.Embroider
open WilsonMeasuredPublicEntranceMeshClock (allowance)
open WilsonWindowUniversalSchool
variable {G:Gauge} (R:Run G) (simple:G.Simple) {σ:WilsonOriginalAllOrderCourse.Schedule G}
  {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
  (pace:WilsonWindowReportingPace.Slow R.kit)
  (nested:WilsonPositionProgramNestedLengths.Nested R.rolls) (cater:Cater R.family R.doors)
  (bank:WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels)
  (forecast:WilsonReportLampForecast.Ready R.family.path.levels) (shop:RG05Preconstruction.ReadoutPurchase R.b)
  (n D q apron requested t span power:ℕ)(B:ℝ)(np:0<n)(size:Fintype.card V ≤ n)
local notation "C" => R.family
local notation "H" f:max => R.family.path.levels.clock.hatBeta f
local notation "X" => Unit×(V×Bool)

/-- The entire normalized N-minus-uncut-K field on the same held configuration. -/
def ReadingAt {N per f K requested power t:ℕ} {B:ℝ} {fk:f≤K} {cut:K≤N}
    (A:Panel R grades N per f K fk cut requested power t B) {j:ℕ} (held:j≤f)
    (W:Config G ((C).side j per)):Prop:=
  ∀s:(Stock.census V).Mode,
    let high:=Raw R grades A s
    let low:=Guard R grades A s
    let road:=held.trans fk
    let read:=actualTransport (C) (N:=N) (fun field=>actualTransport (C) (N:=N) high cut field-low field) road W
    read=actualTransport (C) (N:=N) high (road.trans cut) W-
      actualTransport (C) (N:=N) low road W ∧ ‖read‖≤((H f)^requested)⁻¹

theorem original {m N per j k₀ i:ℕ}(room:Room σ R simple)
    (faculty:Day σ R simple (WilsonMeasuredPublicEntranceFaculty.ask n D q).school m N)
    (opening:Opening R simple n D q m)(hardm:WilsonSingleHardRadius.first R simple ≤ m)
    (positive:∀x,m ≤ x → x ≤ N → 0<regulatorRun (C) N per x ∧ regulatorRun (C) N per x ≤ 1)
    (strips:∀x,((C).path.levels.params x).supportExponent=100)
    (degree target:ℕ)(mj:m+1 ≤ j)(height:j ≤ k₀+1)(fi:k₀+1 ≤ i)(upper:i+1 ≤ N) (cap:∀v,grades v ≤ D)(budget:0 ≤ B)
    (dates:Dates R grades simple pace nested cater forecast shop n apron requested t span power B degree target np size j)
    (geom:(C).S.a (k₀+1)/(C).S.a (i+1) ≤ (H (k₀+1))^span)
    (A:Panel R grades N per (k₀+1) (i+1) (Nat.le_succ_of_le fi) upper requested power t B)
    (entered:∀v,(WilsonMeasuredPublicEntrancePrescribedCampus.original R simple shop grades
      (accuracy grades requested)).choose ≤ A.slot v)
    (path:∀a,X→Site ((C).side a per))
    (big:5 ≤ ((C).path.rep N per (k₀+1)).p.B)
    (apart:∀v w:V,v≠w→((C).path.rep N per (k₀+1)).p.B^2+1 ≤ separation (A.loc v) (A.loc w))
    (ap:(C).S.a j/(C).S.a (k₀+1) ≤ (H (k₀+1))^apron)
    (start:path (k₀+1)=(A.loc∘Prod.fst)∘Prod.snd)
    (line:∀v,j ≤ v→v<k₀+1→path v=((C).path.levels.clock.op v per).ratio.parent ∘ path (v+1))
    :
    (∀W:Config G ((C).side j per),flags ((C).path.rep N per j).p.threshold W=∅ →
      WilsonOriginalMicroscopicEntranceHeldHalo.spring R j N per W≤2 → ReadingAt R grades A height W) ∧
    ∀M a,a∈tests ((C).labels.level degree) → ∀u≤M,
      ReadingAt R grades A height (WilsonCapturedPrimaryWeakTrialRadial.field R degree N per j target M a u):=by
  classical
  let school:=WilsonMeasuredPublicEntranceFaculty.ask n D q
  let reg:=WilsonMeasuredPublicEntranceFaculty.register (V:=V) room faculty per
  have upperF:k₀+1 ≤ i+1:=fi.trans (Nat.le_succ _)
  have older:j ≤ k₀+1:=by omega
  have fine:j ≤ i+1:=older.trans upperF
  have age:m ≤ i:=by omega
  let pin:=fun a=>((C).S.toDepth upperF per).embed (A.loc a)
  obtain ⟨P,_,_,_,_,_,_,_,_,_,_,_,_⟩:=
    WilsonMeasuredPublicEntranceRoomSale.original room n D q faculty grades size cap i (by omega) (by omega) pin
  have dim:=dimensions n D q grades size cap
  obtain ⟨after,sale,ready,radius,housing,safe,halo,meter,posted,radial,refs⟩:=dates
  obtain ⟨gate,tall⟩:=opening
  have rich:2 ≤ ((C).path.levels.budget j).supportExponent:=by
    rw [show ((C).path.levels.budget j).supportExponent=100 from strips j]
    norm_num
  have windows:=WilsonOriginalMicroscopicEntranceHeldMeshClock.original R older apron ap
  have paid:=WilsonOriginalMicroscopicEntranceHeldMaster.original R faculty.hk (roots σ R simple) (tab σ R simple)
    faculty.π faculty.Γ (faculty.Ψ per) room.books room.ahead grades school.school.order school.school.horizon
    school.school.pieces i age _ P upper (fun v=>(refs v _ le_rfl).trans fine) reg pace forecast k₀ fi
    (by omega) faculty.path room.pass room.month dim.2.2.1 school.school.tall q dim.1 dim.2.1
    (by norm_num:0<(1:ℝ)) le_rfl gate room.way room.ticket positive span power B budget (after.trans older)
    geom (strips _) (sale.trans older) (tall.trans (R.alloy.B.a.fits.mono (by omega)))
    nested cater shop n apron requested t j np size (allowance apron)
    (WilsonMeasuredPublicEntranceMeshClock.nonneg apron) ready height (allowance apron) 2
    (WilsonMeasuredPublicEntranceMeshClock.nonneg apron) (by norm_num) (by omega) housing windows.1
    (faculty.seen per).2.1 (safe.trans fine) (halo.trans fine)
    (meter.trans older) A.slot A.target A.tuition A.M A.nonneg A.priced A.before A.names A.axis A.sensors
    A.stamps A.home A.enrolled (fun v b low=>(refs v b low).trans older) A.turn A.loc path
  have final:=paid entered (posted.trans older) A.fixed (strips _) big apart ap start line rich
    windows.2 A.filed (by omega) (hardm.trans (by omega))
  constructor
  · intro W clear spring s
    exact (final s).1 W clear spring
  · intro M a enrolled u used s
    exact (final s).2 degree target M (by norm_num) radial a enrolled u used

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterRead
end
