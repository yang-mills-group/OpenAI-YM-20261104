import YM.Integration.WilsonMeasuredPublicEntrancePanel
import YM.Integration.WilsonMeasuredPublicEntranceRoomSale
import YM.Integration.WilsonMeasuredPublicEntranceAppointments
/-! The actual school admits the trial, carries its earlier signed Wilson reading, and pays on its previously chosen physical coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceMasterRead
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
open WilsonMeasuredPublicEntrancePanel WilsonMeasuredPublicEntranceAppointments
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

def Opening (m:ℕ):Prop:=
  let school:=WilsonMeasuredPublicEntranceFaculty.ask n D q
  let dim:=dimensions n D q (fun _:Fin 0=>0) (by simp) (by simp)
  WilsonReceivedMeasuredStampPrice.opening R simple q school.school.order school.vac dim.1 dim.2.1
    (by norm_num:0<(1:ℝ)) ≤ m+1 ∧ 6*school.school.pieces ≤ R.alloy.B.a.clock.J m

theorem original {m N per j k₀ i:ℕ}(room:Room σ R simple)
    (faculty:Day σ R simple (WilsonMeasuredPublicEntranceFaculty.ask n D q).school m N)
    (opening:Opening R simple n D q m)(refm:(C).ref 0 ≤ m)(hardm:WilsonSingleHardRadius.first R simple ≤ m)
    (positive:∀x,m ≤ x → x ≤ N → 0<regulatorRun (C) N per x ∧ regulatorRun (C) N per x ≤ 1)
    (strips:∀x,((C).path.levels.params x).supportExponent=100)
    (mj:m ≤ j)(height:j+2 ≤ k₀+1)(fi:k₀+1 ≤ i)(upper:i+1 ≤ N) (cap:∀v,grades v ≤ D)(budget:0 ≤ B)
    (dates:Dates R grades simple pace nested cater bank forecast shop n apron requested t span power B np size j)
    (geom:(C).S.a (k₀+1)/(C).S.a (i+1) ≤ (H (k₀+1))^span)
    (A:Panel R grades N per (k₀+1) (i+1) (Nat.le_succ_of_le fi) upper requested power t B)
    (entered:∀v,(WilsonMeasuredPublicEntrancePrescribedCampus.original R simple shop grades
      (accuracy grades requested)).choose ≤ A.slot v)
    (path:∀a,X→Site ((C).side a per))(anchor:X)
    (big:5 ≤ ((C).path.rep N per (k₀+1)).p.B)
    (apart:∀v w:V,v≠w→((C).path.rep N per (k₀+1)).p.B^2+1 ≤ separation (A.loc v) (A.loc w))
    (ap:(C).S.a j/(C).S.a (k₀+1) ≤ (H (k₀+1))^apron)
    (start:path (k₀+1)=(A.loc∘Prod.fst)∘Prod.snd)
    (line:∀v,j+1 ≤ v→v<k₀+1→path v=((C).path.levels.clock.op v per).ratio.parent ∘ path (v+1))
    (house:∀v,coverNumber (((C).path.rep N per (j+1)).p.B) ({path (j+1) anchor,path (j+1) v}:Support _) ≤ 1)
    (center:((C).path.levels.clock.op j per).ratio.parent (path (j+1) anchor)=0):
    ∀u,m ≤ u→∀uj:u ≤ j, Opened (C) 0 u per → Opened (C) 0 j per →
      Reading R grades A (uj.trans (by omega)):=by
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
  obtain ⟨after,sale,ready,radius,housing,safe,halo,meter,posted,refs⟩:=dates
  obtain ⟨gate,tall⟩:=opening
  have windows:=WilsonMeasuredPublicEntranceMeshClock.original R older apron ap
  have oldp:(faculty.Ψ per (j+1)).p.supportExponent ≤ 100:=by
    rw [((faculty.seen per).1.1.walk (j+1) (by omega) (by omega)).truep.point]
    exact (strips _).le
  have paid:=WilsonMeasuredPublicEntranceMaster.original R faculty.hk (roots σ R simple) (tab σ R simple)
    faculty.π faculty.Γ (faculty.Ψ per) room.books room.ahead grades school.school.order school.school.horizon
    school.school.pieces i age _ P upper (fun v=>(refs v _ le_rfl).trans fine) reg pace forecast k₀ fi
    (mj.trans older) faculty.path room.pass room.month dim.2.2.1 school.school.tall q dim.1 dim.2.1
    (by norm_num:0<(1:ℝ)) le_rfl gate room.way room.ticket positive span power B budget (after.trans older)
    geom (strips _) (sale.trans older) (tall.trans (R.alloy.B.a.fits.mono (mj.trans older)))
    nested cater bank shop n apron 1 requested t j 1 np size (allowance apron)
    (WilsonMeasuredPublicEntranceMeshClock.nonneg apron) ready height (allowance apron)
    (WilsonMeasuredPublicEntranceMeshClock.nonneg apron) (radius.trans (by omega))
    (housing.trans j.le_succ) windows.1 (faculty.seen per).2.1 (safe.trans fine) (halo.trans fine)
    (meter.trans older) A.slot A.target A.tuition A.M A.nonneg A.priced A.before A.names A.axis A.sensors
    A.stamps A.home A.enrolled (fun v b low=>(refs v b low).trans older) A.turn A.loc path anchor
  have final:=paid entered (posted.trans older) A.fixed (strips _) big apart ap le_rfl start line house
    center windows.2 oldp A.filed
  intro u mu uj ou oj
  exact final u mu (refm.trans mu) uj ou oj (hardm.trans mu)
end YM.Integration.WilsonMeasuredPublicEntranceMasterRead
end
