import YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterRead
import YM.Integration.WilsonAddressedCollarWindow

/-! The original funded course supplies one faculty for every cutoff; the numerical onset and
all original radial directions precede the ultraviolet and volume regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterUpper
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
open WilsonOriginalMicroscopicEntranceHeldMasterRead (ReadingAt)
open Push.Local WilsonCoeffUV.Embroider
open WilsonMeasuredPublicEntranceMeshClock (allowance)
open WilsonWindowUniversalSchool

open WilsonInvariantActionPosition (berth)

open WilsonMeasuredPublicEntranceMasterRead (Opening)
universe u
variable {G:Gauge}(R:Run G)(simple:G.Simple)
  (pace:WilsonWindowReportingPace.Slow R.kit)
  (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater R.family R.doors)
  (forecast:WilsonReportLampForecast.Ready R.family.path.levels)(shop:RG05Preconstruction.ReadoutPurchase R.b)
local notation "C" => R.family
local notation "H" f:max => R.family.path.levels.clock.hatBeta f
variable {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)

/-- Both inputs are paid before the ultraviolet cutoff, the period and the measured fields. -/
def threshold (n apron requested t reserve power degree target:ℕ)(B:ℝ)(np:0<n)(size:Fintype.card V ≤ n):ℕ:=
  max (eventually_atTop.mp (WilsonOriginalMicroscopicEntranceHeldAppointments.original R grades simple pace
    nested cater forecast shop n apron requested t (reserve+1) power B degree target np size)).choose
    (eventually_atTop.mp (WilsonAddressedCollarWindow.original R simple pace reserve (η:=1) zero_lt_one)).choose

def ReadAt (m N per apron requested t reserve power degree target:ℕ)(B:ℝ)(first:ℕ):Prop:=
  ∀j f K,m+1≤j → first≤j → ∀jf:j≤f, K=berth R reserve f → ∀(fk:f≤K)(cut:K≤N)
    (A:Panel R grades N per f K fk cut requested power t B),
    (∀v,first≤A.slot v) → ∀path:(∀a,Unit×(V×Bool)→Site ((C).side a per)),
    5≤((C).path.rep N per f).p.B →
    (∀v w:V,v≠w→((C).path.rep N per f).p.B^2+1≤ separation (A.loc v) (A.loc w)) →
    (C).S.a j/(C).S.a f≤(H f)^apron →
    path f=(A.loc∘Prod.fst)∘Prod.snd →
    (∀a,j≤a→a<f→path a=((C).path.levels.clock.op a per).ratio.parent ∘ path (a+1)) →
    (∀W:Config G ((C).side j per),flags ((C).path.rep N per j).p.threshold W=∅ →
      WilsonOriginalMicroscopicEntranceHeldHalo.spring R j N per W≤2 → ReadingAt R grades A jf W) ∧
    ∀M a,a∈tests ((C).labels.level degree) → ∀u≤M,
      ReadingAt R grades A jf (WilsonCapturedPrimaryWeakTrialRadial.field R degree N per j target M a u)

theorem received {σ:WilsonOriginalAllOrderCourse.Schedule G}{m N per:ℕ}(room:Room σ R simple)
    (n D q:ℕ)(faculty:Day σ R simple (WilsonMeasuredPublicEntranceFaculty.ask n D q).school m N)
    (opening:Opening R simple n D q m)(hardm:WilsonSingleHardRadius.first R simple ≤ m)
    (positive:∀x,m ≤ x → x ≤ N → 0<regulatorRun (C) N per x ∧ regulatorRun (C) N per x ≤ 1)
    (strips:∀x,((C).path.levels.params x).supportExponent=100)
    (apron requested t reserve power degree target:ℕ)(B:ℝ)(np:0<n)(size:Fintype.card V ≤ n)(cap:∀v,grades v ≤ D)(budget:0 ≤ B):
    ReadAt R grades m N per apron requested t reserve power degree target B
      (threshold R simple pace nested cater forecast shop grades n apron requested t reserve power degree target B np size):=by
  classical
  let held:=eventually_atTop.mp (WilsonOriginalMicroscopicEntranceHeldAppointments.original R grades simple pace nested
    cater forecast shop n apron requested t (reserve+1) power B degree target np size)
  let flight:=eventually_atTop.mp (WilsonAddressedCollarWindow.original R simple pace reserve (η:=1) zero_lt_one)
  let first:=threshold R simple pace nested cater forecast shop grades n apron requested t reserve power degree target B np size
  have date:held.choose ≤ first:=le_max_left ..
  have staff:flight.choose ≤ first:=le_max_right ..
  obtain ⟨_,_,_,_,_,_,_,_,posted,_⟩:=held.choose_spec first date
  intro j f K mj start jf curve fk cut A slots path big apart ap initial line
  have clock:=flight.choose_spec f ((staff.trans start).trans jf)
  have up:f<K:=curve ▸ clock.1
  have geom:(C).S.a f/(C).S.a K ≤ (H f)^(reserve+1):=by
    rw [curve,pow_succ]
    simpa only [Real.rpow_one] using clock.2.2
  obtain ⟨k₀,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:f≠0)
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:K≠0)
  exact WilsonOriginalMicroscopicEntranceHeldMasterRead.original R simple grades pace nested cater forecast shop n D q
    apron requested t (reserve+1) power B np size room faculty opening hardm positive strips degree target mj jf
    (by omega) cut cap budget (held.choose_spec j (date.trans start)) geom A (fun v=>posted.trans (slots v))
    path big apart ap initial line

theorem original {σ:WilsonOriginalAllOrderCourse.Schedule G}{a:Axis}{ε:ℝ}{T:Campaign R}{W:Campaign.Pillars R T}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε σ R T W):
    ∃room:Room σ R simple,∀n D q:ℕ,∀ᶠ m:ℕ in atTop,∀N,m ≤ N → ∃faculty:
      Day σ R simple (WilsonMeasuredPublicEntranceFaculty.ask n D q).school m N,
      (∀per i,m ≤ i → i ≤ N → (faculty.Ψ per i).p.supportExponent=100) ∧
      (∀(V:Type)[Fintype V][DecidableEq V] (per:ℕ),Nonempty
        (WilsonReceivedFirstTrace.Registration (m:=m) (N:=N) (k:=(WilsonMeasuredPublicEntranceFaculty.ask n D q).vac)
        R (roots σ R simple) (tab σ R simple) faculty.π faculty.Γ (faculty.Ψ per) room.books room.ahead
          (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonMeasuredPublicEntranceFaculty.ask n D q).school.horizon
          (WilsonMeasuredPublicEntranceFaculty.ask n D q).school.pieces)) ∧
      ∀(V:Type)[Fintype V][DecidableEq V] (grades:V→ℕ)(np:0<n)(size:Fintype.card V ≤ n),
        (∀v,grades v ≤ D) → ∀(apron requested t reserve power degree target:ℕ)(B:ℝ),0 ≤ B → ∀per,
        ReadAt R grades m N per apron requested t reserve power degree target B
          (threshold R simple pace nested cater forecast shop grades n apron requested t reserve power degree target B np size):=by
  obtain ⟨room,office⟩:=WilsonMeasuredPublicEntranceFaculty.original paid
  refine ⟨room,?_⟩
  intro n D q
  filter_upwards [office n D q,eventually_ge_atTop (WilsonSingleHardRadius.first R simple)]
    with m issued hardm
  obtain ⟨gate,tall,school⟩:=issued
  intro N active
  obtain ⟨faculty,positive,walls,strips,roster⟩:=school N active
  refine ⟨faculty,walls,roster,?_⟩
  intro V _ _ grades np size cap apron requested t reserve power degree target B budget per
  exact received R simple pace nested cater forecast shop grades room n D q faculty ⟨gate,tall⟩ hardm
    (positive per) strips apron requested t reserve power degree target B np size cap budget


end YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterUpper
end
