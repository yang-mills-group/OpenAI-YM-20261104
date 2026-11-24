import YM.Integration.WilsonPositionScaleLawGuardCoordinates
import YM.Integration.WilsonPositionScaleLawGuardWindow
import YM.Integration.WilsonPositionScaleLawGuardInvoice

/-! The native independent scalar, position and homogeneous coefficients
vary continuously in the original physical norm on every bounded scale panel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBanks
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardLift (act pack)
open WilsonPositionScaleLawIndependent (time continuousTime B)
open WilsonPositionScaleLawDressedTransport (guard)
open scoped Topology Polynomial Classical BigOperators
variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem scalar (k:ℕ):Continuous (fun t:Ratio=>coeff k (GroupS.ψ Z.criterion M ν (WilsonPositionScaleLawIndependent.time t))):=
  (continuous_iff_continuousAt.mpr fun s=>((H.details.normative ν).check.coupling s k).continuousAt).comp continuousTime

include H in
theorem position (d k:ℕ):Continuous (fun t:Ratio=>coeff k (WilsonPositionScaleLawGuardLift.pack C (B Z M ν (WilsonPositionScaleLawIndependent.time t) d))):=by
  apply WilsonPositionScaleLawGuardCoordinates.operator
  intro v l
  let row:Module.Dual ℂ (FieldEnd G d):={
    toFun:=fun a=>l ((act C d a) v)
    map_add':=fun a b=>by rw [map_add];change l ((act C d a) v+(act C d b) v)=_;rw [map_add]
    map_smul':=fun z a=>by rw [map_smul];change l (z • (act C d a) v)=_;rw [map_smul];rfl}
  apply ((WilsonPositionScaleLawIndependent.coefficient Z M H ν d k row).comp continuousTime).congr
  intro t;rw [WilsonPositionScaleLawGuardLift.coefficient];rfl

include H in
theorem homogeneous (d k:ℕ):Continuous (fun t:Ratio=>coeff k (WilsonPositionScaleLawGuardLift.pack C (WilsonPositionScaleLawDressedTransport.guard Z M ν (WilsonPositionScaleLawIndependent.time t) d))):=by
  apply WilsonPositionScaleLawGuardCoordinates.operator
  intro v l
  let row:Module.Dual ℂ (Sec G d):=l.comp (fields C.labels d).symm.toLinearMap
  let paid:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have series:Meter.Tracks (fun s=>WilsonPositionScaleLawDressedTransport.guard Z M ν s d) k:=
    (Precise.mainN ν Z.scheme Z.criterion M σ hG paid.Taylor paid.still paid.base).proper d k
  obtain ⟨j,p,_,he⟩:=series ((fields C.labels d) v) row
  have c:Continuous (fun s=>row (coeff k (WilsonPositionScaleLawDressedTransport.guard Z M ν s d) ((fields C.labels d) v))):=by
    rw [he];exact p.continuous.comp Complex.continuous_ofReal
  apply (c.comp continuousTime).congr
  intro t;rw [WilsonPositionScaleLawGuardLift.coefficient];rfl

theorem bounded {V:Type*}[NormedAddCommGroup V](q:ℕ)(a:ℕ→Ratio→V)(ready:∀k,Continuous (a k)):
    ∃C:ℝ,0≤C ∧ ∀t,∀k≤q,‖a k t‖≤C:=by
  have bnd(k:Fin (q+1)):∃C:ℝ,0≤C ∧ ∀t:Ratio,‖a k.val t‖≤C:=by
    obtain ⟨A,hA⟩:=isCompact_univ.bddAbove_image (ready k.val).norm.continuousOn
    exact ⟨max A 0,le_max_right _ _,fun t=>(hA ⟨t,mem_univ _,rfl⟩).trans (le_max_left _ _)⟩
  choose C hC h using bnd
  exact ⟨∑j,C j,Finset.sum_nonneg (fun j _=>hC j),fun t k hk=>(h ⟨k,by omega⟩ t).trans
    (Finset.single_le_sum (fun j _=>hC j) (Finset.mem_univ _))⟩

end YM.Integration.WilsonPositionScaleLawGuardBanks
