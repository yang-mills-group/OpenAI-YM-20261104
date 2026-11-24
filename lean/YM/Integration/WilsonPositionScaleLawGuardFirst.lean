import YM.Integration.WilsonPositionScaleLawGuardInvoice

/-! The genuine independent homogeneous scale starts at the identity with
vanishing linear term on the complete retained field at every grade. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardFirst
open Spec Table Extraction OPE OPE.Orbits PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawGuardLift (pack)
open WilsonPositionScaleLawDressedTransport (guard)
open WilsonPositionScaleLawGuardSheet (atValue)
open scoped Topology Polynomial Classical BigOperators

theorem printed {R:Type*}[NormedRing R][NormedAlgebra ℂ R](a:PowerSeries R)
    (h₀:coeff 0 a=1)(h₁:coeff 1 a=0)(z:ℂ):atValue 1 a z=1:=by
  rw [atValue,WilsonPositionScaleLawGuardEval.printed (R:=R) 1 a z,show Finset.Iic (1:ℕ)=({0,1}:Finset ℕ) by decide]
  simp [h₀,h₁]

variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

include H in
theorem original (s:ℝ)(d:ℕ)(z:ℂ):atValue 1 (pack C (guard Z M ν s d)) z=1:=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base:coeff 0 (guard Z M ν s d)=1:=(GroupS.true_N ν Z.scheme Z.criterion M σ hG data.Taylor data.still data.base s).zero
  have linear:coeff 1 (guard Z M ν s d)=0:=
    Generator.Q.lifted ν Z.scheme Z.criterion M σ s hG data.Taylor data.still data.base
  apply printed
  · rw [WilsonPositionScaleLawGuardLift.pack,PowerSeries.coeff_map,base,map_one]
  · rw [WilsonPositionScaleLawGuardLift.pack,PowerSeries.coeff_map,linear,map_zero]

end YM.Integration.WilsonPositionScaleLawGuardFirst
