import YM.Integration.WilsonPositionScaleLawGuardBanks
import YM.Integration.WilsonPositionScaleLawGuardTurning

/-! Full compact-ratio price of the finite numerical invoice from the nominated MS coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardPrice
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

theorem issued {V:Type*}[NormedRing V](q:ℕ)(a:Ratio→PowerSeries V)
    (ha:∀k,Continuous (fun t=>coeff k (a t))):WilsonPositionScaleLawGuardStock.Stock (fun t=>trunc (q+1) (a t)):=by
  obtain ⟨B,hB,ready⟩:=WilsonPositionScaleLawGuardBanks.bounded q (fun k t=>coeff k (a t)) ha
  exact WilsonPositionScaleLawGuardStock.printed q _ hB ready

include H in
theorem original (d q:ℕ):∃T:ℝ,0≤T ∧ ∀t:Ratio,WilsonPositionScaleLawGuardSheet.total
    (WilsonPositionScaleLawGuardInvoice.sheet C Z M ν t d) q≤T:=by
  let p(t:Ratio):=GroupS.ψ Z.criterion M ν (WilsonPositionScaleLawIndependent.time t)
  let A:=WilsonPositionScaleLawDressedTransport.adjust Z d
  let turned(t:Ratio):=WilsonPositionScaleLawGuardLift.pack C (convertT (WilsonPositionScaleLawIndependent.time t) A)
  let N(t:Ratio):=WilsonPositionScaleLawGuardLift.pack C (WilsonPositionScaleLawDressedTransport.guard Z M ν (WilsonPositionScaleLawIndependent.time t) d)
  let B(t:Ratio):=WilsonPositionScaleLawGuardLift.pack C (WilsonPositionScaleLawIndependent.B Z M ν (WilsonPositionScaleLawIndependent.time t) d)
  obtain ⟨T,hT,price⟩:=WilsonPositionScaleLawGuardWindow.original q p (WilsonPositionScaleLawGuardLift.pack C A) turned N B
    (issued q p (WilsonPositionScaleLawGuardBanks.scalar Z M H ν)) (WilsonPositionScaleLawGuardTurning.printed C q A)
    (issued q N (WilsonPositionScaleLawGuardBanks.homogeneous C Z M H ν d))
    (issued q B (WilsonPositionScaleLawGuardBanks.position C Z M H ν d))
  exact ⟨T,hT,price⟩

end YM.Integration.WilsonPositionScaleLawGuardPrice
