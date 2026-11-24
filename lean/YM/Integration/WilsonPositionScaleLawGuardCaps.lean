import YM.Integration.WilsonPositionScaleLawGuardPrice
import YM.Integration.WilsonPositionScaleLawGuardValue

/-! One compact bound for the whole nominated numerical MS sheet, including
the grounded clock at zero, both field polynomials and the finite overflow. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardCaps
open Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardSheet (Book atValue total)
open WilsonPositionScaleLawGuardInvoice (sheet)
open scoped Topology Polynomial Classical BigOperators

structure Prices {X:Type*}[NormedRing X][NormedAlgebra ℂ X](p:Ratio→Book X)(q:ℕ)(L:ℝ):Prop where
  one:1≤L
  position(t:Ratio)(z:ℂ)(hz:‖z‖≤1):‖atValue q (p t).position z‖≤L
  homogeneous(t:Ratio)(z:ℂ)(hz:‖z‖≤1):‖atValue q (p t).homogeneous z‖≤L
  clock(t:Ratio)(z:ℂ)(hz:‖z‖≤1):‖(trunc (q+1) (p t).scalar).eval z‖≤L*‖z‖
  fringe(t:Ratio):total (p t) q≤L

variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem original (d q:ℕ):∃L:ℝ,Prices (fun t=>sheet C Z M ν t d) q L:=by
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  let p(t:Ratio):=sheet C Z M ν t d
  obtain ⟨B,_,hb⟩:=WilsonPositionScaleLawGuardBanks.bounded q (fun k t=>coeff k (p t).position) (WilsonPositionScaleLawGuardBanks.position C Z M H ν d)
  obtain ⟨N,_,hn⟩:=WilsonPositionScaleLawGuardBanks.bounded q (fun k t=>coeff k (p t).homogeneous) (WilsonPositionScaleLawGuardBanks.homogeneous C Z M H ν d)
  obtain ⟨S,hS,hs⟩:=WilsonPositionScaleLawGuardBanks.bounded q (fun k t=>coeff k (p t).scalar) (WilsonPositionScaleLawGuardBanks.scalar Z M H ν)
  obtain ⟨T,_,ht⟩:=WilsonPositionScaleLawGuardPrice.original C Z M H ν d q
  let b:=((q+1:ℕ):ℝ)*B
  let n:=((q+1:ℕ):ℝ)*N
  let s:=((q+1:ℕ):ℝ)*((q:ℝ)*S)
  let L:=max 1 (max b (max n (max s T)))
  have Bcap:b≤L:=(le_max_left _ _).trans (le_max_right _ _)
  have Ncap:n≤L:=(le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have Scap:s≤L:=(le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have Tcap:T≤L:=(le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨L,le_max_left _ _,fun t z hz=>(WilsonPositionScaleLawGuardValue.original q _ (hb t) hz).trans Bcap,
    fun t z hz=>(WilsonPositionScaleLawGuardValue.original q _ (hn t) hz).trans Ncap,?_,fun t=>(ht t).trans Tcap⟩
  intro t z hz
  have root:coeff 0 (p t).scalar=0:=((H.details.normative ν).first.led (WilsonPositionScaleLawIndependent.time t)).start
  exact (WilsonPositionScaleLawGuardValue.scalar q _ root hS (hs t) hz).trans (mul_le_mul_of_nonneg_right Scap (norm_nonneg _))

end YM.Integration.WilsonPositionScaleLawGuardCaps
