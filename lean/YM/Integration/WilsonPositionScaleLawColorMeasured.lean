import YM.Integration.WilsonPositionScaleLawColorPrinted
import YM.Integration.WilsonPositionScaleLawHome

/-! Numerical uniqueness relative to the true position equations on the chosen
physical home. Radius, constants, MS data and color convention precede all trial coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorMeasured
open Function Filter Set Asymptotics Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land FVA2 FVA2.Arrival
open WilsonPositionPrescribedFormalTest (raw turn)
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPositionScaleLawColorChart (conjugate)
open WilsonPositionScaleLawColorPrinted (painted diagnostic)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPositionPrescribedScreen (correction)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(V:Store G)(ν:ℝ)
    (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){d:ℕ}(q:ℕ)
local notation "N" => MoveSpace G d

def bank (r:ℝ):N:=diagnostic V (recruit (stand (correction F J V d r)) (hierarchy F J d r))

include lead in
theorem original (a b:N)(inv:field a ∘ₗ field b=1)(back:field b ∘ₗ field a=1):
    ∃ L A η:ℝ,0≤L ∧ 0≤A ∧ 0<η ∧ ∀ᶠr in trail,∀t:ℝ,|t|<η→∀x:N,‖x‖<η→
    ‖conjugate a b x-guide G d (turn V ν T d q t)‖≤
      L*‖diagnostic V (recruit (field x ∘ₗ field a) (painted b (raw ν T d q t)))-bank F J V r‖+A*|t|^(q+1):=by
  obtain ⟨L,A,hL,hA,fit⟩:=WilsonPositionScaleLawColorPrinted.bill V ν T q a b inv back
  obtain ⟨η,hη,room⟩:=Metric.mem_nhds_iff.mp fit
  refine ⟨L,A,η,hL,hA,hη,?_⟩
  filter_upwards [(WilsonPositionPrescribedScreen.original F J lead V d).2] with r calibrated t ht x hx
  have small:(t,x)∈Metric.ball (0,0) η:=by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right,Real.norm_eq_abs,max_lt_iff] using And.intro ht hx
  have invoice:=room small
  rw [show bank F J V r=diagnostic V (reference G d) from congrArg (guide G d) calibrated.1]
  exact invoice

include lead in
theorem independent (a b:N)(inv:field a ∘ₗ field b=1)(back:field b ∘ₗ field a=1)
    (same:∀k≤q,painted b (Reg.State.kernel ν T d k)=Reg.State.kernel ν T d k):
    ∃ L A η:ℝ,0≤L ∧ 0≤A ∧ 0<η ∧ ∀ᶠr in trail,∀t:ℝ,|t|<η→∀x:N,‖x‖<η→
    ‖conjugate a b x-guide G d (turn V ν T d q t)‖≤
      L*‖diagnostic V (recruit (field x ∘ₗ field a) (raw ν T d q t))-bank F J V r‖+A*|t|^(q+1):=by
  obtain ⟨L,A,η,hL,hA,hη,invoice⟩:=original F J lead V ν T q a b inv back
  refine ⟨L,A,η,hL,hA,hη,?_⟩
  filter_upwards [invoice] with r bound t ht x hx
  simpa only [WilsonPositionScaleLawColorPrinted.invariant ν T q b same] using bound t ht x hx

end YM.Integration.WilsonPositionScaleLawColorMeasured
end
