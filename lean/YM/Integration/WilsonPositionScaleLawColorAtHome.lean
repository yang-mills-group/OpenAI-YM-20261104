import YM.Integration.WilsonPositionScaleLawColorCandidate

/-! The stored cutoff-side invoice is the actual, fully calibrated physical
moment on every test and all insertion legs at the single original home. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorAtHome
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land FVA2 FVA2.Arrival
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPositionScaleLawColorPrinted (diagnostic painted)
open WilsonPositionScaleLawColorChart (conjugate)
open WilsonPositionScaleLawColorMeasured (bank)
open WilsonPositionPrescribedFormalTest (raw turn)
open WilsonPositionPrescribedScreen (hierarchy correction actual)
open WilsonPositionPrescribedFrame (leg change positioned)
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J){d:ℕ}
local notation "N" => MoveSpace G d

include lead in
theorem measured (V:Store G)(d:ℕ):∀ᶠr in trail,
    hierarchy F (positioned F J V) d r=recruit (stand (correction F J V d r)) (hierarchy F J d r):=
  WilsonPositionPrescribedFrame.measured F J V lead d

def Quote (a b:N)(V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (q:ℕ)(P:ℝ→Prediction G d):Prop:=
    ∃ L A η:ℝ,0≤L ∧ 0≤A ∧ 0<η ∧ ∀ᶠr in trail,∀t:ℝ,|t|<η→∀x:N,‖x‖<η→
    ‖conjugate a b x-guide G d (turn V ν T d q t)‖≤
      L*‖diagnostic V (recruit (field x ∘ₗ field a) (P t))-diagnostic V (hierarchy F (positioned F J V) d r)‖+A*|t|^(q+1)

include lead in
theorem genuine (a b:N)(V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(q:ℕ)(P:ℝ→Prediction G d)
    (h:WilsonPositionScaleLawColorCandidate.Quote F J a b V ν T q P):Quote F J a b V ν T q P:=by
  obtain ⟨L,A,η,hL,hA,hη,quote⟩:=h
  refine ⟨L,A,η,hL,hA,hη,?_⟩
  filter_upwards [quote,measured F J lead V d] with r cost trueHome t ht x hx
  rw [trueHome];exact cost t ht x hx

include lead in
theorem original {B:ℝ}(a:N)(chosen:a∈possible C d B):
    ∃b∈possible C d B,field a ∘ₗ field b=1 ∧ field b ∘ₗ field a=1 ∧
      ∀(V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(q:ℕ),
      Quote F J a b V ν T q (fun t=>painted b (raw ν T d q t)) ∧
      ((∀k≤q,painted b (Reg.State.kernel ν T d k)=Reg.State.kernel ν T d k)→Quote F J a b V ν T q (raw ν T d q)):=by
  obtain ⟨b,selected,ab,ba,quoted⟩:=WilsonPositionScaleLawColorCandidate.original F J lead a chosen
  refine ⟨b,selected,ab,ba,?_⟩;intro V ν T q
  have h:=quoted V ν T q
  exact ⟨genuine F J lead a b V ν T q _ h.1,fun same=>genuine F J lead a b V ν T q _ (h.2 same)⟩

end YM.Integration.WilsonPositionScaleLawColorAtHome
end
