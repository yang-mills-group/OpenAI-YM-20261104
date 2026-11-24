import YM.Integration.WilsonPositionScaleLawColorInverse

/-! A single member of the actual bounded Born set fixes its unique reciprocal
before the named position bank, independent MS data, scale and Taylor order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorCandidate
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land FVA2 FVA2.Arrival
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPositionScaleLawColorInverse (inverse)
open WilsonPositionScaleLawColorPrinted (diagnostic painted)
open WilsonPositionScaleLawColorChart (conjugate)
open WilsonPositionScaleLawColorMeasured (bank)
open WilsonPositionPrescribedFormalTest (raw turn)
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J){d:ℕ}
local notation "N" => MoveSpace G d

def Quote (a b:N)(V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (q:ℕ)(P:ℝ→Prediction G d):Prop:=
    ∃ L A η:ℝ,0≤L ∧ 0≤A ∧ 0<η ∧ ∀ᶠr in trail,∀t:ℝ,|t|<η→∀x:N,‖x‖<η→
    ‖conjugate a b x-guide G d (turn V ν T d q t)‖≤
      L*‖diagnostic V (recruit (field x ∘ₗ field a) (P t))-bank F J V r‖+A*|t|^(q+1)

include lead in
theorem original {B:ℝ}(a:N)(chosen:a∈possible C d B):
    ∃b∈possible C d B,field a ∘ₗ field b=1 ∧ field b ∘ₗ field a=1 ∧
      ∀(V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(q:ℕ),
      Quote F J a b V ν T q (fun t=>painted b (raw ν T d q t)) ∧
      ((∀k≤q,painted b (Reg.State.kernel ν T d k)=Reg.State.kernel ν T d k)→Quote F J a b V ν T q (raw ν T d q)):=by
  let h:=WilsonPositionScaleLawColorInverse.inject C chosen
  let b:=inverse a h
  obtain ⟨ab,ba⟩:=WilsonPositionScaleLawColorInverse.both a h
  refine ⟨b,WilsonPositionScaleLawColorInverse.selected C chosen,ab,ba,?_⟩
  intro V ν T q
  exact ⟨WilsonPositionScaleLawColorMeasured.original F J lead V ν T q a b ab ba,
    WilsonPositionScaleLawColorMeasured.independent F J lead V ν T q a b ab ba⟩

end YM.Integration.WilsonPositionScaleLawColorCandidate
end
