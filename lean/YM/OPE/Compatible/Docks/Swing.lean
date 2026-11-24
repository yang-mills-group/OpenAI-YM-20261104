import YM.OPE.Compatible.Docks.Weeps
/-!
# Earn inverse right with budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open Drift
open scoped Topology BigOperators Classical ContDiff
variable {I E F J X:Type}{k:ℕ} {f:Filter I}{β p:I→ℝ}{s:ℝ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup J][NormedSpace ℝ J]
lemma Lapμ (v:I→E→L[ℝ] F)(w:I→F→L[ℝ] X)(h:Wax β f v s)(hp:Wax β f w 0): Wax β f (fun i=> w i ∘L v i) s:=by simpa only [zero_add] using Paintζ w h _ hp -- F type overlap beware
lemma doubleDiff (A B:E→L[ℝ]F):doublet (A-B)=doublet A-doublet B:=by exact ContinuousLinearMap.ext fun p=>rfl
local notation "ιZ"=> Wax β f
-- model eval gain
lemma Poke (v:I→ E→L[ℝ] (F×F))(u w z:I→F→L[ℝ] X)(hp:Tendsto β f atTop)(hV:ιZ v 0)(hW:ιZ w 0)(hZ:ιZ z 0)(hs:s ≤0)(hx:ιZ p s) : ιZ (fun i=>doublet (u i + p i • w i + p i ^ 2 • z i)∘L v i-doublet (u i) ∘L v i) s:=by
        let a(i):= u i + p i • w i+p i^2 • z i
        have hz:ιZ (fun i=>a i-u i) s:=by simp_rw [a,add_assoc,add_sub_cancel_left]; exact ( (hx.smul hW).mono (by rw [add_zero])).add (((hx.pow 2 (carth hp)).smul hZ).mono (by push_cast;linarith)) (carth hp)
        have he:= (Paintζ (fun i=>doublet (a i-u i)) hV s (twins hz)).mono (show s+0 ≤ s by simp); exact he.congr (Eventually.of_forall fun i=>by dsimp only;rw [doubleDiff]; exact ContinuousLinearMap.sub_comp ..)
-- route inverse propagation
lemma opticsα (u:I→ E→L[ℝ] (F×F))(v:I→ F→L[ℝ] X)(t:I→ X→L[ℝ] F)(A:I→ (F×F) →L[ℝ] E) (h:Wax β f t 0)(hp:Wax β f A 0)(hx:∀ᶠ i in f,u i∘L A i=ContinuousLinearMap.id ..)(hv:∀ i x,v i (t i x)=x): ∃ V:I→(X×X)→L[ℝ] E, Wax β f V 0 ∧ ∀ᶠ i in f,(doublet (v i) ∘L u i) ∘L V i= ContinuousLinearMap.id ..:=by
       let a(i):= A i ∘L doublet (t i); refine ⟨a,Lapμ _ _ (twins h) hp,?_⟩; filter_upwards [hx] with i hi; apply ContinuousLinearMap.ext; rintro ⟨x,y⟩; change doublet _ ((u i ∘L A i) (doublet _ _))=_; rw [hi]; exact Prod.ext (hv i x) (hv i y)
end
end YM.OPE.Yolk
