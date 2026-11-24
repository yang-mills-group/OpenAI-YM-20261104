import YM.FVA2.ThePitch
import YM.JointConstruction.LocalForced
/-!
# install on the common QuadraticLocal family

 This is not an identification of actual coefficients with their (quotient or
 otherwise) perturbative series. Theorem contains the common supplying witnesses
 for those remaining analytic estimates, for the consumer using the referred
 `LocalTaylor_with_forcedInheritance`; includes all its hypotheses. The formal
 diagram estimates use the independent top prescription without replacing it by any approximate
 analytic *one*-step formula.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Atoll
open Source MergeProof
-- ensure not conflating theta r local ext
variable {G:Gauge} (h:G.Simple)
theorem alongside (κ:ℝ)(hκ:0<κ)(δ:PhysicalNext.Repeat.Daisy.Charity.RG12.Decal G)(F:Extraction.Order) : ∃ (C: Family G) (f:Extraction.Order)(T:Table C.book)(W:Spec.Final C (F.refine f) T)(L: EveryPhase.Almanac W)(A:UVExtension.Mast.Couture C h (LocalTaylorR2.Marigold.aetherD (LocalTaylorR2.Strange.jetEngine G) δ)), Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ∧ UVExtension.Oasis.Floral (hG:=h) C ∧
      ( Extraction.Order.mk Extraction.Sequence.full (F.refine f).per ).Ordered C T ∧ EveryPhase.Completed W L ∧ OPE.Facilities C ( F.refine f ) T ∧ LocalTaylorR2.Marigold.QuadPose ( LocalTaylorR2.Strange.jetEngine G ) A ∧ JointConstruction.ForcedStepControl C ∧ ∃ (hC: C.Makes)(hP:∀ i,Bid.pop ( C.localSection i )), Petition h (share C hC hP):= by
    obtain ⟨C,f,T,W,L,A,hC,hCal,hP,h',hT,hL,hF,ha,hA⟩:= JointConstruction.localTaylor_with_forcedInheritance h κ hκ δ F; exact ⟨ C,f,T,W,L,A,hCal,hP,h',hT,hL,hF,ha,hA,hC,everywhere h C hC h' ⟩
end YM.FVA2.Atoll
