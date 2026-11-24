import YM.OPE.Compatible.Kiwi.Tail
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
/-! # Oriented paths.Lct.Headwards. negative links taken explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Prairies Woody
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} {a:Axis}
open YM.AnalyticNext.QuarticMatch.Joint
variable (a)
abbrev Wm := Signed.mirror a
abbrev streak (G:Gauge)(n:Side):Bid.Dir G n→L[ℝ] Bid.Dir G n:=shifts (Wm a) (0:Site n)
lemma siglim (x:Site N):wrap N ((Wm a).act (lift x))=(Wm a).act x:=by rw [←wrap_signed,wrap_lift]
lemma ζFlags : Wm a * Wm a=1:= inv_mul_cancel (Wm a)
variable {R:Type*}[AddCommGroup R][One R]
def dust (i:Axis): Axis→ R:=if i=a then -step i else 0
omit [One R] in
lemma run_axis (p:Axis→R)(t:Axis): (Wm a).act p t= if t=a then -p t else p t:=by
    have ht:= Signed.act_at (Wm a) p t; simp [Wm,Signed.mirror,eq_comm] at *; exact ht
lemma norm_step (i:Axis)(p:Axis→R): (Wm a).act (p+step i)= (Wm a).act p+ (if i=a then -step i else step i):=by rw [(Wm a).act_add, ← Step.vec_pos (i:=i),←Step.vec_rotate]; by_cases h:i=a <;>simp [Wm,Step.rotate,Signed.mirror,posDir,Step.vec,h,eq_comm (a:=a)]
lemma errand (i:Axis)(p:Site N): sendEdge (Wm a) (0:Site N) (p,i)= ((Wm a).act p+dust a i,i):=by
   unfold sendEdge Step.used Step.rotate posDir affine dust; by_cases hi:i=a <;> simp [Wm,Signed.mirror,eq_comm (a:=a),hi,sub_eq_add_neg]
lemma facet (i:Axis): (Step.rotate (posDir i) (Wm a)).neg = decide (i=a):=by simp [Wm,Signed.mirror,Step.rotate,posDir,eq_comm]
lemma α_line (x:Bid.Dir G N) (p:Site N) (i:Axis):
    let z:= x ((Wm a).act p+dust a i, Exterior.coord i)
    streak a G N x (p,Exterior.coord i)= if i=a then -z else z:=by
     intro z; unfold streak shifts; rw [ContinuousLinearMap.pi_apply]; simp_rw [show Exterior.axisEquiv.symm (Exterior.coord i)=i from axisEquiv.symm_apply_apply _]; rw [show (Step.used _ _:Edge (Site N))= _ from errand a i p, facet]; unfold z; by_cases h:i=a<;>simp only [h,if_true,decide_true,if_false,decide_false,Bool.false_eq_true] <;>rfl
lemma η_line (x:Links (Per N) G.El)(p:Site N)(i:Axis): Lattice.pull (Wm a) (0:Site N) x (p,i)= if i=a then (x ((Wm a).act p+dust a i,i))⁻¹ else x ((Wm a).act p+dust a i,i):=by
    change (if (Step.rotate (posDir i) (Wm a)).neg then _ else _) = _; -- Step.read
    rw [show (Step.used _ _:Edge (Site N))=_ from errand a i p,facet]; split_ifs<;>simp_all
lemma offsets (x:Axis→R)(i:Axis): (Wm a).act ((Wm a).act x+dust a i) + dust a i=x:=by
    rw [(Wm a).act_add,← Signed.act_mul,ζFlags, Signed.act_one,add_assoc,show (Wm a).act (dust a i)+dust a i=(0:Axis→R) from ?_,add_zero]; unfold dust; split_ifs with h; simp_rw [Signed.act_neg]; rw [show (Wm a).act (step i)= (-step i:Axis→R) from (by simpa [h] using! norm_step a i (0:Axis→R)), neg_neg,add_neg_cancel]; simp
lemma sigma_twice (x:Bid.Dir G N):streak a G N (streak a G N x)=x:=by
    ext1 i; rcases i with ⟨v,p⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective p; change streak a G _ _ (v,Exterior.coord j)= _; simp_rw [α_line,offsets]; split <;> simp
end YM.OPE.Quit
