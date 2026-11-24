import YM.OPE.Compatible.Juniper.Post
import YM.Next.RANK.Carried
/-! # Physical stencil coincidence -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Lattice MeasureTheory RG Wilson Flume Flume.Page Flume.Script Gauge
open Source Next.Rank Next.Rank.Spindle
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(U:CoverConfig G)
lemma straightH (i:Axis)(v:Cover)(l:ℕ)(p:Bool)(ht:trunk v i): travel (central U) v (List.replicate l ((⟨i,p⟩:Step)))=1:=by
    induction l generalizing v with
    | zero=> rfl
    | succ l ih=>
         have hp : trunk (v+(⟨i,p⟩:Step).vec) i:=fun j h=>by cases p <;> simp only [Step.vec,↓reduceIte,Bool.false_eq_true,Pi.add_apply,Pi.neg_apply,ht j h,step_apply,if_neg (ne_of_gt h),neg_zero,zero_add] -- adjust
         rw [List.replicate_succ, travel,ih _ hp]; cases p
         · change central U (v,i)*_= _; simp [vertical U v i ht]
         change (central U (v-step i,i))⁻¹*_=_; simp_rw [vertical U (v-step i) i (show _ from ((show v-step i = v+(⟨i,true⟩:Step).vec from sub_eq_add_neg ..)|>.symm ▸ hp)),inv_one,mul_one] -- simplify
lemma routeS (x:Cover)(l:List Axis)(hl:l.Pairwise (·<·)): travel (central U) 0 (axisRoute 0 x l)=1:=by
     induction l using List.reverseRecOn with
     | nil=> rfl
     | append_singleton l i ih=>
          have hv:= List.pairwise_append.mp hl; have hp:l.Nodup:= hv.1.imp (fun h=> ne_of_lt h) -- proof
          rw [show axisRoute _ x (l++[i])=axisRoute 0 x l++straight i (x i) from ?_,travel_append,ih hv.1,one_mul]; swap; · simp [axisRoute]
          apply straightH; unfold trunk; intro j hj; rw[axisRoute_end _ _ _ l hp]; simp only [Pi.zero_apply,sub_zero,zero_add]; rw [if_neg]; intro h; have hh:= hv.2.2 j h i (List.mem_singleton.mpr rfl); exact hh.not_gt hj
lemma RoarU (x:Cover): Spindle.leaves U x= incG U x:=by
    have hh:= routeS U x (allAxes 1) (show _ from ?_)
    swap; · change List.Pairwise (·<·) ([0,1,2,3]:List (Fin 4)); decide
    unfold central at hh; erw [travel_gauge] at hh; change Spindle.leaves U 0*incG U x*(Spindle.leaves U (stop (0:Cover) (carryP x)))⁻¹=1 at hh
    rw [show stop _ (carryP x)=x from route_end ..,show Spindle.leaves U 0=1 from ?_,one_mul] at hh; exact (mul_inv_eq_one.mp hh).symm
    simp [Spindle.leaves,travel]
lemma novaU : central U=Scav U:=by rw [central,Scav,show Spindle.leaves U=incG U from funext fun x=>RoarU U x]
-- polynomial budgets for t rays using true Hol testLinks
end YM.OPE.Spells
