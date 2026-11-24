import YM.OPE.Compatible.Seas.Lith
/-!
# Harmful
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam.Port
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Pert.Full (toroid)
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z:(i:ℕ)→Site (U.M i)}{d:ℝ}{f g:ℕ→ Cover→ℝ}{k j:ℕ}
lemma sMinus (h₁:Sach f)(h₂:Sach g):Sach (f-g):=fun x=> by filter_upwards [h₁ x,h₂ x] with i hi hh; rw [Pi.sub_apply,Pi.sub_apply,hi,hh,sub_self]
lemma hue_minus (hf:Hum f)(hg:Hum g):Hum (f-g):=by
   unfold Hum; rw [show (∑ i:Axis,diskS i (f-g))=(∑ i:Axis,diskS i f)-∑ i:Axis,diskS i g from ?_]; exact sMinus hf hg
   funext i x; simp_rw [Pi.sub_apply,Finset.sum_apply, diskS_a,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; simp only[Pi.sub_apply]; ring
lemma hue_zero:Hum 0:=by refine fun x=>Eventually.of_forall fun i=>?_ ; simp_rw [Finset.sum_apply,diskS_a, Pi.zero_apply]; simp
-- force RHS
lemma squat {n:Side}(x:Site n): ∑ i:Axis, (mildX [] (x+step i)+mildX [] (x-step i)-2*mildX [] x)= -(if x=0 then 1 else 0)+(sizeR n)^(-4:ℤ):=by
   have he:=Pert.Full.lap_eq x
   have hp:=congr_arg Complex.reCLM he
   simp_rw [map_sum, map_sub, map_add, map_nsmul] at hp
   simp_rw [mild_tip]; convert! hp using 1
   · simp [two_smul,two_mul]
   unfold sizeR; rw [show (n.val:ℂ)^(-4:ℤ)=(( (n.val:ℝ)^(-4:ℤ):ℝ):ℂ) from by push_cast;rfl]; split <;> simp only [map_neg,Complex.reCLM_apply,Complex.ofReal_re,Complex.one_re, Complex.zero_re]
-- hull ∆
lemma sqHull (x:Cover): ∑ i:Axis, (hull [] (x+step i)+hull [] (x-step i)-2*hull [] x) = -(if x=0 then 1 else 0):=by
    let U:=twin (2:Side); let M:=U.M; have hM:Tendsto (fun i=> (M i).val) atTop atTop:=U.sides; have he(a:Cover): Tendsto (fun i=> mildX [] (wrap (M i) a)) atTop (𝓝 (hull [] a)):= calm M (Eventually.of_forall fun i=> Even.mul_right (show Even (2:Side).val from ⟨1,rfl⟩) ((2:Side)^i).val) hM _ _
    have hu:Tendsto (fun i=> (sizeR (M i))^(-4:ℤ)) atTop (𝓝 0):=by simp_rw [_root_.zpow_neg,zpow_ofNat,←inv_pow]; have ht:=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hM); simpa only[zero_pow (by decide:4 ≠0)] using! ht.pow 4
    apply tendsto_nhds_unique (tendsto_finsetSum _ fun i _=> ((he (x+step i)).add (he (x-step i))).sub ((he x).const_mul 2)); rw [← add_zero (-(if x=0 then 1 else 0):ℝ)]; apply (tendsto_const_nhds.add hu).congr'; filter_upwards [hM.eventually (eventually_gt_atTop (2*size x))] with i hi
    simp only [map_add,map_sub,wrap_step,squat]; by_cases h:x=0; · simp [h]
    have hx:wrap (M i) x≠0:=fun he=>h (by rw [←gentle (n:=M i) hi,he]; ext a;simp [Lattice.lift]); simp only [if_neg hx,if_neg h]
def ebb (D:List Axis)(U:Gloam)(z:(i:ℕ)→Site (U.M i))(i:ℕ)(x:Cover):ℝ:=mildX D (z i+wrap _ x)
def flood (D:List Axis)(U:Gloam)(i:ℕ)(x:Cover):ℝ:=seam D (U.M i) x
lemma ebb_a (a:Axis)(D): ebb (a::D) U z=smear a (ebb D U z):=by funext i x; unfold smear numDiff ebb; rw [mild_more,map_add,show wrap _ (stint a)=step a from wrap_step ..,add_assoc]
lemma flood_a (U:Gloam)(a:Axis)(D): flood (a::D) U=smear a (flood D U):=by funext i x; unfold flood smear numDiff seam; rw [mild_more,hull]; dsimp only; rw [map_add,show wrap _ (stint a)=step a from wrap_step ..,show stint a=(step a:Cover) from rfl];abel
private lemma nuggets {Ψ:ℕ→ℝ}(h:∀ x:Cover,∀ᶠ i in atTop,(∑ a:Axis,diskS a f) i x=Ψ i)(D:List Axis)(hD:D≠[]): Hum (stalkP D f):=by
    induction D with
    | nil=> contradiction
    | cons a D ih=>
      by_cases he:D=[]; swap; · exact hum_grad (ih he) _
      subst D; intro x; filter_upwards [h x,h (x+step a)] with i hi ht; change (∑ b:Axis,diskS b (smear a f)) i x=0
      have hh:(∑ b:Axis,diskS b (smear a f)) i x= (∑ b:Axis,diskS b f) i (x+step a)-(∑ b:Axis,diskS b f) i x:=by
          simp_rw [Finset.sum_apply,diskS_a,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro b _
          unfold smear numDiff; rw [show stint a=(step a:Cover) from rfl, add_right_comm x (step b),sub_add_eq_add_sub];ring
      rw [hh,hi,ht,sub_self]
lemma ebb_h (h:Drone U z)(hp:z 0≠0)(D:List Axis)(hD:D≠[]):Hum (ebb D U z):=by
   have he(l:List Axis): ebb l U z=stalkP l (ebb [] U z):=by induction l with
       | nil=> rfl
       | cons i l ih=> rw [ebb_a,ih];rfl
   rw [he D]; apply nuggets (Ψ:=fun i=>(sizeR (U.M i))^(-4:ℤ)) _ _ hD; intro x; let r:= seaRise U z 0
   filter_upwards [(U.h_null.mul_const (size x:ℝ)).eventually (gt_mem_nhds (show 0*(size x:ℝ)<r from by rw [zero_mul];exact sea_pos hp))] with i hi
   have ha: z i+wrap _ x≠ 0:=by
       intro he; have ht:=Next.Free.within_size x (U.M i); rw [show wrap _ x= -z i from eq_neg_of_add_eq_zero_right he, pdist_neg] at ht; apply not_lt_of_ge (a:=r) ?_ hi; rw [show r= _ from (soar h i).symm]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (U.h_pos _).le
   simp_rw [Finset.sum_apply, diskS_a, ebb,map_add, map_sub,wrap_step, ← add_assoc, ← add_sub_assoc]; rw [squat,if_neg ha,neg_zero,zero_add]
lemma flood_h (U:Gloam)(D:List Axis)(hh:D≠[]):Hum (flood D U):=by
   have he(l:List Axis): flood l U=stalkP l (flood [] U):=by induction l with | nil=>rfl | cons i l ih=>rw [flood_a,ih];rfl
   rw [he D]; apply nuggets (Ψ:=fun i=>(sizeR (U.M i))^(-4:ℤ)) _ _ hh; intro x
   filter_upwards [U.sides.eventually (eventually_gt_atTop (2*size x))] with i hi
   have hx:wrap (U.M i) x=0 ↔ x=0:=by
       refine ⟨fun he=>?_,fun he=>he ▸ map_zero _⟩; rw [← gentle (n:=U.M i) hi,he]; ext a;simp [Lattice.lift]
   let Y(a:Axis):= mildX [] (wrap (U.M i) (x+step a))+ mildX [] (wrap (U.M i) (x-step a))-2*mildX [] (wrap (U.M i) x)
   let B(a:Axis):= hull [] (x+step a)+hull [] (x-step a)-2*hull [] x
   simp_rw [Finset.sum_apply, diskS_a]; rw [Finset.sum_congr (g:=fun a=> Y a-B a) rfl (fun a _=>?_ ),Finset.sum_sub_distrib]; swap; · unfold Y B flood seam; ring
   unfold Y B; simp_rw [map_add, map_sub, wrap_step,squat,sqHull,hx]; ring
end YM.OPE.Balsam.Port
