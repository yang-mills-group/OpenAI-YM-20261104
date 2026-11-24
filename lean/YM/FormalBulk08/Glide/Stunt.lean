import YM.FormalBulk08.Glide.Both

/-! A vertical analytic difference accepted at coarse scale ANY direction. Use
Ward in unchanged r. One marked root for divergence, others integrated. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{m r:ℕ}{L : Side}{I : Type}

abbrev colorsL (G : Gauge):= Stationary.Loc G 1
abbrev spots (G : Gauge):= Stationary.Loc G 0

def proxy (S:Cross L (spots G) I) : Cross L (colorsL G) I:=fun v i=>if v.2.1=coord 0 then S (v.1,vac,v.2.2) i else 0
lemma proxy_pay {S:Cross L (spots G) I}(hs:S.strip η C)(h:0≤C) : (proxy S).strip η C:= by intro v k; unfold proxy; split; exact hs _ _; simp [Width, SumBudget,h]

def trench (S: Cross L (colorsL G) I)(U: Cross L (spots G) I) := ∀ x a i b,
      merit S (x,coord a,i) b = merit U (x+step a,vac,i) b- merit U (x,vac,i) b

variable [Fintype I]
lemma sum_strip {V : Type} [Fintype V] {R: Cover × V→ ℝ} (hp:Summable R): (∑' x,R x) =∑ i: V,∑' x:Cover,R (x,i):=by
   rw [← (Equiv.prodComm V Cover).tsum_eq]; let f:=R ∘ (Equiv.prodComm V Cover);change (∑' x,f x)= _; rw [Summable.tsum_prod (show Summable f from (Equiv.prodComm V Cover).summable_iff.mpr hp),tsum_fintype];rfl

set_option maxHeartbeats 500000 in
lemma trench_tally {S: Cross L (colorsL G) I}{U:Cross L (spots G) I}{T:Tile (edgeL G) (m+1)}(h:trench S U)(p:0≤σ)(q:0≤η)(hp:Bail (fame _) σ T B)(hq:Bail (fame _) σ (tap T) D)(hw:S.strip η C)(ha:U.strip η C)(hc:0≤C) (b:Biglot I)(v:chain (edgeL G) m):
     ∑' x,T (Fin.cons x v)*merit S x b= -∑' x, tap T (Fin.cons x v) * merit (proxy U) x b:= by
   let w x:= (Fin.cons x v : chain (edgeL G) (m+1)); let P (x:Cover)(i:hue G):=merit U (x,vac,i) b
   have he : Summable fun (x:edgeL G)=>T (w x)*merit S x b := Summable.of_norm_bounded ((center_row S hw q hc b).norm.mul_left _) (fun i=>by rw [_root_.norm_mul]; exact mul_le_mul_of_nonneg_right (hp.value p (w i) 0) (norm_nonneg _))
   have hh : Summable fun (x:edgeL G)=>tap T (w x)*merit (proxy U) x b:= Summable.of_norm_bounded ((center_row _ (proxy_pay ha hc) q hc b).norm.mul_left _) (fun i=>by rw [_root_.norm_mul]; exact mul_le_mul_of_nonneg_right (hq.value p (w i) 0) (norm_nonneg _))
   have hs (i:hue G): Summable (fun x=>P x i):=(center_row U ha q hc b).comp_injective (i:=fun x:Cover=>(show Biglot (spots G) from (x,vac,i))) (fun x y h=>congr_arg Prod.fst h)
   have ht (g f:Cover→ Cover) (a : Axis) (i:hue G) (hg:Injective g): Summable fun x=>T (w (f x,coord a,i))*P (g x) i:= Summable.of_norm_bounded (((hs i).comp_injective hg).norm.mul_left _) (fun j=>by rw [_root_.norm_mul];exact mul_le_mul_of_nonneg_right (hp.value p _ 0) (norm_nonneg _))
   let K a (i:hue G) (x: Cover):= T (w (x,coord a,i))
   have hP (a : Axis)(i:hue G):
      (∑' x,T (w (x,coord a,i))*merit S (x,coord a,i) b)=-(∑' x,(K a i x-K a i (x-step a))*P x i):= by
       simp_rw [show ∀ x, merit S (x,coord a,i) b =_ from (fun x: Cover=> h x a i b), mul_sub,sub_mul]
       let g:=Equiv.addRight (step a:Cover); let f (x:Cover):=x-step a
       change (∑' x,(K a i x*P (g x) i - K a i x*P x i)) = -(∑' x,(K a i x*P x i-K a i (f x)*P x i))
       have hy: Summable fun x=>K a i x*P x i := ht id id a i Function.injective_id
       rw [Summable.tsum_sub (show Summable fun x=> K a i x * P (g x) i from ht g id a i g.injective) hy, Summable.tsum_sub hy (show Summable fun x=> K a i (f x)*P x i from ht id f a i Function.injective_id),neg_sub]; congr 1
       rw [← Equiv.tsum_eq g (fun x=> K a i (f x) * P x i)]; simp [f,g]
   change (∑' x,T (w x)*merit S x b)= -∑' x,tap T (w x)* _
   rw [sum_strip he,sum_strip hh];
   rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; conv_lhs=> rw [Finset.sum_comm]
   conv_rhs=> arg 1;rw [Finset.sum_comm]
   rw [←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _
   let Y (a:TypeFace 1)(x:Cover):=tap T (w (x,a,i))*merit (proxy U) (x,a,i) b
   change _ = -∑ a,∑' x,Y a x
   rw [Finset.sum_eq_single (f:=fun a=>∑' x,Y a x) (coord 0)]; swap
   · intro a _ ha; unfold Y; simp [merit, lands,Bank.scroll,proxy,ha]
   swap; · simp
   rw [←Equiv.sum_comp axisEquiv (fun a=>∑' x,T (w (x,a,i))*merit S (x,a,i) b)]
   simp_rw [coord_map,hP]; rw [Finset.sum_neg_distrib,← Summable.tsum_finsetSum]; swap
   · intro a _; simp_rw [sub_mul]; exact (ht id id a i Function.injective_id).sub (ht id (fun x=>x-step a) a i Function.injective_id)
   congr 1; apply tsum_congr; intro x; rw [← Finset.sum_mul]; unfold Y
   rw [show merit (proxy U) (x,coord 0,i) b=P x i from by unfold merit lands P; simp [proxy,Bank.scroll,merit,lands]]; unfold tap; simp only [w,Fin.cons_zero, Fin.tail_cons,riverP,Finset.sum_apply,Pi.sub_apply]; congr 1
   exact Fintype.sum_equiv axisEquiv _ _ fun a=>by rw [backwards, axisEquiv.symm_apply_apply];rfl
end YM.FormalBulk08.Glide
