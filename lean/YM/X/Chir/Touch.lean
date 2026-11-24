import YM.X.Chir.Penny
/-!
# Symmetry and normalization of Green gradient convolution. Telescoping and weighted sum including puncture.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "D"=> Interval.mass
local notation "S" => Site n
local notation "L"=>(atTop:Filter ℕ)
variable (x y:Site n)(i j:Axis)
abbrev prong (i:Axis):Scaff:= graphS [i] 0
abbrev h0 :Scaff:=graphS [] 0
lemma h0_pay : h0 n x y= green (x-y):= by simp only [h0,graphS,Interval.grads,map_zero,add_zero]
open Pert Pert.Full in
lemma neutral : ∑ x:Site n,green x=0:= by
   suffices h: ∑ x:Site n,toroid x=0 by unfold green; rw [←Complex.re_sum,h, Complex.zero_re]
   unfold toroid; rw [sum_comm]; simp_rw [←Finset.mul_sum,Pert.Full.scan]; simp [topWeight, Full.delta,Full.moment,Lattice.lift]
def flipA : S≃S where
    toFun i:= x-i; invFun i:=x-i; left_inv i:= sub_sub_self ..; right_inv i:=sub_sub_self ..
lemma sunny : ∑ y:S,h0 n x y=0:= by simp_rw [h0_pay]; exact (Equiv.sum_comp (flipA x) green).trans neutral
abbrev traceL (e:ℝ)(x y:Site n)(f g:Scaff):ℝ:= e⁻¹^2 * ∑ i:Site n, f n x i* g n y i
lemma fstep : prong i n x y=h0 n x (y-step i)-h0 n x y:= by simp only [prong,graphS,Interval.grads,differ,map_zero,add_zero,h0]; rw [show x-(y-step i)=x-y+step i by abel]
lemma edge_shift (f g : S→ℝ)(v:S): ∑ u:S,(f (u-v)-f u)*g u=∑ u:S,f u*(g (u+v)-g u):= by
     simp_rw [sub_mul,mul_sub,Finset.sum_sub_distrib]; conv_lhs=> arg 1; rw [← Equiv.sum_comp (Equiv.addRight v)]; simp only [show ∀ x:S,(Equiv.addRight v) x=x+v from fun x=>rfl,add_sub_cancel_right]
lemma base_lap (u:S) : ∑ i:Axis, (prong i n x (u+step i)- prong i n x u)=(if x=u then 1 else 0) - (n.val:ℝ)^(-4:ℤ) := by
    rw [show _ - (n.val:ℝ)^(-4:ℤ) = - (-(if x=u then 1 else (0:ℝ))+(n.val:ℝ)^(-4:ℤ)) from by ring, ← back_cost 0 x u, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [graph_two,fstep,h0_pay,add_sub_cancel_right]; rw [show x-(u-step i)=x-u+step i by abel, show x-(u+step i)=x-u-step i by abel]; ring
lemma energy_pair (i:Axis) : ∑ z:S, prong i n x z* prong i n y z = ∑ z:S,h0 n x z*(prong i n y (z+step i)-prong i n y z):= by simp_rw [fstep x]; exact edge_shift (h0 n x) _ _ -- edge_shift x y implicit?
lemma dotTour (e:ℝ) : ∑ i:Axis, traceL e x y (prong i) (prong i)= e⁻¹^2* green (x-y):= by
    unfold traceL; simp_rw [energy_pair, ← Finset.mul_sum]; rw [sum_comm (f:=fun i z=> h0 n x z* _)]; simp_rw [←Finset.mul_sum,base_lap]; simp_rw [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_mul,sunny,zero_mul,sub_zero]; rw [h0_pay]
lemma even_g (u:S): prong i n x (x+y-u)= -prong i n y (u+step i):= by
    simp only [fstep,h0_pay,add_sub_cancel_right]; rw [show x-(x+y-u)= -(y-u) by abel,show x-(x+y-u-step i)= -(y-(u+step i)) by abel,green_neg,green_neg]; ring
-- price fees. dyadic already paid.
local notation "ε"=>epsilon q
def toRight (i:Axis)(f:Scaff): Scaff:= fun n x y=> f n x (y+step i)
lemma reflect_at (e:ℝ): traceL e x y (prong i) (prong j)= traceL e x y (toRight j (prong j)) (toRight i (prong i)):= by
    unfold traceL; conv_lhs=> rw [← Equiv.sum_comp (flipA (x+y))]
    apply congr_arg (_ * ·); apply Finset.sum_congr rfl; intro z _; change prong i n x (x+y-z)*prong j n y (x+y-z)=prong j n x (z+step j) * prong i n y (z+step i); rw [even_g, add_comm x y, even_g]; ring
variable {X Y:Fielding.Walk}
abbrev Tr (q:ℕ+)(X Y:Fielding.Walk)(f g:Scaff)(k:ℕ):= traceL (epsilon q k) (transit q X k) (transit q Y k) f g
lemma transmute (f g:Scaff): Tr q X Y f g=Tr q Y X g f:= by ext1 k; unfold Tr traceL; simp only [mul_comm]
lemma turned (f g:Scaff)(j:Axis): Tr q X Y (toRight j f) g-Tr q X Y f g= Tr q X Y (ds j f) g:= by ext1 k; unfold Tr traceL; simp only [Pi.sub_apply,←mul_sub,ds_val,sub_mul,Finset.sum_sub_distrib]; rfl
variable (hx:Clear q R X Y)(hq:1<q.val)(hr:R≥0)
include hx hr hq
lemma niggle (f g:Scaff)(i:Axis)(h:f∈air 1)(hc:c≥0) (hh:∀ᶠ k:ℕ in atTop,Paying (transit q Y k) 3 c (g (side q k) (transit q Y k))):
     Tendsto (Tr q X Y (toRight i f) g-Tr q X Y f g) L (𝓝 0):= by
       rw [turned]; obtain ⟨a,ha,he⟩:= nice hq f h; refine friction_s hx hq hr ha.le hc ?_; exact (he.and hh).mono fun k h=>⟨(h.1 _|>.2 i),h.2⟩
lemma tr_sym (i j:Axis): Tendsto (Tr q X Y (prong i) (prong j)- Tr q X Y (prong j) (prong i)) L (𝓝 0):= by
    let f:=prong i; let g:=prong j; have hf : f∈ air 1:= air_graph _ _ rfl; have hg:g∈air 1:=air_graph _ _ rfl; obtain ⟨c,hc,H⟩:= costF hq f hf; obtain ⟨a,ha,W⟩:=costF hq g hg; let F:=toRight i f; let U:=toRight j g; let l:=Tr q X Y; rw [show Tr q X Y (prong i) (prong j)=l U F from funext (fun k=> reflect_at _ _ _ _ _),show Tr q X Y (prong j) (prong i)=l g f from rfl]; have he:=niggle hx hq hr g F j hg (show 8*c≥0 by positivity) (H.mono (fun k hk=>shift_step (transit q Y k) i (f _ _) (hk _) hc.le)); have hh: Tendsto (l g F-l g f) L (𝓝 0):= by unfold l; rw [transmute g F, transmute g f]; exact niggle (hx.sym q X Y) hq hr f g i hf ha.le (W.mono fun k hk=>hk _)
    rw [show l U F-l g f=(l U F-l g F)+(l g F-l g f) from by ring]; have ht:= he.add hh; rw [zero_add] at ht; exact ht
end YM.PositionX.Chir
