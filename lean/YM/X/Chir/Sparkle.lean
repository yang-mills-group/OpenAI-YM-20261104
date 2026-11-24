import YM.X.Chir.Cov
/-!
# Single-line spin K-- collapses to δ plus zero mode & primitive leakage HEAT
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}
variable (i j:Axis)(p c:Tet)(r t:ℝ)
-- graph shift leath
lemma graph_st (n:Side)(t:Cover)(x y:Site n)(l:List Axis) : graphS (i::l) t n x y = graphS l (t+step i) n x y - graphS l t n x y:= by simp only [graphS,Interval.grads,differ,map_add,wrap_step,add_assoc]
lemma graph_two (n:Side)(x y:Site n): graphS [i,i] (-step i) n x y= green ((x-y)+step i)+green ((x-y)-step i)-(2:ℝ)*green (x-y):= by simp only [graphS,Interval.grads,differ,map_neg,wrap_step, ←sub_eq_add_neg, sub_add_cancel]; ring
lemma back_cost (k:ℕ) (x y:Site n): ∑ i:Axis, graphS [i,i] (-step i) n x y = (- (if x=y then 1 else 0):ℝ)+(n.val:ℝ)^(-4:ℤ) := by
    have he:= Pert.Orb.lap_shift (x-y); simp_rw [← show green=(fun z:Site n => (Pert.Full.toroid z).re) from rfl, sub_eq_zero] at he; rw [← he]; simp_rw [graph_two,Pert.Orb.lap,nsmul_eq_mul]; push_cast; rfl
-- explicit expansion exchange.coefficient. Avoid Matrix. world calibration.
def α_pair (r:ℝ) (p:Tet)(t:ℝ)(c:Tet)(x y:Axis):ℝ:= ∑ i:Axis,form r p y i*form t c x i
lemma α_flip: α_pair r p t c i j=α_pair t c r p j i:= by unfold α_pair; simp_rw [mul_comm]
lemma leased : exchangeF r p t c = -∑ x:Axis,∑ y:Axis, α_pair r p t c x y • graphS [x,y] (-step x) := by
    unfold exchangeF transfer α_pair; rw [Finset.sum_comm]; simp_rw [map_sum, map_smul,graph_d,Finset.smul_sum, ← Finset.sum_neg_distrib,smul_neg,smul_smul]; apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_comm]; simp_rw [Finset.sum_smul,zero_sub]; apply Finset.sum_congr rfl; intro y _; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro v _; rw [mul_comm]
lemma α_mm : α_pair (-1) p (-1) c i j= (if p=c∧j=i then 1 else 0) - η_at p c j i:=by change (∑ x:Axis, mn p j x * mn c i x)=_; simp_rw [show ∀ x:Axis,mn c i x = -mn c x i from layout (-1) c i, mul_neg,Finset.sum_neg_distrib,mm]; split_ifs <;> ring
def slag (p c:Tet): Scaff:= -∑ x:Axis,∑ y:Axis, η_at p c y x • graphS [x,x,y] (-step x)
lemma slag_h : slag p c∈air 3:= (air 3).neg_mem ((air 3).sum_mem fun x _=> (air 3).sum_mem fun y _=> (air 3).smul_mem _ (air_graph _ _ rfl)) -- no unfold syntax
lemma waste_blue : ∑x:Axis,∑y:Axis, η_at p c y x • graphS [x,y] 0=0:= by
    let f(y x:Axis):Scaff:= η_at p c y x • graphS [x,y] 0; let k:= ∑x:Axis,∑y:Axis,f y x
    have h : k=-k:= by
       unfold k; nth_rw 1 [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; unfold f; rw [η_at_flips p c x y,neg_smul,graph_alt y x []]
    change k=0; ext n z y; have he:- k n z y= k n z y:= congr_fun (congr_fun (congr_fun h.symm n) z) y; change k n z y=0; linarith only [he]
lemma waste_sum : ∑ x:Axis,∑ y:Axis, η_at p c y x • graphS [x,y] (-step x) = slag p c:= by
    have he (x y:Axis): graphS [x,y] (-step x)= graphS [x,y] 0-graphS [x,x,y] (-step x):= by ext n u v; simp only [Pi.sub_apply,graph_st x n (-step x) u v [x,y],neg_add_cancel,sub_sub_self]; -- ..
    unfold slag; rw [← zero_sub (∑ _,_)]; rw [←waste_blue p c]; simp_rw [he,smul_sub,Finset.sum_sub_distrib]; -- macro
lemma spincontact : exchangeF (-1) p (-1) c= (if p=c then -∑ x:Axis,graphS [x,x] (-step x) else 0)+slag p c := by
     rw [leased]; simp_rw [α_mm,sub_smul, Finset.sum_sub_distrib,waste_sum]; by_cases h:p=c <;> simp [h,ite_smul]; ring
lemma slag_plot (e:ℝ)(x y:Site n)(he:0<e) :
     Wpp e (-1) p (-1) c n x y = e* sprite e 3 (slag p c) n x y + if p=c then (e^4)⁻¹ * ((if x=y then (1:ℝ) else 0) - (n.val:ℝ)^(-4:ℤ)) else 0 := by
     unfold Wpp; rw [spincontact]; simp only [sprite,Pi.smul_apply,smul_eq_mul,Pi.add_apply]; -- need ite manually
     by_cases hz:p=c
     · simp [hz,back_cost 0]; field_simp; ring
     simp [hz];field_simp
end YM.PositionX.Chir
