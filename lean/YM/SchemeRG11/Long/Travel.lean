import YM.SchemeRG11.Long.Scout
/-! Dressed general lines; asymptotic in one spacing h independent L Laning. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open scoped Classical
variable {G:Gauge} {n m:ℕ} {T:Align.Itinerary}
local notation "D" => Atoll.land G
lemma double_comm (u v:Touch G) : (Atoll.land G).bed u v=(Atoll.land G).bed v u:= (Atoll.land G).bed_comm u v
lemma doub (u v w:Touch G):(Atoll.land G).bed (u+v) w=(Atoll.land G).bed u w+(Atoll.land G).bed v w:=by rw [double_comm,Dose.bed,map_add,double_comm u,double_comm v];rfl
lemma paid_s (u v:Touch G)(c:ℝ):(Atoll.land G).bed (c • u) v=c* (Atoll.land G).bed u v:=by rw [double_comm,Dose.bed,map_smul]; change c*(Atoll.land G).bed v u=_; rw [double_comm]
lemma flexD (z:Cover)(a b:Touch G): (Atoll.land G).bed (flex z a) (flex z b)= (Atoll.land G).bed a b:=by
 have e(i j:Shaft G):(Atoll.land G).bed (flex z (idi i)) (flex z (idi j)) = (Atoll.land G).bed (idi i) (idi j):=by rw [flex_one,flex_one]; simp only [Dose.bed,grain, idi,Dose.single_wind, Atoll.land,rise,add_sub_add_right_eq_sub]
 have h(u:Touch G)(U:∀ i:Shaft G,(Atoll.land G).bed (flex z (idi i)) (flex z u)=(Atoll.land G).bed (idi i) u)(v:Touch G):(Atoll.land G).bed (flex z v) (flex z u)=(Atoll.land G).bed v u:=by induction v using Finsupp.induction_linear with
  | zero=>rw [map_zero];rw [(Atoll.land G).bed_comm 0, (Atoll.land G).bed_comm 0];simp [Dose.bed]
  | add p q hp hq=>rw [map_add,doub,doub,hp,hq]
  | single p c=>rw [show Finsupp.single p c=c • idi p by simp [idi],map_smul,paid_s, paid_s,U]
 apply h b _ a; intro i; rw [double_comm,double_comm (idi i)]; exact h _ (fun j=> e j i) b
lemma ripple (a b:Touch G)(i:Axis)(z:Cover) :
 (Atoll.land G).bed (flex z a) (rift G i b)= (Atoll.land G).bed (flex (z-step i) a) b - (Atoll.land G).bed (flex z a) b:=by
 change (Atoll.land G).bed _ (_ - _) =_
 unfold Dose.bed; rw [map_sub]; change (Atoll.land G).bed _ _ - (Atoll.land G).bed _ _ = _ - _
 rw [show (Atoll.land G).bed (flex z a) (flex (step i) b)=(Atoll.land G).bed (flex (z-step i) a) b from by
   rw [← flexD (step i) (flex (z-step i) a) b, flex_mul, show (step i:Cover)+(z-step i)=z by abel]];rfl
lemma birds (u:Fliers)(a b:Touch G)(x:Cover): (Atoll.land G).bed (flex x (riffle u a)) b=fleet u (fun z=>(Atoll.land G).bed (flex z a) b) x:=by rw [double_comm,Dose.bed,fade]; simp_rw [show ∀ z:Cover,sense ((Atoll.land G).windfall b) (flex z a)=_ from fun z=>double_comm b (flex z a)] -- type

def streak (v:Fliers): Cover:= -(v.map (fun i=> (step i:Cover))).sum
lemma dualDrive (x y:Fliers)(p q:Touch G)(z:Cover): (Atoll.land G).bed (flex z (riffle x p)) (riffle y q)= (-1)^y.card *fleet (x+y) (fun i=>(Atoll.land G).bed (flex i p) q) (z+streak y):=by
 induction y using Multiset.induction generalizing x z with
 | empty=>rw [Multiset.card_zero,pow_zero,one_mul,add_zero]; exact (birds x p q z) |>.trans (by simp [streak])
 | cons a b ih=>
   rw [riffle_cons]; change (Atoll.land G).bed _ (rift G a _)=_
   rw [ripple _ _ _,ih x,ih x,Multiset.card_cons,pow_add,show streak (a ::ₘ b)=streak b-step a from by simp only [streak,Multiset.map_cons,Multiset.sum_cons]; abel,Multiset.add_cons, fleet_cons,Module.End.mul_apply,soar_apply]
   rw [show z+(streak b-step a)=z-step a+streak b by abel,show z-step a+streak b+step a=z+streak b by abel]; ring
lemma ruralDerivative (l:List Axis)(f:Plane ℝ)(z:Cover): fleet (l: Fliers) f z=derive l f z:=by induction l generalizing z with
 | nil=>rfl
 | cons i l h=>rw [show ((i :: l): Fliers)= i ::ₘ (l: Fliers) from rfl,fleet_cons]; change soar i _ _=_; rw [soar_apply,h,h]; rfl
end YM.SchemeRG11.Long
