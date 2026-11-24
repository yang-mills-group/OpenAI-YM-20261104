import YM.OPE.Compatible.Slope.Road
/-!
# Page coordinates
Canonical kernels for the virtual polynomial RG. Cost on this representation is kept at a fixed power of the complete displacement, not diameter after wrapping. No need to grant exponentially broad polynomial freebies at a stationary repeated hop. `pack` both ways to Shift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter MeasureTheory Finset Lattice Wilson Laurent RG
open scoped BigOperators Classical Topology
variable {I J:Type*}
abbrev Page (T:Type*) (r:ℕ):= Fin r → Cover × T
abbrev Script (T:Type*) (r:ℕ):= Page T r→ℝ
abbrev Ink (T:Type*) (r:ℕ):= Fin r → T
namespace Page
variable {d m:ℕ}{T:Type*} (x:Page T d)
def blurb (T:Type*) (d:ℕ) : Bin d ×Ink T d≃Page T d where
   toFun p i:=(stepOut p.1 i,p.2 i)
   invFun p:=(lace _ (fun i=>(p i).1),fun i=>(p i).2)
   left_inv _:= rfl
   right_inv _:=rfl
def syn (p:Bin d)(t:Ink T d):= blurb _ _ (p,t)
abbrev xy:= ((blurb T d).symm x).1
abbrev tint:= ((blurb T d).symm x).2
lemma here (i:Fin d): (x i).1=stepOut x.xy i:=rfl
lemma ink (p:Bin d)(t:Ink T d): xy (syn p t)=p∧tint (syn p t)=t:=⟨rfl,rfl⟩
lemma carved : syn x.xy x.tint=x:=rfl
-- diameter accounting
abbrev stamp (x:Page T d):ℕ:= notch x.xy
abbrev figure (m:ℕ) (x:Page T d):= poise m x.xy
lemma payer (m:ℕ): 1 ≤ fun x:Page T d=>figure m x:=fun i=>poise_one m (xy i)
lemma perimeter (x:Page T d): stamp x=1+∑ i,size ((x i).1):=by rw [stamp,notch,couple_size]; rfl
def slide (v:Cover) : Page T d ≃ Page T d where
   toFun p i:=(v+(p i).1,(p i).2)
   invFun p i:=(-v+(p i).1,(p i).2)
   left_inv _:=funext fun _=> Prod.ext (neg_add_cancel_left ..) rfl
   right_inv _:=funext fun _=> Prod.ext (add_neg_cancel_left ..) rfl
lemma slide_zero (x:Page T d): slide 0 x=x:=by ext1 i; simp [slide]
lemma slide_kind (p q:Cover): slide p (slide q x)=slide (p+q) x:=funext fun _=> Prod.ext (add_assoc ..).symm rfl
lemma slide_price (v:Cover): stamp (slide v x) ≤ stamp x+d*size v:=by
   rw [perimeter (slide v x), perimeter x]; let X(i:Fin d):= size (v+(x i).1); have h : ∑ i,X i≤ d* size v+∑ i,size (x i).1:=by
      apply (sum_le_sum (fun i _=> size_add v (x i).1)).trans_eq; rw [sum_add_distrib]; simp
   change 1+∑ i,X i≤ _; omega
-- seal reanchor to submission
abbrev primary (x:Page T d):Cover:= if h:0<d then (x ⟨0,h⟩).1 else 0
lemma origin (v:Cover)(h:0<d): primary (slide v x)=v+primary x:=by unfold primary; simp [slide,h]
def steady (x:Page T d):Page T d:= slide (-primary x) x
lemma still : primary x.steady=0:=by
    by_cases h:0<d
    · rw [steady,origin _ _ h]; exact neg_add_cancel _
    simp [primary,h]
lemma refill (v:Cover) (he:d>0): steady (slide v x)=steady x:=by rw [steady,origin _ _ he, slide_kind]; unfold steady; congr! 2; abel --
lemma pulled : slide (primary x) (steady x)=x:=by rw [steady,slide_kind,add_neg_cancel,slide_zero]
lemma primary_size : size (primary x) ≤ x.stamp:=by
    unfold primary; split
    next h => rw [perimeter]; exact (Finset.single_le_sum (f:=fun i=>size (x i).1) (fun _ _=>Nat.zero_le _) (mem_univ (⟨0,h⟩:Fin d))).trans (Nat.le_add_left _ _)
    simp [size]
lemma stable_price (d0): figure d0 x.steady ≤ ((d+1:ℕ):ℝ)^d0*figure d0 x:=by
    have he : stamp x.steady ≤ (d+1)*stamp x :=by
        have ht:= x.slide_price (-primary x); rw [size_neg] at ht; unfold steady; linarith only [ht, Nat.mul_le_mul_left d (primary_size x)]
    unfold figure poise; rw [← mul_pow, ← Nat.cast_mul]; gcongr
-- perms
lemma turns (A:Equiv.Perm (Fin d)): (stamp (x ∘ A))= stamp x:=by rw [perimeter _,perimeter _]; exact congr_arg (1+·) (Equiv.sum_comp A (fun i=>size (x i).1))
end Page
end YM.OPE.Flume
