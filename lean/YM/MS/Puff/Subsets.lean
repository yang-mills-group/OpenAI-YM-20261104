import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import YM.MS.Puff.Ring

set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Function Finset
open Book Book.Convolve
variable {E W:Type} [DecidableEq W]
namespace SplitP
def nat : SplitP ℕ:={
   origin:=0,grade:=id,zeroC _:=Iff.rfl
   pieces:=antidiagonal
   quiet x y:= by simp [eq_comm]
   pays:= fun p=> Finset.mem_antidiagonal.mp p
   sym:= by intros; simp [add_comm]
   trip:= fun _ _ x f=> Book.Convolve.associate f x }
def subs (x:Finset W): Finset (Finset W× Finset W):= x.powerset.map ⟨ fun z=>(z,x \ z),fun _ _ h=> congr_arg Prod.fst h⟩
lemma cards {S p q:Finset W} : (p,q)∈ subs S ↔ p ⊆ S ∧ q=S \ p:= by
    simp only [subs,Finset.mem_map,Finset.mem_powerset,Embedding.coeFn_mk,Prod.mk.injEq]; grind
lemma joins {S p q:Finset W}: (p,q)∈subs S ↔ p ∪ q=S ∧ Disjoint p q := by
   rw [cards]; constructor; · rintro ⟨hp,rfl⟩; exact ⟨Finset.union_sdiff_of_subset hp,Finset.disjoint_sdiff ⟩
   rintro ⟨rfl,h⟩; refine ⟨ Finset.subset_union_left,?_⟩; rw [Finset.union_sdiff_left ]; exact (Finset.sdiff_eq_self_iff_disjoint.mpr h.symm).symm -- check names
variable [AddCommMonoid E]
lemma sumS (f:Finset W→ Finset W→ E)(S:Finset W): ∑ i∈ subs S,f i.1 i.2=∑ i∈ S.powerset,f i (S\ i):= Finset.sum_map ..
lemma ins {S:Finset W} {x:W}(h:x∉ S)(P:Finset W→ Finset W→ E): (∑ i∈subs (insert x S),P i.1 i.2)=(∑ i∈ subs S,P (insert x i.1) i.2)+(∑ i∈ subs S,P i.1 (insert x i.2)):= by
   -- via add pieces. formula `Finset.sum_powerset_insert`.
   rw [sumS, Finset.sum_powerset_insert h _,sumS (fun a b=> P (insert x a) b),sumS (fun a b=> P a (insert x b)), add_comm ]; refine congr_arg₂ (·+·) (Finset.sum_congr rfl (fun i hi=>?_)) ( Finset.sum_congr rfl (fun i hi=>?_) ) <;> congr 1 <;> ext t <;> ( obtain hu:=Finset.mem_powerset.mp hi; grind )
lemma trip' (E:Type)[AddCommMonoid E] (f:Finset W→ Finset W→Finset W→E)(x:Finset W): (∑ v∈subs x,∑ u∈subs v.2,f v.1 u.1 u.2) =∑ v∈subs x,∑ u∈subs v.1,f u.1 u.2 v.2:= by
   induction x using Finset.induction_on generalizing f with| empty=> simp [subs]| insert i S h ih=>
      rw [ins h (fun a b=>∑ u∈subs b,f a u.1 u.2), ins h (fun a b=>∑ u∈ subs a,f u.1 u.2 b) ]; -- simp.subI? apply congr tactic
      let A (f: Finset W→ Finset W→ Finset W → E):=∑ v∈subs S,∑ u∈subs v.2,f v.1 u.1 u.2; let B(f:Finset W→ Finset W→ Finset W → E):=∑ v∈subs S,∑ u∈subs v.1,f u.1 u.2 v.2
      let f1(a b c:Finset W):= f (insert i a) b c; let f2(a b c:Finset W):= f a (insert i b) c; let f3(a b c:Finset W):= f a b ( insert i c ); calc
         _ = A f1+( A f2 + A f3 ):= by refine congr_arg₂ (·+·) rfl ?_; unfold A; rw [← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl (fun j hj=>?_); exact ins (fun H=> h ( ( cards.mp ( (joins.mpr ⟨ (Finset.union_comm ..).trans (joins.mp hj).1,(joins.mp hj).2.symm⟩) ) ).1 H )) (fun p q=>f j.1 p q)
         _ = B f1+B f2+B f3:= by rw [ add_assoc ]; exact congr_arg₂ (·+·) (ih _) (congr_arg₂ (·+·) (ih _) (ih _))
         _ = _:= by unfold B; rw [← Finset.sum_add_distrib]; refine congr_arg₂ (·+·) ( Finset.sum_congr rfl fun j hj=> ( ins (fun H=>h ( (cards.mp hj).1 H )) (fun p q=>f p q j.2) ).symm ) rfl
def marked (W: Type)[DecidableEq W]: SplitP (Finset W):={
   origin:=∅
   grade S:= S.card
   zeroC _:= Finset.card_eq_zero
   pieces:= subs
   quiet x y:= by rw [cards,Finset.sdiff_empty]; exact ⟨ fun h=> h.2.symm,fun h=>⟨ Finset.empty_subset _,h.symm⟩⟩
   pays:=fun h=> let u:= joins.mp h; by rw [ ← u.1,Finset.card_union_of_disjoint u.2 ]
   sym:= by intros; rw [joins,joins,Finset.union_comm,disjoint_comm]
   trip:= fun E _ x F=> trip' E F x }
end SplitP
end YM.MS.Puff
