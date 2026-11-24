import YM.FormalBulk08.Orb.Swans

/-! Convert uncentered coordinates to relative to the possibly gauge dependent saddle.
Only the unit Jacobian of this translation cancels. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators Classical
variable {V I J : Type*}

def levels (a : V→ Ink V J) := roam ℝ (Sum.elim a (fun j:J=>boost V (C (MvPolynomial.X j))))
def upstream (V : Type*) {J : Type*} : Pap J →+* Pap (V ⊕ J) := PowerSeries.map (MvPolynomial.rename Sum.inr).toRingHom
def still (V J : Type*) := fun i:V => C (MvPolynomial.X (R:=ℝ) (Sum.inl (β:=J) i))
def dish (a : V→Pap (V⊕J)) (z : I→Pap J) : Pap (V⊕I) →+* Pap (V⊕J) := roam ℝ (Sum.elim a (fun i=>upstream V (z i)))
lemma levels_still (a : V→Ink V J) (i) : levels a (still V J i)=a i := by simp [levels,still,roam]
lemma upstream_reveal (a : V→Ink V J) (p : Pap J) : levels a (upstream V p)=boost V p := by
   unfold levels roam upstream; rw [change_after]
   unfold boost
   have he : (insertAt ℝ (Sum.elim a (fun j:J=>boost V (C (MvPolynomial.X j))))).comp (MvPolynomial.rename Sum.inr).toRingHom = C.comp MvPolynomial.C := by
      ext <;> simp [boost]
   unfold boost at he; rw [he,pure_map]
lemma dish_reveal (a : V→Ink V J) (b : V→Pap (V⊕J)) (z : I→Pap J) (p : Pap (V⊕I)) :
    levels a (dish b z p)=roam ℝ (Sum.elim (fun i=>levels a (b i)) (fun i=>boost V (z i))) p := by
   unfold dish levels roam
   rw [change_comp]; rw [show (changeBy _).comp _=_ from ?hex]
   case hex =>
     ext
     case hC r n m p=> simp [boost]
     case hX i n m l=> cases i <;> simp only [RingHom.comp_apply,insert_X,Sum.elim_inl,Sum.elim_inr]; rw [show changeBy _ _= _ from upstream_reveal a (z _)] -- case

variable [DecidableEq V] [Fintype V] (H D : Hull V I)
variable (Y : V→Pap (V⊕J)) (z w : I→Pap J)
-- let y from A coordinates. discount shifted B

def live : V → Ink V J := fun i => advance H z (Sum.inl i)
def shuttle : Pap (V⊕J)→+* Ink V J:=levels (live H z)
def centered : V→Ink V J:= fun i => shuttle H z (Y i)-boost V (roam ℝ w (C (D.drift i)))

lemma lease (p : Pap (V⊕I)) : shuttle H z (dish (still V J) z p)=roam ℝ (advance H z) p := by
   unfold shuttle; rw [dish_reveal];simp_rw [levels_still]; rfl
lemma discount (p : Pap (V⊕I)) : roam (TypeR J) (centered H D Y z w) (roam ℝ (advance D w) p)=shuttle H z (dish Y w p) := by
   rw [shuttle,dish_reveal,roam,roam]; rw [change_comp]
   unfold roam
   have he : (changeBy (insertAt (TypeR J) (centered H D Y z w))).comp (insertAt ℝ (advance D w))=insertAt ℝ (Sum.elim (fun i=>levels (live H z) (Y i)) fun i=>boost V (w i)) := ?h
   rw [he]; case h=>
     ext
     case hC r n m v=> simp
     case hX i n m v=>
       cases i with
       | inl i=>
          simp_rw [advance,RingHom.comp_apply, insert_X,Sum.elim_inl,map_add,change_C,insert_X,show changeBy _ (boost _ _)= _ from roam_boost (centered H D Y z w) _, centered]; rw [map_sub,sub_add_cancel]; rfl
       | inr i=> simp_rw [advance,RingHom.comp_apply,insert_X,Sum.elim_inr,show changeBy _ (boost _ _)= _ from roam_boost (centered H D Y z w) _]
end YM.FormalBulk08.Orb
