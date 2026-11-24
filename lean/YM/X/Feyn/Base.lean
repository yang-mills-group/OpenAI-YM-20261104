import YM.X.Feyn.Split
/-!
# Hessian projection and divergence-free representative padded from Tree. `pad`
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set MeasureTheory Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb
open Pert.Orb (Potential positiveLinks takeLink wilson action dLin bridge bridgeEquiv gZ takeDiv form curL formL)
open Series Series.Radial GaussianScore
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val)
local notation "E" => Potential G n
local notation "A" => Dir G n

def pad : A→ₗ[ℝ] E:= fits he - gZ ∘ₗ (bridgeEquiv G n).symm.toLinearMap ∘ₗ dLin ∘ₗ fits he
lemma pad_div (v:A): dLin (pad he v)=0:= by
   rw [pad,LinearMap.sub_apply,map_sub]; change dLin (fits he v) - bridgeEquiv G n ((bridgeEquiv G n).symm _)=_; rw [LinearEquiv.apply_symm_apply,LinearMap.comp_apply,sub_self]
lemma glows (a:E): Pert.Orb.fixing a= (∑ x, Inner.inner ℝ (takeDiv x a) (takeDiv x a)) /4:= by simp_rw [real_inner_self_eq_norm_sq];rfl
lemma curl_grad (v:Pert.Orb.Zero G n)(x i j): curL x i j (gZ v) = 0:= by change Pert.Orb.cur (Pert.Orb.grad v.val) x i j = _; unfold Pert.Orb.cur Pert.Orb.grad; rw [add_right_comm x]; abel
include he
lemma cut_grad (v:Pert.Orb.Zero G n): cut (gZ v)=0:= by
   have he' : score (cut (gZ v)) (cut (gZ v))=0:= by
      have ht:= cut_pow he (gZ v); rw [form,glows] at ht; simp_rw [curl_grad,inner_zero_left,ite_self,Finset.sum_const_zero] at ht; change (0+(∑ x,Inner.inner ℝ (takeDiv x (gZ v)) (takeDiv x (gZ v)))) /2= _ at ht; linarith [ht]
   have H:jet fiscal 2 (cut (gZ v))=0:= by rw [Orb.second_jet] at he'; exact (mul_eq_zero.mp he').resolve_left (by norm_num)
   by_contra hp; obtain ⟨c,hc,h⟩:= (saddle (G:=G) he).slope; specialize h (cut (gZ v)); rw [show (saddle _).P _ _=2 * _ from Orb.second_jet _,H] at h; exact (not_lt_of_ge h) (by rw [mul_zero,zero_div]; positivity)
lemma cut_pad (v : A):cut (pad he v)=v:= by unfold pad; rw [LinearMap.sub_apply,map_sub]; change cut _ - cut (gZ _)=_; rw [cut_grad he,sub_zero,cut_self]
lemma pad_fit (v:A)(p:E): cost.P (pad he v) p=(saddle he).P v (cut p):= by
   let a:= pad he v; have ht x: Pert.Orb.form x x= (saddle (G:=G) he).P (cut x) (cut x)+_:= cut_pow he x
   have heq := ht (a+p); rw [map_add,LinearMap.map_add (saddle (G:=G) he).P,LinearMap.add_apply, map_add,map_add,(saddle he).turns (cut p) (cut a)] at heq
   rw [show form (a+p) (a+p)= form a a+form a p+(form a p+ form p p) by simp_rw [Pert.Orb.form_add, Pert.Orb.form_symm a (a+p), Pert.Orb.form_symm p (a+p), Pert.Orb.form_add, Pert.Orb.form_symm p a], ht p, ht a] at heq
   have hV (x:Site n): takeDiv x a=0:= congr_fun (congr_arg Subtype.val (pad_div he v)) x
   simp_rw [glows,map_add (takeDiv (G:=G) _),hV,zero_add,inner_zero_left,Finset.sum_const_zero] at heq
   rw [cut_pad] at heq; change Pert.Orb.form a p=_; linarith [heq]
end YM.PositionX.Feyn
