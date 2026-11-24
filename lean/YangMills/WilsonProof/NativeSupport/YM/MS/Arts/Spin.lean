import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Par
/-! # Linear rotations of auxiliary Euclidean dimensions -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open Momentum
variable {A B:Type}[Fintype A][Fintype B]{m n:ℕ}
lemma pair_left (a b:Momentum A): pairing a b=pairing b a:=by simp only [pairing]; apply Finset.sum_congr rfl; intro i _; ring
lemma pair_plus (a b c: Momentum A): pairing (a+b) c=pairing a c+pairing b c:= by simp only [pairing,Pi.add_apply,add_mul,Finset.sum_add_distrib]
lemma pair_times (t:ℝ) (a b:Momentum A): pairing (t • a) b=t*pairing a b:= by simp only [pairing,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
def innerL (a:Momentum A): Momentum A→L[ℝ] ℝ := ∑ i, a i • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:A=>ℝ) i
lemma inner_at (a b:Momentum A): innerL a b=pairing a b:= by rw [innerL,_root_.sum_apply]; rfl
lemma inner_norm (a:EuclideanSpace ℝ A): ‖a‖=√(Momentum.sq (WithLp.ofLp a)):= by rw [EuclideanSpace.norm_eq]; simp only [Momentum.sq,Real.norm_eq_abs,sq_abs]
lemma sq_gt (a:Momentum A)(h:a≠0): 0<Momentum.sq a:= lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2) (Momentum.sup_square a)

structure Spin (A:Type)[Fintype A] where
   turn : Momentum A≃L[ℝ] Momentum A
   rad : ∀ x y, pairing (turn x) (turn y)=pairing x y
namespace Spin
variable (K:Spin A)
def back : Spin A:= ⟨K.turn.symm,fun x y=> by nth_rw 2 [← K.turn.apply_symm_apply x,← K.turn.apply_symm_apply y]; rw [K.rad]⟩ -- nth_rw problem
@[simp] lemma front {x}: K.turn (K.back.turn x)=x:= K.turn.apply_symm_apply _
@[simp] lemma rear{x}: K.back.turn (K.turn x)=x:= K.turn.symm_apply_apply _
lemma fare (p:Momentum A): Momentum.sq (K.turn p)=Momentum.sq p:= by simp only [sq_eq,K.rad]
def sand : EuclideanSpace ℝ A≃ₗᵢ[ℝ] EuclideanSpace ℝ A:= by
   let P:= WithLp.linearEquiv 2 ℝ (Momentum A); refine ⟨(P.trans K.turn.toLinearEquiv).trans P.symm,fun p=>?_⟩; change ‖WithLp.toLp 2 (K.turn (P p))‖= _ ; rw [inner_norm, WithLp.ofLp_toLp,K.fare,inner_norm]; rfl
lemma volume : MeasurePreserving K.turn := by
    have h:= (PiLp.volume_preserving_ofLp A).comp (K.sand.measurePreserving.comp ( PiLp.volume_preserving_toLp A)); exact h
-- coordinates, orth relations
variable [DecidableEq A]
def profile (i j:A): ℝ:= K.turn (spray i) j -- order like seeder
lemma dual (i j:A): K.profile i j=K.back.profile j i := by
    unfold profile; have ht:= K.rad (spray i) (K.back.turn (spray j)); rw [front] at ht; simpa [pairing,spray,Pi.single_apply,ite_mul,mul_ite] using ht
lemma orth (p:Momentum A)(i:A): (∑ a:A,p a*K.profile a i)=K.turn p i:= by nth_rw 2 [← standardP p]; simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]; rfl -- nth rw
lemma weights (i j:A): (∑ a:A,K.profile i a* K.profile j a)=(if i=j then 1 else 0):= by change pairing (K.turn (spray i)) (K.turn (spray j))=_; rw [K.rad]; simp [pairing,spray,Pi.single_apply,(eq_comm (a:=i))]; -- inspect
end Spin
/-- canonical reflection -/
def wall (a:Momentum A)(t:ℝ): Momentum A→L[ℝ] Momentum A:= ContinuousLinearMap.id ℝ _ - t • (innerL a).smulRight a
lemma wall_pay (a:Momentum A)(t:ℝ)(b:Momentum A): wall a t b=b - (t*pairing a b) • a:= by simp only [wall,sub_apply,ContinuousLinearMap.id_apply,smul_apply,ContinuousLinearMap.smulRight_apply, inner_at,mul_smul]
lemma pair_sub (a b c:Momentum A): pairing a (b-c)=pairing a b-pairing a c:=by simp [pairing,mul_sub,Finset.sum_sub_distrib]
lemma pair_h (t:ℝ)(a b:Momentum A): pairing a (t • b)=t*pairing a b:=by rw [pair_left,pair_times,pair_left a]
lemma wall_sq (a:Momentum A)(h:a≠0)(x:Momentum A): pairing a (wall a (2/a.sq) x)=-pairing a x:= by rw [wall_pay,pair_sub,pair_h,←sq_eq]; have hh:=sq_gt a h; field_simp; ring
lemma reset (a:Momentum A)(h:a≠0): Involutive (wall a (2/a.sq)):= by
    intro x; rw [wall_pay,wall_sq a h x,wall_pay]; simp
lemma wall_inner (a:Momentum A)(h:a≠0)(x y:Momentum A) : pairing (wall a (2/a.sq) x) (wall a (2/a.sq) y)=pairing x y:= by
   -- expand with sign
   nth_rw 1 [pair_left (wall a _ x),wall_pay a _ x]; rw [pair_sub,pair_h,pair_left _ a,wall_sq a h y,pair_left (wall _ _ y),wall_pay a _ y,pair_sub,pair_h,pair_left x a]; ring

def tilt (a:Momentum A)(h:a≠0): Spin A where
   turn := (LinearEquiv.ofBijective ((wall a (2/a.sq))).toLinearMap ((reset a h).bijective)).toContinuousLinearEquiv
   rad:= wall_inner a h
lemma floors (a: Momentum A)(h:a≠0){x:Momentum A}(hp:pairing a x=0): (tilt a h).turn x=x := by change wall _ _ _ = _; rw [wall_pay,hp]; simp
lemma turns (a b: Momentum A)(h:a≠b)(hp:a.sq=b.sq): (tilt (a-b) (sub_ne_zero.mpr h)).turn a=b:= by
   change wall _ _ _=_; rw [wall_pay]; have H : pairing (a-b) a*2=(a-b).sq:= by
       simp_rw [sq_eq] at hp ⊢; have hx : ∀ c: Momentum A,pairing (a-b) c=pairing a c-pairing b c:= by intro c; rw [pair_left,pair_sub,pair_left c a,pair_left c b]; -- nxt
       simp_rw [hx,pair_sub,pair_left a b]; linear_combination hp
   have hx: (2/(a-b).sq)*pairing (a-b) a=1:= by have ht:=sq_gt _ (sub_ne_zero.mpr h); field_simp; rw [mul_comm,H]
   rw [hx]; simp
end YM.MS.Arts
