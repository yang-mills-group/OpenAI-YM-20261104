import YM.X.Reed.Sprout
import YM.Next.RANK.Sky
/-!
Centered shifts calculus and polynomial growth and continuum limits.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Next.Rank.CellsInt Tensor TensorProduct Filter MeasureTheory Metric Finset Function
open scoped Topology ContDiff BigOperators
variable {V : Type} [NormedAddCommGroup V][NormedSpace ℝ V] {n:ℕ}
def burst (i:Axis) : T E4 V (n+1) →ₗ[ℝ] T E4 V n where
   toFun A:= (n+1:ℝ) • A.curryLeft (basis i)
   map_add' A B:= by ext1 v; simp [smul_add]
   map_smul' r A:= by ext1 v; simp [smul_comm r]
lemma burst_eval (i:Axis)(A:T E4 V (n+1))(v): burst i A v=(n+1:ℕ) • A.curryLeft (basis i) v:= by change ((n+1:ℝ) • A.curryLeft (basis i)) _ =_; rw [← Nat.cast_smul_eq_nsmul ℝ]; simp
lemma burst_sym {A:T E4 V (n+1)}(h:Tensor.Sym A)(i:Axis): Tensor.Sym (burst i A):= by intro v s; rw [burst_eval,burst_eval,freeze_sym A h (basis i) v s]
lemma burst_diag {A:T E4 V (n+1)}(h:Tensor.Sym A)(i:Axis)(x:E4) : diagonal (burst i A) x=Maxwell.grad i (diagonal A) x:= by rw [Maxwell.grad, Analysis.D,differential_diagonal A h]; exact burst_eval ..
def reach (δ:E4): T E4 V n →ₗ[ℝ] Cover→V:= LinearMap.pi (fun v=> gather (mapZ v+δ))
def rewind (f:Cover→V)(i:Axis):Cover→V:= fun z=>stepValue f i (z-step i)
lemma step_time (z:Cover)(δ:E4)(i:Axis):
    mapZ z + (δ+tip i) +tip i=mapZ (z+step i)+δ:= by rw [mapZ_step]; unfold tip; module
lemma step_grabs {A:T E4 V (n+1)}(h:Tensor.Sym A)(δ:E4)(i:Axis): stepValue (reach δ A) i=reach (δ+tip i) (burst i A):= by
    have he : burst i A=((↑(n+1:ℕ)):ℝ) • A.curryLeft (basis i):= by ext1 v; rw [burst_eval]; simp only [Nat.cast_smul_eq_nsmul, smul_apply]
    funext z; change gather _ _ - gather (mapZ z +δ) A=gather (mapZ z + (δ+tip i)) _; rw [←step_time,he,map_smul, Nat.cast_smul_eq_nsmul ℝ,←grab A _ i h]; congr 2; abel
lemma rewind_grabs {A:T E4 V (n+1)}(h:Tensor.Sym A)(δ:E4)(i:Axis): rewind (reach δ A) i=reach (δ-tip i) (burst i A):= by
    unfold rewind; rw [step_grabs h]; funext z; change gather (mapZ (z-step i)+_) _=gather (mapZ z+_) _; have he :=step_time (z-step i) δ i; rw [sub_add_cancel] at he; congr 2; rw [show mapZ z+(δ-tip i)= (mapZ z+ δ)-tip i by abel, ← he]; abel
lemma reach0 (A:T E4 V 0)(δ:E4)(f:Fin 0→E4): reach δ A=fun _=> A f:= by funext z; simp only [reach,gather,LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk,Fintype.sum_unique,pick,Fintype.sum_empty,block,whisk,prod_const_one,one_smul]; apply congr_arg; exact Subsingleton.elim ..
lemma top {A:T E4 V n}(h:Tensor.Sym A)(δ:E4)(l:Fin n→Axis)(z:Cover): jumps n l (reach δ A) z=(n.factorial:ℝ) • A (basis ∘ l):= by
    induction n generalizing δ with
    | zero=> rw [jumps,reach0 A δ (basis ∘ l)]; simp
    | succ n IH=> rw [jumps,step_grabs h,IH (burst_sym h _), burst_eval,ContinuousMultilinearMap.curryLeft_apply,←Nat.cast_smul_eq_nsmul ℝ,smul_smul, Nat.factorial_succ,Nat.cast_mul, mul_comm]; congr 2; funext j; exact Fin.cases rfl (fun _=>rfl) j
lemma higher {A:T E4 V n}(h:Tensor.Sym A)(δ:E4){k:ℕ}(hk:n<k)(l:Fin k→Axis): jumps k l (reach δ A)=0:= by
    induction k with
    | zero=>omega
    | succ k IH=>
       rw [jumps,hopped]; rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with he|he
       · subst k; funext z; unfold stepValue; rw [top h,top h,sub_self]; rfl
       rw [IH he]; exact jumps_zero 1 (fun _=>l 0)

variable {a : ℕ→ℝ} {x:ℕ→E4} {y:E4}
lemma touch (f : Fin n→Axis)(x:Axis→ℝ): ∏ i:Axis,(x i)^pick f i = ∏ i:Fin n, x (f i):= by
   induction n with
   | zero=> simp [pick]
   | succ n IH=>
     let j:= f 0
     have he i : pick f i = (if j=i then 1 else 0)+ pick (Fin.tail f) i:= by conv_lhs => rw [← Fin.cons_self_tail f]; exact pick_step ..
     simp_rw [he,pow_add]; rw [prod_mul_distrib, IH,prod_eq_single j,Fin.prod_univ_succ (fun i=> x (f i))]; swap; · intro w _ hw; simp [hw.symm]
     · simp [j]; left; rfl -- simplify
     simp
lemma sail (ha:Tendsto a atTop (𝓝 0)) {t:ℕ→ℝ}{u:ℝ}(ht:Tendsto (fun k=>a k*t k) atTop (𝓝 u))(n:ℕ):
    Tendsto (fun k=>a k^n*whisk n (t k)) atTop (𝓝 (u^n)) := by
   cases n with
   | zero=> simpa only [pow_zero,whisk,mul_one] using tendsto_const_nhds
   | succ n=>
     let f(k:ℕ)(i:ℕ):= a k*(t k + ((↑(n+1:ℕ)):ℝ)/2-(i+1:ℕ))
     have he k : a k^(n+1)*whisk (n+1) (t k)=a k*t k*∏ i∈range n,f k i:= by
        unfold whisk f;rw [prod_mul_distrib,prod_const,card_range,pow_succ]; ring
     simp_rw [he]; have hp i:Tendsto (fun k=> f k i) atTop (𝓝 u):= by
        unfold f; simp only [add_sub_assoc,mul_add]; simpa using ht.add (ha.mul_const (((↑(n+1:ℕ)):ℝ)/2-(i+1:ℕ)))
     convert ht.mul (tendsto_finsetProd _ fun i _=> hp i) using 1
     simp only [prod_const,card_range,pow_succ]; rw [mul_comm]

def bare (A:T E4 V n):E4→V:=fun y=> ∑ l:Fin n→Axis,(∏ i, y i ^pick l i) • A (basis ∘ l)
lemma yell (y:E4)(A:T E4 V n): bare A y=diagonal A y:= by
    induction n with
    | zero=> unfold bare diagonal; simp only [Fintype.sum_unique, touch, Fintype.prod_empty,one_smul]; apply congr_arg; exact Subsingleton.elim ..
    | succ n IH=>
       let B(i:Axis):= A.curryLeft (basis i); have he: diagonal A y= ∑ i:Axis, y i • diagonal (B i) y:= by
          rw [show diagonal A y= diagonal (A.curryLeft y) y by unfold diagonal; rw [ContinuousMultilinearMap.curryLeft_apply]; exact congr_arg A (funext (fun i=> Fin.cases rfl (fun _=>rfl) i))]; conv_lhs => enter [1,2]; rw [show y=∑ i:Axis,y i • basis i from Eq.symm (by ext1 i; simp)] -- name?
          simp only [map_sum,map_smul, _root_.sum_apply,diagonal,smul_apply]; rfl
       rw [he]; unfold bare; rw [← Equiv.sum_comp (Fin.consEquiv (fun _=>Axis)), Fintype.sum_prod_type]; apply sum_congr rfl; intro i _;rw [← IH (B i),bare,smul_sum]; apply sum_congr rfl; intro l _
       rw [touch,touch, Fin.prod_univ_succ, smul_smul]; congr 1; unfold B; rw [ContinuousMultilinearMap.curryLeft_apply]; apply congr_arg; funext j;exact Fin.cases rfl (fun _=>rfl) j

lemma twig (ha:Tendsto a atTop (𝓝 0))(hx:Tendsto (fun k=>a k • x k) atTop (𝓝 y))(A:T E4 V n) : Tendsto (fun k=>a k^n • gather (x k) A) atTop (𝓝 (diagonal A y)):= by
   rw [← yell]; unfold gather bare; simp only [LinearMap.coe_mk,AddHom.coe_mk,smul_sum,smul_smul]; apply tendsto_finsetSum _ ; intro l _
   have he k:a k^n*block (pick l) (x k)=∏ i:Axis,(a k^pick l i*whisk (pick l i) (x k i)):= by rw [prod_mul_distrib,touch l (fun _=> a k)]; simp only [prod_const, card_univ,Fintype.card_fin];rfl
   simp_rw [he]; refine Tendsto.smul_const (tendsto_finsetProd _ (fun i _=> sail ha ?_ _)) _; exact (EuclideanSpace.proj i).continuous.continuousAt.tendsto.comp hx
end YM.PositionX.Reed
