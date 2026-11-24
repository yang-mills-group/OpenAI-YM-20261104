import YM.SignedWilsonExpansion.PlaneAxes
namespace YM.SignedWilsonExpansion.AxisChoice
/-! Factor before projecting. Moment variables Fourier units. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "P" => FourP
local notation "X" => Slice.rib
local notation "T" => tangent
local infixl:70 "⬩" => innerP
local notation "δ" => Slice.delta
local notation "e" => AxisChoice.direction
variable {h:ℝ→ℝ}
-- unprojected pieces
def TX (h:ℝ→ℝ)(i j:Axis)(p q k:P):ℝ:= ∑ u:Axis,∑ v:Axis, precision u v k * (2*feather ( yMark 1 2 ) h u i v j k p (-k) q )
def VX (h:ℝ→ℝ)(i j:Axis)(p q k:P):ℝ:= ∑ u:Axis,∑ v:Axis, precision u v k * Bubble.center h 1 2 u i v j k p (-k) q (p+q)
def UX (h:ℝ→ℝ)(i j:Axis)(p q k:P):ℝ:= ∑ u:Axis,∑ v:Axis,4*k.sq*flow k u*Bubble.paint h (k+(p+q)) 1 2 v * h0 u v i j
def RX (h:ℝ→ℝ)(i j:Axis)(p q k:P):ℝ:= ∑ u:Axis,∑ v:Axis,4*k.sq*flow k u*Bubble.paint h (k+(p+q)) 1 2 v * (2*feather X h u i v j k p (-k-(p+q)) q )
lemma assembly (p q k:P)(i j:Axis): TraceE.complete h 1 2 p q i j k= TX h i j p q k + TX h j i q p k + VX h i j p q k + VX h j i q p k +
         UX h i j p q k+ RX h i j p q k + RX h j i q p k:= by
    unfold TraceE.complete TX VX UX RX; simp only [leafPrice,body, flow, mul_add, Finset.sum_add_distrib]; rw [ add_comm q p ]; abel

variable (k p q r:P)(u v:Axis)(i j:Test)(x y:ℝ)
local notation "Y" => (ℝ×ℝ)
-- factorization removes longitudinal components at fixed both momenta
lemma rib_neg (i:Axis) : X u i v p q r = -X v i u r q p:=by unfold Slice.rib; rw [show Slice.delta u i=Slice.delta i u from (by simp_rw [Slice.delta,eq_comm (a:=u) (b:=i)]), show Slice.delta v i=Slice.delta i v from (by simp_rw [Slice.delta,eq_comm (a:=v) (b:=i)]),show Slice.delta v u=Slice.delta u v from (by simp_rw [Slice.delta,eq_comm (a:=v) (b:=u)])]; simp only [Pi.sub_apply]; ring -- fix
def weight (h:ℝ→ℝ)(x:ℝ):ℝ:= h x * x
local notation "Z" => weight h
lemma out_paint : Bubble.paint h p 1 2 u=Z p.sq * flow p u:=rfl
def drum (k:P)(i:Test)(x:ℝ):P:= (-2*k (e i)) • flow k + (2*x*(value k i+x)) • T i
def beat (i:Axis)(k p:P): P:=fun u=>∑ l:Axis,X u i l k p (-(k+p))*flow (k+p) l
lemma root_f : beat (e i) k (x • T i)=drum k i x + (value k i+x) • k:= by
    -- finite pin/passage; lifts ∑ l on plane exactly.
    funext u
    have he: (1:Axis)≠2:= by decide
    have hx(f:Axis→ℝ)(k:P): (∑ l',f l'*flow k l')=-f 1*k 2+ f 2*k 1:= by unfold flow Energy.leg; simp [mul_sub,mul_ite, Finset.sum_sub_distrib]; ring
    unfold beat drum; rw [hx]; by_cases ht:u=(1:Axis) <;> by_cases hp:u=(2:Axis) <;> cases i <;>
     simp [* ,value,Slice.rib,Slice.delta,tangent,direction,unitV,spike, Pi.single_apply, eq_comm (a:=(1:Axis)) (b:=u), eq_comm (a:=(2:Axis)) (b:=u), eq_comm (a:=(2:Axis)) (b:=(1:Axis)),flow, Energy.leg] <;> ring

def speaker (h:ℝ→ℝ)(k:P)(i:Test)(x:ℝ):P := weight h (slide k x i).sq • drum k i x -- `h` hygienic binder likely unused/different.
lemma speak_v (h:ℝ→ℝ)(i j:Axis)(p q k:P):
    VX h i j p q k=4* ( weight h (k+p).sq * weight h (-k+q).sq * matP k (beat i k p) (beat j (-k) q) ):= by
    rw [VX]; have ht: k+p-(p+q)=-(-k+q):= by abel
    unfold Bubble.center matP beat; simp only [LinearMap.mk₂_apply,ht, out_paint, Landau.sq_neg,flow_neg]; -- signs need -(-k+q) for X right argument; neg_neg.neg_neg remove
    simp only [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum, Pi.neg_apply]
    apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _ -- inspect ∑ l order 
    conv_rhs=> rw [ Finset.sum_comm ]
    refine Finset.sum_congr rfl fun l _=> Finset.sum_congr rfl fun m _=> ?_; ring
lemma back_v (u:Axis)(i:Axis)(K:P)(p:P) : beat i (-(K+p)) p u= ∑ l:Axis,X l i u K p (-(K+p))*flow K l:= by
    unfold beat; have he: -(K+p)+p= -K:=by abel
    rw [ show (-(K+p)+p) = -K from he, neg_neg, flow_neg ]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [rib_neg]; simp -- args placeholders
lemma speak_r (h:ℝ→ℝ)(i j:Axis)(p q k:P) :
    RX h i j p q k=8*k.sq*h (k+p).sq * weight h (k+(p+q)).sq * matP (k+p) (beat i (-(k+p)) p) (beat j (k+p) q):= by
    let K:=k+p; let S:= K+q
    let C:= -(k+p+q)
    have ht(v:Axis):beat j (k+p) q v=-(∑ l:Axis,X l j v C q (k+p)*flow (k+(p+q)) l):= by
       rw [ show k+(p+q)= S by rw [← add_assoc] ]; obtain he:= back_v v j C q; unfold C at he; have hz: -(k+p+q)+q=-(k+p):=by abel
       rw [hz,neg_neg,flow_neg] at he; simp_rw [Pi.neg_apply,mul_neg,Finset.sum_neg_distrib] at he; exact he
    unfold RX; simp_rw [feather, matP, LinearMap.mk₂_apply, ht, back_v _ i, show -k-(p+q)=C from (by unfold C; abel), out_paint]
    simp only [ ← Finset.sum_neg_distrib, Finset.sum_mul, Finset.mul_sum ]; -- permute right l m αu .. -> (u,v,l,m)
    have swirl(f:Axis→Axis→Axis→ℝ) : ∑ l:Axis,∑ v:Axis,∑ u:Axis,f l v u= ∑ u:Axis,∑ l:Axis,∑ v:Axis,f l v u:= by
        conv_rhs=> rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro _ _; rw [Finset.sum_comm]
    conv_rhs=> enter [2,v]; rw [swirl]
    conv_rhs=> rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _; conv_rhs=> rw [swirl]
    refine Finset.sum_congr rfl fun v _=> Finset.sum_congr rfl fun l _=> Finset.sum_congr rfl fun m _=>?_ ; unfold bond; ring

lemma closed_r (K:P) : matP K p K=0:= by rw [matrix_comm, projector]
lemma arrival_v (h:ℝ→ℝ)(i j:Test)(k:P)(x y:ℝ) :
    VX h (e i) (e j) (x • T i) (y • T j) k=4*matP k (speaker h k i x) (speaker h (-k) j y):= by
       rw [speak_v, root_f,root_f]; unfold speaker; simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply, projector, closed_r,map_neg,smul_eq_mul, neg_zero,mul_zero,add_zero, slide]; ring
lemma arrival_r (h:ℝ→ℝ)(i j:Test)(k:P)(x y:ℝ) :
    RX h (e i) (e j) (x • T i) (y • T j) k =
      let p:= slide k x i; 8*k.sq*h p.sq * matP p ( drum (-p) i x ) ( speaker h p j y ):= by
       simp only; rw [speak_r,root_f,root_f]; unfold speaker slide; rw [ show ∀ A B:P,∀ z r:ℝ,∀ p:P, matP p (A+z • (-p)) (B+r • p)= matP p A B from fun A B z r p=> by simp only [map_add,map_smul,map_neg,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.neg_apply,projector,closed_r,neg_zero,smul_zero,add_zero] ]; rw [map_smul,← add_assoc k]; change _= (8*k.sq)*(h _) *(weight _ _ * _); ring

-- crucial covariance factor: left vector below has vanishing curl component pairing to extent(k+p).
lemma negative_arm (k:P)(i:Test)(x:ℝ): drum (-slide k x i) i x =
     -(2*k (e i)) • flow (slide k x i) - ( 2*x*value k i ) • T i:= by
    have he: slide k x i (e i)=k (e i):= by simp only [slide,Pi.add_apply,Pi.smul_apply,tick,smul_zero,add_zero]
    have ht: value (slide k x i) i=value k i+x:= by unfold value; rw [value_shift, delta_self, mul_one]
    have hr(k:P): value (-k) i= -value k i:= by unfold value; rw [flow_neg]; rfl
    unfold drum; rw [ Pi.neg_apply,he,flow_neg,hr,ht ]; module
lemma left_extent (k:P)(i:Test)(x:ℝ) : matP (slide k x i) ( drum (-slide k x i) i x ) (extent (slide k x i) ) =
    -2*x*value k i*(value k i+x)*(k.sq-disk k):= by rw [ negative_arm,map_sub,map_smul,map_smul, LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.smul_apply, belongs, plane_tan ]; unfold value; rw [ value_shift, delta_self, strut,grown ]; unfold value; simp_rw [smul_eq_mul]; ring

-- smoothness
section sm
abbrev Panel := Axis→Axis→P→P→ℝ
def sample (U:P×P→ℝ)(p q:P): ℝ×ℝ→ℝ:= fun x=> U (x.1 • p,x.2 • q)
abbrev daily (F:Panel) (i j:Test) : Y→ℝ:= sample (Function.uncurry (F (AxisChoice.direction i) (AxisChoice.direction j))) (T i) (T j)
def bill (F:Panel) :ℝ:= ∑ i:Test,∑ j:Test,tooth (daily F i j)
abbrev Smooth (F:Panel) : Prop:=∀ i j:Test,ContDiff ℝ ∞ (daily F i j)
variable {F:Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (he:ContDiff ℝ ∞ h)
include he
omit he
@[local fun_prop] lemma poly_g (v:Axis) {c: F→ P}(h:ContDiff ℝ ∞ c): ContDiff ℝ ∞ (fun x=> Energy.leg 1 2 v (c x)):= by unfold Energy.leg; split_ifs <;> fun_prop
@[local fun_prop] lemma poly_p (i j:Axis){f:F→P} (h:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (fun x=> precision i j (f x)):= by unfold precision Momentum.sq Landau.delta; split_ifs<;>fun_prop
include he
lemma warmT : Smooth (fun i j p q=> TX h i j p q k) := by intro i j; unfold daily sample TX feather yMark Slice.rib bond Momentum.sq Function.uncurry; fun_prop
lemma warmR : Smooth (fun i j p q=> RX h i j p q k) := by intro i j; unfold daily sample RX feather Slice.rib Bubble.paint bond flow Momentum.sq Function.uncurry; fun_prop
lemma warmU : Smooth (fun i j p q=> UX h i j p q k) := by intro i j; unfold daily sample UX Bubble.paint flow Momentum.sq Function.uncurry; fun_prop
lemma warmV : Smooth (fun i j p q=> VX h i j p q k) := by intro i j; unfold daily sample VX Bubble.center Slice.rib Bubble.paint Momentum.sq Function.uncurry; fun_prop
omit he
variable {U V:Panel}
lemma Smooth.swaps (h:Smooth U): Smooth (fun i j p q=> U j i q p):= fun i j=> (h j i).comp (contDiff_snd.prodMk contDiff_fst)
lemma Smooth.add (h:Smooth U)(hp:Smooth V): Smooth (fun i j p q=>U i j p q+V i j p q):= fun i j=>(h i j).add (hp i j)
lemma detail : (fun (x y:ℝ)=>daily U i j (x,y))= (fun x y=> U (e i) (e j) (x • T i) (y • T j)):=rfl
lemma add_b (hp:Smooth U)(hx:Smooth V): bill (fun i j p q=> U i j p q+ V i j p q)= bill U + bill V:= by
    unfold bill; simp_rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> tooth_add (hp i j) (hx i j)
lemma sym_b (hp:Smooth U): bill (fun i j p q=> U j i q p)=bill U:= by
    unfold bill; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Heter.swap (hp i j)
lemma through (U:Panel)(hp:Smooth U)(i:Test): deriv (fun x:ℝ=>∑ j:Test, Heter.dY (daily U i j) x) 0=∑ j:Test,tooth (daily U i j):= deriv_fun_sum (fun j _=> (Heter.dY_s (hp i j)).differentiable (by simp) _)
lemma through_all (U:Panel)(hp:Smooth U) : deriv (fun x:ℝ=>∑ i:Test,∑ j:Test,Heter.dY (daily U i j) x) 0=bill U:= by
    unfold bill; rw [deriv_fun_sum]; exact Finset.sum_congr rfl (fun i _=> through U hp i)
    exact fun i _=> (ContDiff.sum (fun j (_:j∈Finset.univ)=>Heter.dY_s (hp i j))).differentiable (by simp) _
lemma thru (f:Test→Y→ℝ)(hp:∀ i:Test,ContDiff ℝ ∞ (f i)) : ∑ j:Test,Heter.dY (f j) x=Heter.dY (fun y=>∑ j:Test,f j y) x:= by unfold Heter.dY; rw [ deriv_fun_sum ]; exact fun j _=> ((hp j).comp (f:=fun t:ℝ=>(x,t)) (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _
lemma row (i:Test)(j:Test)(F:Panel) : ∀ x:ℝ,Heter.dY (daily F i j) x = deriv (fun y:ℝ=> F (e i) (e j) (x • T i) (y • T j)) 0 := fun _=>rfl

end sm

end
end YM.SignedWilsonExpansion.AxisChoice
