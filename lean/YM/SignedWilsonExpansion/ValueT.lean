import YM.SignedWilsonExpansion.Quartic
namespace YM.SignedWilsonExpansion.AxisChoice
/-! second projection of TX. Keep relative signs between *momentum* vectors tested -- Taylor differentiation doesn't strip a pole or momentum delta.
 -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "P" => FourP
local notation "T" => tangent
local infixl:70 "⬩" => innerP
local notation "δ" => Slice.delta
local notation "e" => AxisChoice.direction
variable {h:ℝ→ℝ} (he: ContDiff ℝ ∞ h)
variable (k p q r:P)(u v l m:Axis)(i j:Test)(x y:ℝ)
local notation "Z" => weight h
local notation "Λ" => Momentum.sq
local notation "G" => value
local notation "X" => Slice.rib
lemma color_y : yMark 1 2 v (e j) m p (y • T j) r = yMark 1 2 v (e j) m p 0 r +2*play 1 2 m v * y:= by
    have he : Energy.leg 1 2 (e j) 0=0:= by simp [Energy.leg]; -- all ite
    have ht: Energy.leg 1 2 (e j) ( y • T j )=y:= value_origin j y
    unfold yMark; rw [ ht, he ]; ring
def pat (p:P)(c:Axis)(v m:Axis)(k:P):ℝ:=
    ∑ u:Axis,∑ l:Axis, precision u v k * precision l m (k+p)* X u c l k p (-(k+p))
def photo (p:P)(c:Axis)(k:P):ℝ:= pat p c 2 1 k-pat p c 1 2 k
lemma striped (p:P)(c:Axis)(k:P) :
    (∑ u:Axis,∑ v:Axis,∑ l:Axis,∑ m:Axis,
        precision u v k * precision l m (k+p) * X u c l k p (-(k+p)) * play 1 2 m v)=photo p c k := by
    have h(f:Axis→Axis→ℝ) : (∑ v:Axis,∑ m:Axis,f v m*play 1 2 m v)=f 2 1-f 1 2:= by unfold play; simp only [mul_sub,Finset.sum_sub_distrib]; unfold Slice.delta; simp [mul_ite,ite_mul]
    unfold photo; rw [← h (fun v m=>pat p c v m k) ]; unfold pat; simp_rw [Finset.sum_mul]
    rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro v _; conv_rhs=> rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]
lemma warm_y (p:P)(c:Axis) :
    TX h c (e j) p (y • T j) k= TX h c (e j) p 0 k +
         -4*y*h (Λ (k+p))*photo p c k:= by
    unfold TX; simp_rw [ feather,color_y ]; rw [ ← striped ]; simp only [ Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_neg_distrib ];
    refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=> Finset.sum_congr rfl fun l _=> Finset.sum_congr rfl fun m _=> ?_; unfold bond; ring

def faith (p:P)(i:Test):ℝ:=
    -4*p.sq*(p.sq-disk p)-2*p.sq*p (AxisChoice.direction i)^2
def amount (x:ℝ)(p:P)(i:Test):ℝ:=
    faith p i + x*( 2*p (AxisChoice.direction i)^2 +4*value p i^2-4*p.sq )*value p i +
       x^2*( 2*value p i^2-2*p.sq )
set_option maxHeartbeats 1200000 in
lemma capT : photo (x • T i) (e i) p=x*amount x p i:= by
    unfold photo pat; cases i <;> simp [direction,tangent,unitV,spike, Pi.single_apply, Slice.rib,Slice.delta, amount,faith,disk,value,flow,Energy.leg,precision,Landau.delta, Momentum.sq, show Finset.univ (α:=Axis)={0,1,2,3} from rfl ] <;> ring 

local notation "F" => fun i j p q=> TX h i j p q k
lemma halo_step : dY (daily F i j) x = -4*h (Λ (slide k x i))*photo (x • T i) (e i) k := by
    rw [row]; beta_reduce; simp_rw [warm_y k j]; -- hp parse
    let p:= slide k x i; let B:=photo (x • T i) (e i) k; let b:= -4*h p.sq*B; let v:= TX h (e i) (e j) (x • T i) 0 k; convert! ((( hasDerivAt_id' (0:ℝ)).const_mul b).const_add v).deriv using 1; · congr 1; ext x; unfold v b B p slide; ring
    unfold b; ring
include he
lemma Tprice : bill F=64*(Λ k)^2*h (Λ k)-48*Λ k*disk k*h (Λ k):= by
    let L t (i:Test):= h (Λ (slide k t i))*amount t k i * (-4)
    have hv(i j:Test) : tooth (daily F i j)= h k.sq* faith k i * (-4):= by
        have h₀(x):dY (daily F i j) x = L x i * x:= by rw [halo_step,capT]; unfold L; ring
        let f t:= L t i; have H:Differentiable ℝ f:= by unfold f L amount slide Momentum.sq; have hm:= he.differentiable (by simp); fun_prop
        rw [ tooth, funext h₀, ( ( ( H 0 ).hasDerivAt ).fun_mul (hasDerivAt_id' (0:ℝ)) ).deriv ]; simp [f,L,amount]
    unfold bill; simp_rw [hv]; unfold disk; simp [faith, direction, disk]; ring

end
end YM.SignedWilsonExpansion.AxisChoice
