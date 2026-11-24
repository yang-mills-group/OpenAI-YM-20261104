import YM.SignedWilsonExpansion.Heter
namespace YM.SignedWilsonExpansion.AxisChoice
/-! Test uses TWO momentum derivatives at 0, colored AA perpendicular to
the timelike axis. Linear curl F12, not electric for chosen time =3. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
abbrev Test := Bool
abbrev direction (i:Test) : Axis:= if i then 2 else 1
local notation "e" => direction
abbrev unitV (i:Axis):FourP:= spike i
abbrev tangent (i:Test): FourP:= if i then unitV 1 else -unitV 2
local notation "P" => FourP
local notation "X" => Slice.rib
local notation "T" => tangent
def flow (p:P): P:=fun i=>Energy.leg 1 2 i p
def kernel (p:P)(u:Axis):ℝ:= flow p u
def extent (p:P) : P:=fun u=> if u=1∨u=2 then p u else 0
local notation "δ" => Slice.delta
def disk (p:P):ℝ:= p 1 ^2+p 2 ^2
def innerP (p q:P):ℝ:=∑ i:Axis,p i*q i
local infixl:70 "⬩" => innerP
lemma inner_sq (p:P): p⬩p=p.sq:= by unfold Momentum.sq innerP; simp only [pow_two]
lemma inner_swap (p q:P): p⬩q=q⬩p:= by simp_rw [innerP]; refine Finset.sum_congr rfl fun i _=>?_ ; ring
def slide (p:P)(x:ℝ)(i:Test) : P:= p+x • T i
variable (p q r:P)(i:Test) (x:ℝ)(u v:Axis)
abbrev value (p:P)(i:Test):= flow p (direction i)
lemma flow_neg : flow (-p)= -flow p:= funext fun _=> Walk.leg_neg
lemma value_shift : flow (slide p x i) u=flow p u+x*δ u (e i):= by
    cases i <;> unfold flow slide Energy.leg Slice.delta <;> simp only [direction,tangent,unitV,spike,Bool.false_eq_true,Bool.true_eq,↓reduceIte,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply,Pi.neg_apply] <;> by_cases h:u=(1:Axis) <;> by_cases hx:u=(2:Axis) <;> simp [*] <;> ring
lemma value_origin : flow (x • T i) (e i)=x:= by
   have ht:= value_shift 0 i x (e i); simpa [slide, Slice.delta, show flow 0 (e i)=0 from (by unfold flow Energy.leg; simp)] using ht
lemma fun_flow (p q:P): flow (p+q)=flow p+flow q:= by funext i; unfold flow Energy.leg; by_cases he:i=(1:Axis) <;> by_cases ht:i=(2:Axis) <;> simp [*,Pi.add_apply] <;> ring
lemma flow_plane : extent (flow p)=flow p:= by funext i; unfold extent flow Energy.leg; split <;> next h=> first| rfl| simp [not_or] at h; simp [h]
lemma cut_unit : extent ( T i )= T i:= by
    funext u; unfold extent; split_ifs <;> next he=> first| rfl| cases i <;> simp [tangent,unitV,spike, not_or] at he <;> simp [tangent,unitV,spike, Pi.single_apply, he, Ne.symm he.2,Ne.symm he.1 ]
lemma linear_disk (x:P)(v:P) : extent (x+v)= extent x+ extent v:= by funext i; unfold extent; simp only [Pi.add_apply]; split_ifs <;> simp
lemma disk_neg : extent (-p)= -extent p:= by funext i; unfold extent; simp only [Pi.neg_apply]; split_ifs <;> simp
lemma dial_neg : disk (-p)=disk p:= by simp [disk]
lemma price_disk (x:P)(v:P)(t:ℝ) : extent (t • x)= t •extent x:= by funext i; unfold extent; simp only [Pi.smul_apply]; split_ifs <;> simp
lemma delta_self : δ u u=1:= by simp [Slice.delta]
lemma tick : T i (e i)=0:=by cases i <;> simp [direction,tangent,unitV,spike,Pi.single_apply]; -- distinct
lemma feeling : flow p⬩T i= -p (e i):= by cases i <;> simp [innerP,tangent,direction,flow,Energy.leg,unitV,spike,Pi.single_apply,ite_mul,mul_ite]; -- maybe ring
lemma scope : T i⬩p=value p i:= by cases i <;> simp [innerP,tangent,direction,flow,Energy.leg,value,unitV,spike,Pi.single_apply,ite_mul,mul_ite]
lemma scopeE : T i⬩extent p=value p i:= by rw [scope]; cases i <;> simp [extent,tangent,direction,value,flow, Energy.leg]
lemma zero_twist : flow p⬩p=0 := congr_fun (Walk.progress (a:=1) (b:=2)) p
lemma dashPlane : flow p⬩extent p=0:= by
    unfold innerP; simp only [extent,mul_ite]; have he : ∀ i:Axis,flow p i*(if i=1∨i=2 then p i else 0)=flow p i*p i:= by intro i; split_ifs <;> next h=> first|rfl|simp [not_or] at h; simp [flow,Energy.leg,h] ; -- hp
    simp_rw [ ← mul_ite ]; exact ( Finset.sum_congr rfl (fun i _=> he i) ).trans (zero_twist p)
lemma dashCost : p⬩extent p=disk p:= by
    unfold innerP extent
    simp [show Finset.univ (α:=Axis)= {0,1,2,3} from rfl]
    unfold disk; ring
lemma scalar_cost : extent p⬩extent p=disk p:= by rw [← dashCost p]; unfold innerP; apply Finset.sum_congr rfl; intro i _; unfold extent; split_ifs<;> ring
lemma tangent_square : T i⬩T i=1:= by rw [scope]; cases i <;> simp [direction,tangent,unitV,spike,value,flow,Energy.leg]
lemma total : (∑ i:Test,value p i*p (e i))=0:=by simp [tangent,direction,unitV,spike,value,flow,Energy.leg]; ring
lemma fuel : (∑ i:Test, value p i ^2)=disk p:= by simp [tangent,direction,unitV,spike,value,flow,disk, Energy.leg]
lemma stock : (∑ i:Test,p (e i)^2)=disk p:= by simp [direction,disk,add_comm]
lemma grow : (∑ i:Test, value p i*(T i u))=extent p u:= by
    simp only [Fintype.sum_bool]
    have he: (1:Axis)≠2:=by decide
    by_cases h:u=(1:Axis)<;> by_cases hv:u=(2:Axis)<;> simp [*,value,flow,tangent,direction,extent,Energy.leg,unitV,spike,Pi.single_apply,eq_comm, he ]

def pair2 : P →ₗ[ℝ] P →ₗ[ℝ] ℝ:= LinearMap.mk₂ ℝ (fun x y=> x⬩y)
   (fun v x u=>by simp [innerP,add_mul,Finset.sum_add_distrib])
   (fun t v x=>by simp [innerP, mul_assoc, Finset.mul_sum])
   (fun u v x=>by simp [innerP,mul_add, Finset.sum_add_distrib])
   (fun t v x=>by simp [innerP,mul_left_comm,Finset.mul_sum])
def matP (k:P): P→ₗ[ℝ] P→ₗ[ℝ] ℝ:= LinearMap.mk₂ ℝ (fun A B=>∑ u:Axis,∑ v:Axis, precision u v k * A u * B v)
   (fun u v x=>by simp only [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib])
   (fun t u v=>by simp only [Pi.smul_apply,smul_eq_mul, Finset.mul_sum,mul_left_comm t (precision _ _ _),mul_assoc])
   (fun u v x=>by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib])
   (fun t u v=>by simp only [Pi.smul_apply,smul_eq_mul, Finset.mul_sum,mul_assoc]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by ring)
lemma tool: pair2 p q=p⬩q:=rfl
lemma matrix_q : matP p q r=p.sq*(q⬩r) - (p⬩q)*(p⬩r):= by
    change ∑ u:Axis,∑ v:Axis, precision u v p * q u *r v=_
    unfold innerP; simp only [ precision, sub_mul,Finset.sum_sub_distrib]; simp [Landau.delta,ite_mul, Finset.sum_mul,Finset.mul_sum,mul_assoc,mul_left_comm ]; rw [Finset.sum_comm]; simp [mul_left_comm]
lemma matrix_comm (v:P) : matP p q v=matP p v q:= by rw [ matrix_q,matrix_q,inner_swap q ]; ring
lemma projector : matP p p q=0:= by rw [matrix_q, inner_sq ]; ring
lemma belongs : matP p ( flow p ) ( extent p ) =0:= by rw [matrix_q, inner_swap _ (flow p), zero_twist, dashPlane]; ring
lemma streak : matP p ( extent p ) (extent p)=disk p*(p.sq-disk p):= by rw [matrix_q,scalar_cost,dashCost]; ring
lemma plane_tan : matP p (T i) ( extent p)=value p i*(p.sq-disk p):= by rw [matrix_q,scopeE, inner_swap p,scope,dashCost]; ring
lemma strut : (slide p x i).sq=p.sq+2*value p i*x+x^2:= by unfold slide; simp_rw [← inner_sq, ← tool]; simp only [map_add,map_smul,LinearMap.smul_apply,LinearMap.add_apply,tool,scope, show value (T i) i=1 from ((scope (T i) i).symm.trans (tangent_square i)), inner_swap p (T i),smul_eq_mul]; ring
lemma grown : disk (slide p x i)=disk p+2*value p i*x+x^2:= by
    cases i <;> simp [value,slide,extent,tangent,direction,unitV,spike,Pi.single_apply,flow, Energy.leg,disk] <;> ring
lemma free_neg {k:P}: matP (-k)= matP k:= by apply LinearMap.ext; intro p; apply LinearMap.ext; intro q; simp only [matrix_q,Landau.sq_neg,innerP,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]; ring
end
end YM.SignedWilsonExpansion.AxisChoice
