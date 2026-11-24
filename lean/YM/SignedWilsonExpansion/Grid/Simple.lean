import YM.SignedWilsonExpansion.Both
namespace YM.SignedWilsonExpansion.Overlap
/-! Additional off-plane overlap readout. Polynomial bills of the raw
four-dimensional Landau transverse contraction at a 02 probe of 12. Index
choice zero is a **spatial** index (time = 3 throughout the pair test).
Momentum arguments `p,q` differentiate genuinely transferring (localized)
mark; not setting `p=-q`. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Koszul MS.Plane MS.Plane.Flux MS.Landau MS.High MS.Landau.Detect MS.Landau.Detect.Mark
open FVA2 FVA2.Lambda Area Walk Bubble Heter TreeLine AxisChoice
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace
local notation "P" => FourP
local notation "L" => Momentum.sq
abbrev port (i:Bool) : Axis := if i then 2 else 0
abbrev side (i:Bool) : P:= if i then unitV 0 else -unitV 2
local notation "e" => port
local notation "T" => side
local notation "p" => fun (x:ℝ)(i:Bool) => x • (side i)
variable (h:ℝ→ℝ)(i j:Bool)(k:P)(x y:ℝ)
-- notation for scripting; all explicit variables k etc use `local ...` resolution (Lean hygiene tested)
local notation "a" => k 0
local notation "b" => k 1
local notation "c" => k 2
local notation "H" => weight h

lemma tQuiet (h:ℝ→ℝ)(i j:Bool)(k:P)(x y:ℝ): TX h (e i) (e j) (x • T i) (y • T j) k=TX h (e i) (e j) (x • T i) 0 k:= by
    have he : ∀ y:ℝ, Energy.leg 1 2 (port j) (y • side j)=0:= by intro y; cases j <;> simp [port,side,Energy.leg,unitV,spike]
    have hv : Energy.leg 1 2 (port j) (0:P)=0:= by simp [ Energy.leg ]
    simp only [TX,feather,yMark,he,hv]

def vCard : Bool→Bool→ ℝ
 | false,false => -16 * L k *(-a^2*b^2 - a^2*c^2 + a^2*c*x - a^2*c*y + a^2*x*y + b^2*x*y)
 | false,true => -16* L k *(-a*b^2*c - a*c^3 + a*c^2*x + b^2*x*y)
 | true,false => -16* L k *(-a*b^2*c - a*c^3 - a*c^2*y + b^2*x*y)
 | true,true => 16*(L k *b^2*c^2 - L k *b^2*x*y + L k *c^4 + a^2*b^2*x*y)

def uCard : Bool→Bool→ ℝ
 | false,false => 8* L k *(-b^2 - c^2 + c*x + c*y)
 | true,true => -8* L k *c^2
 | _,_ => 0

def rCard : Bool→Bool→ ℝ
 | false,false => -32* L k *(L k - 2*c*x + x^2)*(-a^2*b^2 - a^2*c^2 + a^2*c*x + a^2*c*y + b^2*x*y)
 | false,true => 32* L k *(L k - 2*c*x + x^2)*(a*b^2*c - a*b^2*x + a*c^3 - 2*a*c^2*x + a*c*x^2 - b^2*x*y)
 | true,false => -32* L k *(L k + 2*a*x + x^2)*(-a*b^2*c - a*c^3 + a*c^2*y - b^2*c*x + b^2*x*y - c^3*x + c^2*x*y)
 | true,true => 32* L k *(L k *b^2*c^2 - L k *b^2*x*y + L k *c^4 + a^2*b^2*x*y + 2*a*b^2*c^2*x + 2*a*c^4*x + b^2*c^2*x^2 + c^4*x^2)
lemma qAxis (F:Axis→ℝ): ∑ i:Axis, F i=F 0+F 1+F 2+F 3:= by exact Fin.sum_univ_four ..
-- Project away a longitudinal before pricing, rather than expanding 8-degree
-- terms which later cancel.
def arm0 : Bool → P
 | false => ( 2*b*x ) • unitV 0 + (2*a*(c-x)) • unitV 1+(-2*a*b) • unitV 2
 | true => (2*b*x) • unitV 0 + (2*c^2) • unitV 1 +(-2*b*c) • unitV 2
lemma second : beat (e i) k (p x i)= arm0 k x i + (if i then b else 0) • k:= by
    funext u; cases i <;> fin_cases u <;> simp (disch := decide) [arm0, beat, side, port, unitV, spike, Pi.single_apply, flow, Slice.rib, Slice.delta,Energy.leg,qAxis] <;> ring
lemma heel : L (k+p x i) = if i then (L k+2*a*x+x^2) else (L k-2*c*x+x^2):= by cases i <;> simp (disch := decide) [qAxis,side,Momentum.sq,unitV,spike, Pi.single_apply] <;> ring
set_option maxHeartbeats 500000 in
lemma vCard_pay : 4*matP k (beat (e i) k (p x i)) (beat (e j) (-k) (p y j))= vCard k x y i j:= by
    rw [second,second]; simp only [map_add,map_smul, map_neg,LinearMap.smul_apply,LinearMap.add_apply, projector, closed_r, smul_zero, add_zero, neg_zero]; rw [matrix_q]; unfold innerP
    cases i <;> cases j <;> simp (disch := decide) [vCard,arm0,qAxis,unitV,spike,Pi.single_apply] <;> ring
lemma folded_v : VX h (e i) (e j) (x • T i) (y • T j) k= vCard k x y i j * ( H (L (k + p x i)) * H (L (-k + p y j)) ):= by rw [speak_v,← vCard_pay]; ring
set_option maxHeartbeats 500000 in
lemma rCard_pay : 8* L k *matP (k+p x i) (beat (e i) (-(k+p x i)) (p x i)) (beat (e j) (k+p x i) (p y j))=rCard k x y i j:= by
    have ht (u v t:P)(z w:ℝ) : matP t (u+z • (-t)) (v+w • t) = matP t u v:= by simp only [map_add,map_smul,map_neg,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.neg_apply,projector,closed_r,smul_zero,add_zero,neg_zero]
    rw [second,second,ht,matrix_q,heel]; unfold innerP
    cases i <;> cases j <;> simp (disch := decide) [rCard,arm0,qAxis,side,unitV,spike,Pi.single_apply] <;> ring
lemma folded_r : RX h (e i) (e j) (x • T i) (y • T j) k= rCard k x y i j * (h (L (k+p x i)) * H (L (k+(p x i + p y j)))):= by rw [speak_r,← rCard_pay]; ring
set_option maxHeartbeats 500000 in
lemma uCard_pay : (∑ u:Axis,∑ v:Axis, 4* L k*flow k u*flow (k+(p x i+p y j)) v*h0 u v (e i) (e j))=uCard k x y i j:= by
   cases i <;> cases j <;> simp (disch := decide) [uCard, side, port, unitV, spike, flow, h0,sideV, Slice.delta, Energy.leg,qAxis] <;> ring
lemma folded_u : UX h (e i) (e j) (x • T i) (y • T j) k= uCard k x y i j * H (L (k+(p x i+p y j))):= by
    unfold UX; rw [← uCard_pay]; simp_rw [out_paint, Finset.sum_mul]; refine Finset.sum_congr rfl fun u _=>Finset.sum_congr rfl fun v _=>?_ ; ring
end
end YM.SignedWilsonExpansion.Overlap
