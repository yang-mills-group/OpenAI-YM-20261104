import YM.SignedWilsonExpansion.MarkArithmetic
namespace YM.SignedWilsonExpansion.AxisChoice
/-! Taking the derivatives under actual projection. Part R and V.
Crucially derivative of weight cancels with the curl projection and the
null directions of the line. -/
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
variable {h:ℝ→ℝ} (he: ContDiff ℝ ∞ h)
variable (k p q r:P)(u v:Axis)(i j:Test)(x:ℝ)
local notation "Z" => weight h
def folio (h:ℝ→ℝ)(p:P)(i:Test)(x:ℝ):= weight h (slide p x i).sq
local notation "Υ" => folio h
local notation "Λ" => Momentum.sq
local notation "Y" => (ℝ×ℝ)
@[simp] lemma slide0 : slide k 0 i=k := by simp only [slide, zero_smul,add_zero]

include he
lemma buoy : ContDiff ℝ ∞ Z:= by unfold weight; fun_prop
lemma start (x:ℝ) : HasDerivAt (Υ k i) ( (2*value k i+2*x) * deriv Z (Λ (slide k x i)) ) x:= by
    have hp : HasDerivAt (fun x=> Λ (slide k x i)) (2*value k i+2*x) x:= by
        simp_rw [strut]; convert! ((( (hasDerivAt_id' x).const_mul ( 2*value k i )).const_add k.sq ).fun_add ( ( hasDerivAt_id' x ).pow 2 )) using 1; norm_num
    convert! ( (( buoy he ).differentiable (by simp) (Λ (slide k x i)) ).hasDerivAt.comp x hp ) using 1; rw [mul_comm]

abbrev invoice (h:ℝ→ℝ)(k:P)(i:Test): P:= weight h k.sq • ((2*value k i) • T i) + ( 2*value k i* deriv (weight h) k.sq ) • ((-2*k (AxisChoice.direction i)) • flow k )
lemma speaker_grad : HasDerivAt ( speaker h k i ) ( invoice h k i ) 0:= by
    have he' : HasDerivAt (drum k i) ( (2*value k i) • T i ) 0:= by
        let A:= hasDerivAt_id' (0:ℝ); have fe : HasDerivAt (fun z:ℝ=>2*z*( value k i + z )) (2*value k i) 0:= by convert! (( A.const_mul (2:ℝ)).fun_mul ( A.const_add (value k i))) using 1; ring
        exact ( fe.smul_const (T i)).const_add ((-2*k (e i)) • flow k)
    convert! (( start he k i 0 ).smul he') using 1; unfold folio drum invoice; simp only [slide0, add_zero,mul_zero,zero_mul,zero_smul ]
omit he
lemma receipt (h:ℝ→ℝ)(k:P) : ∑ i: Test, invoice h k i=(2*weight h k.sq) • extent k := by
    funext u
    have hp(i:Test): invoice h k i u= 2* weight h k.sq *(value k i *T i u) - ( (4*deriv ( weight h ) k.sq*flow k u)*( value k i*k (e i) )):= by unfold invoice; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul ]; ring
    simp only [ Finset.sum_apply, hp, Finset.sum_sub_distrib ]; rw [← Finset.mul_sum, grow, ← Finset.mul_sum, total,mul_zero,sub_zero ]; rfl
lemma has_lin (B : P→ₗ[ℝ] ℝ)(t:ℝ){f:ℝ→P}{A:P} (hp:HasDerivAt f A t) : HasDerivAt (fun s=> B (f s)) (B A) t:= (( LinearMap.toContinuousLinearMap B ).hasFDerivAt.comp_hasDerivAt t hp)

local notation "C" => fun i j p q=> VX h i j p q k
local notation "R" => fun i j p q=> RX h i j p q k
include he
lemma sell : ∑ j:Test,dY (daily C i j) x= -8* Z (Λ k) * matP k (speaker h k i x) (extent k):= by
    let B:= matP k (speaker h k i x)
    have hp(j:Test): dY (daily C i j) x=4*B (invoice h (-k) j):= by
        rw [row i j C]; beta_reduce; simp_rw [arrival_v]; exact (( has_lin B 0 (speaker_grad he (-k) j) ).const_mul (4:ℝ)).deriv
    simp_rw [hp,← Finset.mul_sum,← map_sum, receipt, MS.Landau.sq_neg,disk_neg,map_smul,map_neg,smul_eq_mul ]; unfold B; ring
lemma buying (i:Test) :
    HasDerivAt (fun x:ℝ=> ∑ j:Test,dY (daily C i j) x)
       (-8*Z (Λ k)*matP k ( invoice h k i ) (extent k)) 0:= by
   simp_rw [ sell he ]; exact (has_lin (( matP k ).flip (extent k)) 0 ( speaker_grad he k i )).const_mul _
lemma Vprice : bill C= -16* (Z (Λ k))^2 * disk k*(Λ k-disk k):= by
    rw [ bill ]; simp_rw [ ← through C (warmV k he), (buying he k _).deriv,← LinearMap.flip_apply (matP k),← Finset.mul_sum, ← map_sum, receipt, map_smul, LinearMap.flip_apply, streak ]; rw [smul_eq_mul]; ring

lemma sellR : ∑ j:Test,dY (daily R i j) x= -32* Λ k *value k i*x*(value k i+x)*(Λ k-disk k)
    * h (Λ (slide k x i))* Z (Λ (slide k x i)):= by
    let p:= slide k x i; let B:=matP p (drum (-p) i x); let q:=8*k.sq*h p.sq
    have hp(j:Test): dY (daily R i j) x=q*B (invoice h p j):= by
       rw [row i j R]; beta_reduce; simp_rw [arrival_r]; exact ( has_lin B 0 ( speaker_grad he p j ) |>.const_mul q ).deriv
    simp_rw [hp]; rw [← Finset.mul_sum,← map_sum, receipt, map_smul, smul_eq_mul]; unfold q B p; rw [ left_extent ]; ring
lemma sellRx : HasDerivAt (fun x=> ∑ j:Test,dY (daily R i j) x) (-32*(Z (Λ k))^2 * (value k i)^2 * ( Λ k-disk k )) 0:= by
    let L(x:ℝ):=-32* Λ k *value k i*(value k i+x)*(Λ k-disk k) *h (Λ (slide k x i))* Υ k i x
    have hx: Differentiable ℝ L:= by unfold L folio weight slide Momentum.sq; have hm:= he.differentiable (by simp); fun_prop
    have h(x:ℝ): (∑ j:Test,dY (daily R i j) x)=x*L x:= by rw [sellR he]; unfold L folio; ring
    rw [funext h]; convert! (( hasDerivAt_id' (0:ℝ)).fun_mul (( hx 0 ).hasDerivAt)) using 1; unfold L folio weight; rw [slide0]; ring
lemma Rprice : bill R= -32*(Z (Λ k))^2 *disk k*(Λ k-disk k):= by
    rw [ bill ]; simp_rw [ ← through R (warmR k he), (sellRx he k _).deriv, ← Finset.sum_mul, ← Finset.mul_sum, fuel k ]

end
end YM.SignedWilsonExpansion.AxisChoice
