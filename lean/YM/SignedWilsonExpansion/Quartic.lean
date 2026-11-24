import YM.SignedWilsonExpansion.VoiceV
namespace YM.SignedWilsonExpansion.AxisChoice
/-! `UX`: the contact loop. Derivative of weight retained on external both. -/
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
variable (k p q r:P)(u v:Axis)(i j:Test)(x y:ℝ)
local notation "Z" => weight h
local notation "Λ" => Momentum.sq
local notation "γ" => Slice.delta
local notation "κ" => value

def beta (k:P)(i j:Test) : P →ₗ[ℝ] ℝ:= {
    toFun B:= -2*Slice.delta (AxisChoice.direction i) (AxisChoice.direction j) * ( flow k⬩ B ) + value k i*B (AxisChoice.direction j) + value k j*B (AxisChoice.direction i),
    map_add' B C:= by simp [innerP,mul_add, Finset.sum_add_distrib]; abel
    map_smul' t B:= by simp_rw [ ← tool,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply ]; ring }
lemma works (k p:P): ∑ u:Axis,∑ v:Axis, flow k u* flow p v* h0 u v (e i) (e j) = beta k i j (flow p) := by
    simp [ beta,innerP,h0,sideV, Slice.delta, show Finset.univ (α:=Axis)={0,1,2,3} from rfl ]; cases i <;> cases j <;> simp [ flow,value,direction,Energy.leg ]; all_goals ring
lemma fixed (w:P)(v:P): beta k i j (flow (slide w y j))= beta k i j (flow w)+ y * beta k i j (unitV (e j)):= by
    have he: flow (slide w y j)=flow w+y • unitV (e j):= by
        funext q; rw [ value_shift ]; by_cases hp:q=e j <;> simp [ *, Slice.delta,unitV,spike,Pi.single_apply, Ne.symm ]
    rw [he,map_add,map_smul]; rfl
lemma planes (h:ℝ→ℝ): UX h (e i) (e j) p q k= 4*k.sq*weight h (k+(p+q)).sq * beta k i j (flow (k+(p+q))) := by
    unfold UX; rw [ ← works ]; simp_rw [ out_paint, Finset.mul_sum ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=> by ring))
lemma head_pull : (∑ j:Test, beta k i j (unitV (e j)))=κ k i:= by
    cases i<;> (simp [ beta, Slice.delta, innerP, direction, unitV, spike, flow, value, Energy.leg,ite_mul,Pi.single_apply,mul_ite]; ring)
lemma axis_pull : (∑ j:Test,κ (slide k x i) j* beta k i j ( flow (slide k x i) ))=x*(κ k i^2-disk k):= by
    cases i <;> (simp [ beta, Slice.delta, innerP, direction, unitV, spike, flow, value,slide,tangent,disk, Energy.leg, Pi.single_apply,show Finset.univ (α:=Axis)={0,1,2,3} from rfl ]; ring)

local notation "U" => fun i j p q=> UX h i j p q k
include he
lemma first_U : ∑ j:Test,dY (daily U i j) x = 4*k.sq*(2*deriv Z (Λ (slide k x i))*x*(κ k i^2-disk k)+folio h k i x*κ k i):= by
    let B:= slide k x i; let H:=4*k.sq
    have P' j:dY (daily U i j) x= H*(2* κ B j*deriv Z (Λ B)* beta k i j (flow B)+folio h k i x*beta k i j (unitV (e j))):= by
       rw [row]; beta_reduce; simp_rw [planes, ← add_assoc]; change deriv (fun y:ℝ=>H* folio h B j y * beta k i j (flow (slide B y j))) 0=_; simp_rw [fixed (v:=B) ]
       obtain he' := ((( start he B j 0 ).const_mul H).fun_mul ( ( (hasDerivAt_id' (0:ℝ)).mul_const ( beta k i j ( unitV (e j) ) ) ).const_add (beta k i j (flow B)) )).deriv; rw [he']; unfold folio; rw [slide0]; unfold B H; ring
    simp_rw [P']; unfold H; rw [← Finset.mul_sum, Finset.sum_add_distrib,← Finset.mul_sum,head_pull]; simp_rw [mul_right_comm (2:ℝ) (κ B _) _, mul_assoc (2*deriv Z _), ← Finset.mul_sum]; unfold B; rw [axis_pull,← mul_assoc (2*deriv Z _) ]
local notation "B" => disk k
lemma xfirst_U :
    HasDerivAt (fun x:ℝ=>∑ j:Test,dY (daily U i j) x) ( 8*k.sq*deriv Z k.sq *(2*value k i^2-B)) 0:= by
    let f x:=deriv Z (Λ (slide k x i))
    have hp : ContDiff ℝ ∞ f:= by unfold f slide Momentum.sq; have H:= ( show ContDiff ℝ (∞+1) Z from (by simp [ buoy he ] ) ).deriv'; fun_prop
    simp_rw [ first_U he ]; obtain he' := hp.differentiable (by simp) (0:ℝ)
    convert! (( ( ( (he'.hasDerivAt.const_mul (2:ℝ)).fun_mul ( hasDerivAt_id' (0:ℝ) ) ).mul_const ( κ k i^2-B ) ).fun_add ( (start he k i 0).mul_const ( κ k i ) ) ).const_mul (4*k.sq)) using 1; unfold f; rw [slide0]; ring
lemma Uprice : bill U=0:= by
    rw [ bill ]; simp_rw [ ← through U (warmU k he), ( xfirst_U he k _ ).deriv,← Finset.mul_sum ]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum, fuel ]; simp
end
end YM.SignedWilsonExpansion.AxisChoice
