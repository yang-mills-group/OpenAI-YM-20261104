import YM.Pert.Triangle.Admissible
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-! A smooth, compact, rotation-averaged profile on the b,U,U slots with a nonzero signed continuum Taylor response. Merely exploiting a pointwise nonzero free triple moment without response control would not suffice for a coupling coordinate. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
variable {G:Gauge} (h:G.Simple)
local notation "P" => Points 3
local notation "I" => Fin 3

def bellM : ContDiffBump (0:ℝ) := ⟨(1/2:ℝ),1,by norm_num,by norm_num⟩
def candid (R:ℝ) (p:P) : ℝ := bellM (‖p 0‖^2-R^2) * (bellM (‖p 1‖^2-12^2)) * (bellM (‖p 2‖^2))
lemma candidPositive (p:P) (R:ℝ) (hn:p∈support (candid R)) : 0<candid R p := lt_of_le_of_ne (mul_nonneg (mul_nonneg bellM.nonneg bellM.nonneg) bellM.nonneg) (mem_support.mp hn).symm
lemma candidSmooth (R:ℝ) : ContDiff ℝ ∞ (candid R) := by
  have hr (i:Fin 3) (a:ℝ): ContDiff ℝ ∞ (fun p : P=>bellM (‖p i‖^2 - a)) := bellM.contDiff.comp (((contDiff_norm_sq ℝ).comp (displacementDiff i)).sub contDiff_const)
  convert! ((hr 0 (R^2) |>.mul (hr 1 (12^2)) |>.mul (hr 2 0))) using 1
  ext p; unfold candid; dsimp; rw [sub_zero]
lemma markM (u:ℝ) (hu : bellM u≠0) : |u|<1 := mem_ball_zero_iff.mp (bellM.support_eq ▸ (show u∈Function.support bellM from hu))

def pallet (R:ℝ) (p:P) : Prop :=
    R-1 ≤ ‖p 0‖ ∧ ‖p 0‖ ≤ R+1 ∧ 10≤‖p 1‖ ∧ ‖p 1‖ ≤18 ∧ ‖p 2‖≤2
lemma on_pallet {R :ℝ} (hR : 128≤R) (p:P) (h : p∈support (candid R)) : pallet R p := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals
    have ha := markM _ (left_ne_zero_of_mul (left_ne_zero_of_mul (show candid R p≠0 from h): bellM _ * _ ≠ 0))
    have hb := markM _ (right_ne_zero_of_mul (left_ne_zero_of_mul (show candid R p≠0 from h): _ * bellM (‖p 1‖^2-12^2) ≠ 0))
    have hc := markM _ (right_ne_zero_of_mul (show candid R p≠0 from h) : bellM (‖p 2‖^2)≠0)
    dsimp [candid] at *
    nlinarith [abs_lt.mp ha,abs_lt.mp hb,abs_lt.mp hc,norm_nonneg (p 0),norm_nonneg (p 1),norm_nonneg (p 2)]
lemma closed_pallet {R:ℝ} (hR : 128≤R) : tsupport (candid R) ⊆ {p|pallet R p} := by
  refine closure_minimal (fun p hp=> on_pallet hR p hp) ?_
  have H i (z:ℝ) : IsClosed {x:P | z≤‖x i‖} ∧ IsClosed {x:P | ‖x i‖ ≤ z} := ⟨isClosed_le continuous_const ((displacementDiff i).continuous.norm),isClosed_le ((displacementDiff i).continuous.norm) continuous_const⟩
  exact (H 0 (R-1)).1.inter ((H 0 (R+1)).2.inter ((H 1 _).1.inter ((H 1 _).2.inter (H 2 _).2)))
lemma supportedCandid {R:ℝ} (hr:128≤ R) : HasCompactSupport (candid R) := by
  let S := closedBall (0:E4) (R+1)
  have hc := (isCompact_univ_pi (fun i:Fin 3=> show IsCompact S from isCompact_closedBall ..)).image (f:=@WithLp.toLp 2 (I→E4)) (PiLp.continuous_toLp ..)
  refine hc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun p hp=>?_ ) hc.isClosed)
  have he:=on_pallet hr p hp
  refine ⟨fun i=>p i, fun i hi=> mem_closedBall_iff_norm.mpr ?_, rfl⟩
  rw [sub_zero]; fin_cases i
  · exact he.2.1
  · exact he.2.2.2.1.trans (by linarith)
  · exact he.2.2.2.2.trans (by linarith)

def farEnough (p:P):Prop := ∀ i j:I, i≠j → 4 < ‖p i-p j‖
lemma pallet_far {R:ℝ} (hr:128≤ R) {p:P} (hp:pallet R p) : farEnough p := by
  have hs := suitable_separations p ⟨hp.2.2.1,hp.2.2.2.1, hp.2.2.2.2,by linarith [hp.1]⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  · exact hs.1
  · exact hs.2.1
  · exact (hs.1.trans_le (norm_sub_rev ..).symm.le)
  · exact hs.2.2
  · exact hs.2.1.trans_le (norm_sub_rev ..).symm.le
  · exact hs.2.2.trans_le (norm_sub_rev ..).symm.le
lemma candidFar {R:ℝ} (hr:128≤R) {p:P}(hp:p∈tsupport (candid R)) : farEnough p := pallet_far hr (closed_pallet hr hp)
-- not changing domain
def voter (R:ℝ) (hR : 128≤R) : RealTest 3 := ⟨candid R,(candidSmooth R |>.of_le (by decide)),supportedCandid hR,fun p hp=> by
  have hw i j := candidFar hR hp i j
  change p∈conf 3
  exact fun i j e=> Classical.byContradiction fun hi=>by
     have he:=hw i j hi
     rw [show p i=p j from e,sub_self,norm_zero] at he
     norm_num at he⟩
end YM.Pert.Triangle
