import YM.OPE.Interpolate.Leap
import YM.OPE.Polar.Damping
import YM.OPE.Polar.Look
/-! Combine enough good normals near coordinate basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter Metric
open scoped Topology BigOperators Classical
variable {I: Type}[Fintype I][DecidableEq I] (i:I)(a:Axis)
def ray (i:I)(p:Ortho) : I→E4:= Pi.single i (forwards p).val
variable {v:I→E4}{p:Ortho}
lemma ray_norm (p:Ortho) : ‖ray i p‖=1:= by unfold ray; rw [Pi.norm_single,(forwards p).property]
lemma ray_error {ε:ℝ}(h:‖(forwards p).val-basis a‖ < ε): ‖ray i p - kindle i a‖ ≤ ε:= by
    unfold ray kindle; rw [← Pi.single_sub,Pi.norm_single]; exact h.le
set_option quotPrecheck false
local notation "N"=> Fintype.card (I×Axis)
def knobSize (I : Type)[Fintype I] := 1/(2*((Fintype.card (I × Axis) :ℝ)+1))
lemma knob_pos : 0<knobSize I:= by unfold knobSize; positivity
local notation "T"=> knobSize I
lemma knobs_cost (x : (I→E4) → ℂ)(K : ℝ) (h0:‖x v‖≤Real.exp K) (h:DifferentiableAt ℝ x v) (hx:∀ (i:I)(a: Axis),∃ p: Ortho, ‖(forwards p).val - basis a‖< knobSize I ∧ Radiates x v (ray i p) (Real.exp K)) : Watches x v K (2*((Fintype.card (I×Axis) :ℝ)+1)):=by
    refine ⟨h0,fun f A ha hA=> ?_,h⟩; choose p hP hF using hx
    have hu(i:I×Axis):‖f (kindle i.fst i.snd)‖ ≤ ‖f‖*T+A:=by
       let z:= ray i.1 (p i.1 i.2); let w:= kindle i.1 i.2; have hp: ‖w-z‖ ≤ T:= by rw [norm_sub_rev]; exact ray_error i.1 _ (hP ..)
       have hx := norm_sub_norm_le (f w) (f z); rw [← map_sub] at hx; linarith only [hA z (ray_norm ..|>.le) (hF ..), hx,f.le_opNorm (w-z),mul_le_mul_of_nonneg_left hp (norm_nonneg f)]
    have he:‖f‖ ≤ N * (‖f‖*T+A) := (operator f).trans (le_trans (Finset.sum_le_sum (fun i _=> hu i)) (by simp; linarith));
    have h : (N : ℝ)*knobSize I ≤ 1/2:=by unfold knobSize; have h : 0<(2:ℝ)*(N+1):=(by positivity); field_simp; linarith
    nlinarith only [mul_le_mul_of_nonneg_left h (norm_nonneg f),ha,he]
end YM.OPE.Polar
