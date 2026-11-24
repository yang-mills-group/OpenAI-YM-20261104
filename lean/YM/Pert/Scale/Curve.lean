import YM.Pert.Position.Frame
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
Smearing of the actual dilation response at positive relative length. Arguments stay in the separated open set whenever the profile is nonzero. No evaluation of a derivative of a product of two coincident fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 180000
noncomputable section
namespace YM.Pert.Scale
open Filter Function Set MeasureTheory Analysis Table Topology Classical
open scoped ContDiff
variable {n : ℕ}

def shiftMean (t : Test n) (f : Points n → ℂ) (s : ℝ) := ∫ x : Points n, t x * f (s • x)
def shiftLead (t : Test n) (f : Points n → ℂ) (s : ℝ) := ∫ x : Points n, t x * fderiv ℝ f (s • x) x

lemma slides {s : ℝ} (hs : 0<s) {x : Points n} (hx : x∈conf n) : s • x ∈conf n :=
   Work.A04.scale_conf s hs hx
lemma slide_diff {s : ℝ} (hs : 0<s) {x : Points n} (f : Points n → ℂ) (hf : ContDiffOn ℝ ∞ f (conf n)) (hx : x∈conf n) :
    ContDiffAt ℝ ∞ f (s • x) :=
  (hf (s • x) (slides hs hx)).contDiffAt ((conf_open _).mem_nhds (slides hs hx))

lemma slides_term {s : ℝ} (hs : 0<s) {x : Points n} (f : Points n → ℂ)
    (hf : ContDiffOn ℝ ∞ f (conf n)) (hx : x∈conf n) : ContinuousAt (fderiv ℝ f) (s • x) :=
   (slide_diff hs f hf hx).continuousAt_fderiv (by decide)

theorem shift_deriv (t : Test n) {f : Points n → ℂ} (hf : ContDiffOn ℝ ∞ f (conf n)) {s : ℝ} (hs : 0<s) :
     HasDerivAt (shiftMean t f) (shiftLead t f s) s := by
  haveI : IsBoundedSMul ℝ (Points n) := .of_norm_smul_le NormedSpace.norm_smul_le
  haveI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
  let J := Icc (s/2) (2*s)
  have hJ : J ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  have hj {u : ℝ} (hu : u∈J) : 0<u := (half_pos hs).trans_le hu.1
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod t.hasCompactSupport).exists_bound_of_continuousOn
    (α:=ℝ × Points n) (f:=fun w => fderiv ℝ f (w.1 • w.2)) (s:=J ×ˢ tsupport t)
       (fun x hx => ((slides_term (hj hx.1) f hf (t.tsupport_subset hx.2)).comp
         (f:=fun w : ℝ × Points n => w.1 • w.2) (x:=x) (by fun_prop)).continuousWithinAt)
  let P := fun (u:ℝ) (x:Points n) => t x * f (u • x)
  let D := fun (u:ℝ) (x:Points n) => t x * fderiv ℝ f (u • x) x
  have hm {u : ℝ} (hu : 0<u) : Integrable (P u) := t.smearing (hf.continuousOn.comp (f:=fun x : Points n=>u • x) (by fun_prop) (fun _=> slides hu))
  let bound := fun x : Points n=> |C| * ‖t x‖ * ‖x‖
  have hl : Integrable bound := by
    apply (show Continuous bound from by dsimp[bound]; fun_prop (disch:=exact t.continuous)).integrable_of_hasCompactSupport
    exact t.hasCompactSupport.norm.mul_left.mul_right
  have hD : Integrable (D s) := by
    apply Test.smearing t (K:=fun x : Points n => fderiv ℝ f (s•x) x)
    intro x hx
    have ha := (slides_term hs f hf hx).comp (f:=fun x : Points n => s • x) (x:=x) (by fun_prop)
    exact (ha.clm_apply (continuousAt_id (x:=x))).continuousWithinAt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ (μ:=volume) (F:=P) (F':=D) (bound:=bound)
    (Filter.Eventually.mono hJ (fun u hu=> (hm (hj hu)).aestronglyMeasurable)) (hm hs) hD.aestronglyMeasurable
    (Eventually.of_forall fun x u hu=> ?_) hl (Eventually.of_forall fun x u hu=>?_)).2
  · by_cases hx : x ∈ tsupport t
    · have hxC : ‖fderiv ℝ f (u•x)‖ ≤ C := hC (u,x) ⟨hu,hx⟩
      have hn : ‖fderiv ℝ f (u • x) x‖ ≤ |C| * ‖x‖ := by
        exact ((fderiv ℝ f (u•x)).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hxC.trans (le_abs_self C)) (norm_nonneg _))
      calc
        ‖D u x‖ ≤ ‖t x‖ * (|C| * ‖x‖) := (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
        _ = bound x := by dsimp[bound]; ring
    rw [show D u x=0 from by simp[D,image_eq_zero_of_notMem_tsupport hx], norm_zero]
    dsimp[bound]; positivity
  by_cases hx : x ∈ tsupport t
  · have hc := ((slide_diff (hj hu) f hf (t.tsupport_subset hx)).differentiableAt (by simp)).hasFDerivAt
    have hde : HasDerivAt (fun a:ℝ => a•x) x u := by simpa only [one_smul] using! (hasDerivAt_id' u).smul_const x
    exact (hc.comp_hasDerivAt u hde).const_mul (t x)
  simp only [P,D,image_eq_zero_of_notMem_tsupport hx,zero_mul]; exact hasDerivAt_const u 0

end YM.Pert.Scale
