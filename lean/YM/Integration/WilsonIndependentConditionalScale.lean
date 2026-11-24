import YM.Integration.WilsonIndependentConditionalVacuum

/-! Exact change of the conditional Gaussian reference on the genuine
free coordinates. The zero-source denominator uses the same held field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentConditionalScale
open MeasureTheory PertExtension PertExtension.GaussianScore WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Convention
open Lattice RG FreeResolvent
open scoped Classical Topology BigOperators MatrixOrder
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

def bias (L:Law E)(a:ℝ)(x:E):ℝ:=Real.exp ((1-(a⁻¹)^2)*L.P x x/2)

omit [FiniteDimensional ℝ E] in
theorem density (L:Law E)(a:ℝ)(x:E):
    bias L a x*L.kern x=L.kern (a⁻¹ • x) := by
  unfold bias Law.kern
  rw [←Real.exp_add]
  apply congrArg Real.exp
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

theorem original [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
    (L:Law E)(a:ℝ)(ha:0<a)(F:E→ℝ):
    L.average μ (fun x=>bias L a x*F (a⁻¹ • x))=
      (a^Module.finrank ℝ E)*L.average μ F := by
  have same:(fun x=>bias L a x*F (a⁻¹ • x))*L.kern=(fun x=>(F*L.kern) (a⁻¹ • x)):=by
    funext x;simp only [Pi.mul_apply]
    rw [mul_comm (bias ..),mul_assoc,density]
  rw [Law.average,same,Measure.integral_comp_smul_of_nonneg μ (F*L.kern) a⁻¹ (hR:=inv_nonneg.mpr ha.le)]
  simp only [smul_eq_mul,inv_pow,inv_inv,Law.average,mul_div_assoc]

theorem conditional [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
    (L:Law E)(a:ℝ)(ha:0<a)(vac marked:E→ℝ):
    L.average μ (fun x=>bias L a x*(vac*marked) (a⁻¹ • x)) /
       L.average μ (fun x=>bias L a x*vac (a⁻¹ • x)) =
      L.average μ (vac*marked)/L.average μ vac := by
  rw [original μ L a ha,original μ L a ha]
  exact mul_div_mul_left _ _ (pow_ne_zero _ ha.ne')

variable {G:Gauge}{c f:Side}(S:StepData c f)(T:Tree.Forest S.ratio)(H:FaceRow)

theorem planted (h:(treeMatrix G S T H).PosDef)(a:ℝ)(ha:0<a)(b:TreeVars G c)
    (vac mark:Lawn (Active G T)→TreeVars G c→ℝ):
    (law h).average volume (fun x=>bias (law h) a x *
      ((fun x=>vac x (a⁻¹ • b))*(fun x=>mark x (a⁻¹ • b))) (a⁻¹ • x)) /
      (law h).average volume (fun x=>bias (law h) a x*vac (a⁻¹ • x) (a⁻¹ • b))=
    (law h).average volume ((fun x=>vac x (a⁻¹ • b))*(fun x=>mark x (a⁻¹ • b))) /
      (law h).average volume (fun x=>vac x (a⁻¹ • b)):=
  conditional volume (law h) a ha _ _

end YM.Integration.WilsonIndependentConditionalScale
