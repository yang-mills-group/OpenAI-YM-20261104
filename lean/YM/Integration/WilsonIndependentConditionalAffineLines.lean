import YM.Integration.WilsonIndependentConditionalDiagramResponse

/-! A change of a finite forest's measured coordinates before Wick contraction.
Both the retained value and every marked covariance move under the same matrix. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalAffineLines
open WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries Matrix
open scoped Classical BigOperators
variable {I J E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℝ E]

def directions (R:Matrix J I ℝ)(d:I→Module.Dual ℝ E)(j:J):Module.Dual ℝ E:=
   ∑ i,R j i • d i

theorem probe (R:Matrix J I ℝ)(d:I→Module.Dual ℝ E)(b:I→ℝ)(p:Jet J):
    Gaussian.probe d b (cord R p)=Gaussian.probe (directions R d) (R*ᵥb) p:=by
  funext y
  unfold Gaussian.probe
  rw [cord_apply]
  apply congrArg (fun q=>MvPolynomial.eval q p)
  funext j
  simp [Matrix.mulVec,dotProduct,directions,mul_add,Finset.sum_add_distrib]

variable [FiniteDimensional ℝ E] (A:Law E)

theorem lines (R:Matrix J I ℝ)(d:I→Module.Dual ℝ E):
    Gaussian.bond A (directions R d)= R*(show Matrix I I ℝ from Gaussian.bond A d)*R.transpose:=by
  funext x y
  simp only [Gaussian.bond,Law.wick,directions,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum,Matrix.mul_apply,Matrix.transpose_apply,
    Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.HasTemperateGrowth]

omit [FiniteDimensional ℝ E] [μ.HasTemperateGrowth] [BorelSpace E] in
theorem hearing (R:Matrix J I ℝ)(d:I→Module.Dual ℝ E)(b:I→ℝ)(P:Ink J):
    burn A d μ (loom R P) b=burn A (directions R d) μ P (R*ᵥb):=by
  ext e
  simp only [burn,loom,coeff_mk,coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  apply congrArg (A.average μ)
  exact probe R d b _

end YM.Integration.WilsonIndependentConditionalAffineLines
