import YM.Integration.WilsonIndependentConditionalGaussianMoment

/-! Compare the actual normalized Gaussian expectation and full held Wick series, including rank zero. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalHeldGaussian
open WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open scoped Classical BigOperators
variable {I J E:Type} [Fintype I] [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A:Law E)(d:I→Module.Dual ℝ E)(μ:Measure E)
    [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]

def held (b:J→ℝ):I⊕J→ℝ:=Sum.elim 0 b
def noise (d:I→Module.Dual ℝ E):I⊕J→Module.Dual ℝ E:=Sum.elim d 0

omit [Fintype I] [Fintype J] [MeasurableSpace E] [BorelSpace E] in
theorem pad : Gaussian.bond A (noise (J:=J) d)=fillSlots J (Gaussian.bond A d):=by
  funext u v
  cases u <;> cases v <;> simp [noise,fillSlots,Gaussian.bond,Law.wick,Matrix.fromBlocks]

omit [Fintype I] [Fintype J] in
private theorem hear (b:J→ℝ)(p:POL (I⊕J)):
    emphasis (held b) p=emphasis b (projectZeroPoly I J p):=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [emphasis,projectZeroPoly]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i h=>
    rw [map_mul,map_mul,map_mul,h]
    cases i <;> simp [emphasis,held,projectZeroPoly]

theorem original (b:J→ℝ)(p:Ink (I⊕J)):
    burn A (noise d) μ p (held b)=PowerSeries.map (emphasis b).toRingHom (Wick J (Gaussian.bond A d) p):=by
  ext1 e
  rw [PowerSeries.coeff_map,burn,PowerSeries.coeff_mk]
  change Gaussian.averaged A (noise d) μ (held b) (coeff e p)=emphasis b (coeff e (Wick J (Gaussian.bond A d) p))
  rw [WilsonIndependentConditionalGaussianMoment.original,pad,hear]
  change _=emphasis b (coeff e (PowerSeries.map _ (blur _ p)))
  rw [PowerSeries.coeff_map,overlay_apply]
  rfl

end YM.Integration.WilsonIndependentConditionalHeldGaussian
