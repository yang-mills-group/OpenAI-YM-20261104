import YM.Integration.WilsonMatrixCoordinates
import YM.Integration.WilsonLinkMatrixAmplitude

/-! Exact transfer of faithful linear matrix observations from the centered Wilson law. -/
noncomputable section
namespace YM.Integration.WilsonLinearKernelFactor
open YM RG RG02 RG02.Asym Lattice Wilson Filter MeasureTheory Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series.Tested
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
open WilsonKernelCoupling WilsonMatrixCoordinates
variable {G : Gauge} {c f : Side} (S : StepData c f)

def mean (b : ℝ) (i : Index G) : ℝ :=
  ∫ g : G.El, link S b 1 g * coordinate G i (G.mat g) ∂G.probHaar

theorem split (b : ℝ) (q : G.El) (B : G.Mat →L[ℝ] ℝ) :
    (∫ v : G.El, link S b q v * B (G.mat v) ∂G.probHaar) =
      ∑ i, weight G B i q * mean S b i := by
  have ht := (measurePreserving_mul_right G.probHaar q⁻¹).integral_comp
    (Homeomorph.mulRight q⁻¹).measurableEmbedding
    (fun g : G.El => link S b 1 g * B (G.mat (g*q)))
  have hs : (∫ v : G.El, link S b q v * B (G.mat v) ∂G.probHaar) =
      ∫ g : G.El, link S b 1 g * B (G.mat (g*q)) ∂G.probHaar := by
    simpa only [link,inv_one,mul_one,mul_assoc,inv_mul_cancel] using ht
  have hl : Continuous (link S b (1:G.El)) := by
    unfold link StepData.penaltyWeight
    fun_prop
  rw [hs]
  simp_rw [decompose G B q,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [mean,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with g
    ring
  · intro i _
    exact (hl.mul (continuous_const.mul
      ((coordinate G i).continuous.comp G.continuous_mat))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

end YM.Integration.WilsonLinearKernelFactor
