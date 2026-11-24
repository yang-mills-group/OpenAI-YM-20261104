import YM.Integration.WilsonKernelCoupling
import YM.Integration.WilsonLinkAmplitudeExpansion

/-! Smooth functions of a faithful Wilson matrix at any predicted group element. -/
noncomputable section
namespace YM.Integration.WilsonLinkMatrixAmplitude
open YM RG RG02 RG02.Asym Lattice Wilson Filter MeasureTheory Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series.Tested
open WilsonKernelCoupling WilsonLinkAmplitudeChart WilsonLinkAmplitudeExpansion
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

def atPrediction (q : G.El) (F : G.El → ℝ) (x : Friction.W G) : ℝ := F (x () * q)

theorem integral (q : G.El) (F : G.El → ℝ) (t : ℝ) :
    mean S (atPrediction q F) t = Complex.ofReal
      (∫ v, link S (t^2)⁻¹ q v * F v ∂G.probHaar) := by
  let L (v : G.El) := S.penaltyWeight (t^2)⁻¹ v * F (v*q)
  have hpi : (∫ x, weighted S (atPrediction q F) t x ∂Friction.roll G) = ∫ v, L v ∂G.probHaar := by
    have he : weighted S (atPrediction q F) t = fun x : Friction.W G => ∏ i : Unit, L (x i) := by
      funext x
      simp only [Finset.univ_unique,Finset.prod_singleton]
      rfl
    rw [he]
    change (∫ x : Friction.W G, (∏ i : Unit, L (x i)) ∂Measure.pi (fun _ => G.probHaar)) = _
    rw [integral_fintype_prod_eq_prod (fun _ : Unit => L)]
    simp
  have h := (measurePreserving_mul_right G.probHaar q⁻¹).integral_comp
    ((Homeomorph.mulRight q⁻¹).measurableEmbedding) L
  have he : (fun v => link S (t^2)⁻¹ q v * F v) =
      (fun v => L (v*q⁻¹) / S.penaltyZ (t^2)⁻¹ G) := by
    funext v
    simp only [link,L,inv_mul_cancel_right]
    ring
  unfold WilsonLinkAmplitudeExpansion.mean
  rw [hpi,he,integral_div,h,Complex.ofReal_div]

theorem matrix (P : ChartRatio G) (hP : LocalRatio P) (q : G.El)
    (F : G.Mat → ℝ) (hF : ContDiff ℝ ∞ F) :
    Near (fun t => Complex.ofReal (∫ v, link S (t^2)⁻¹ q v * F (G.mat v) ∂G.probHaar))
      (normalizedSeries S P (atPrediction q (fun v => F (G.mat v)))) := by
  let w := atPrediction q (fun v => F (G.mat v))
  have hw : Continuous w :=
    hF.continuous.comp (G.continuous_mat.comp ((continuous_apply ()).mul continuous_const))
  have he : ContDiff ℝ ∞ (fun u : Friction.E G => G.mat (G.lieExp (u ()))) :=
    (G.exp_jet.comp (contDiff_apply _ G.Color ())).of_le le_top
  have hj : ContDiffAt ℝ ∞ (fun u : Friction.E G => w (expLinks G Unit u)) 0 := by
    change ContDiffAt ℝ ∞ (fun u : Friction.E G => F (G.mat (G.lieExp (u ()) * q))) 0
    simp only [G.mat_mul]
    exact hF.contDiffAt.comp _ (he.contDiffAt.mul contDiffAt_const)
  apply Near.same (normalized S P hP w hw hj)
  exact Filter.Eventually.of_forall (fun t => integral S q (fun v => F (G.mat v)) t)

end YM.Integration.WilsonLinkMatrixAmplitude
