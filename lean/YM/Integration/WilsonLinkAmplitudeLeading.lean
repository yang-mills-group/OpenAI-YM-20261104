import YM.Integration.WilsonLinkAmplitudeExpansion

/-! The leading coefficient of the measured smooth Wilson link expectation. -/
noncomputable section
namespace YM.Integration.WilsonLinkAmplitudeLeading
open YM RG RG02 Lattice Wilson Filter MeasureTheory Metric Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open PertExtension.Series.Radial RG02.Asym RG02.Therm WilsonLinkAmplitudeChart WilsonLinkAmplitudeExpansion
open scoped ContDiff Topology BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

theorem at_zero : expLinks G Unit (0 : Friction.E G) = fun _ => (1 : G.El) := by
  funext u
  apply G.mat_injective
  change G.mat (G.lieExp 0) = G.mat 1
  rw [G.mat_lieExp_zero,G.mat_one]

theorem raw_zero (P : ChartRatio G) (hP : LocalRatio P) (w : Friction.W G → ℝ) :
    coeff 0 (rawSeries S P w) =
      Complex.ofReal ((Therm.leading (Friction.Γ S G) (Friction.rate G) 0 * P.scale) * w (fun _ => 1)) := by
  rw [rawSeries,coeff_C_mul,Therm.shuttle,coeff_mk,
    Wick.fixed (Friction.Γ S G) (Friction.rate G) _ (Complex.ofReal (P.scale * w (fun _ => 1)))]
  · push_cast
    ring
  funext x
  rw [Therm.pulsed,coeff_zero_eq_constantCoeff_apply,map_mul]
  simp only [← coeff_zero_eq_constantCoeff_apply,Asym.ex,PowerSeries.coeff_mk]
  simp [ribbon_coeff,Radial.jet_zero,amplitude,Friction.jac,Chart.jacobian,Chart.fee,hP.anchored,hP.scale.le,at_zero]

theorem leading (P : ChartRatio G) (hP : LocalRatio P) (w : Friction.W G → ℝ) :
    coeff 0 (normalizedSeries S P w) = Complex.ofReal (w (fun _ => 1)) := by
  have hz : Complex.ofReal (Therm.leading (Friction.Γ S G) (Friction.rate G) 0 * P.scale) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (Therm.leading_pos ..) hP.scale).ne'
  rw [normalizedSeries,coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_inv]
  simp only [← coeff_zero_eq_constantCoeff_apply,raw_zero S P hP w,Friction.paid_base S P hP]
  rw [Complex.ofReal_mul,mul_right_comm,mul_inv_cancel₀ hz,one_mul]

end YM.Integration.WilsonLinkAmplitudeLeading
