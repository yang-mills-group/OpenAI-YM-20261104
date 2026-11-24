import YM.Comparison.RG02.Cumulants.Cloud
/-! Integration of a complete, jointly evaluated finite conditional source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianPaidTable
open Marker Multi Next.Rank Next.SectorChange Comparison.RG02 Comparison.RG02.Cumulants MeasureTheory
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
variable (R:Census V)(Q:Matrix I I ℝ)(h:(I→ℝ)→Hot R→ℂ)
def presented (s:R.Mode)(z:I→ℝ):ℂ:=(lit R (h z)).pass.part s
def table:Poly R:=Poly.inject (fun s=>∫ z,presented R h s z ∂(Gaussian.cloud Q))
theorem original (sym:Q.IsSymm)(pos:Q.PosSemidef)(f:Hot R→Normal.poly I)
    (hit:∀z s,Cloud.paint z (f s)=h z s):
    Cloud.prescription Q sym 0 f=table R Q h ∧
      ∀s,Integrable (presented R h s) (Gaussian.cloud Q):=by
  have row(z:I→ℝ)(s:R.Mode):
      (lit R (fun a=>Cloud.paint z (f a))).pass.part s=presented R h s z:=by
    unfold presented
    rw [funext (hit z)]
  have atMode(s:R.Mode):=Cloud.gaussian Q sym pos 0 f s
  simp only [zero_add,Cloud.shift_zero] at atMode
  constructor
  · ext1 s
    exact (atMode s).2.symm.trans (integral_congr_ae (Filter.Eventually.of_forall (fun z=>row z s)))
  · intro s
    exact (atMode s).1.congr (Filter.Eventually.of_forall (fun z=>row z s))
end YM.Integration.WilsonOriginalGaussianPaidTable
