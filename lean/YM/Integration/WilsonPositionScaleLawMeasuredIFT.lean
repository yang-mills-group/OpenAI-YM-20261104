import YM.XSpace.Passage
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredIFT
open Function Filter Set
open scoped Topology ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def residual (D:E→E) (z:E×E) : E := D z.2-z.1

theorem regular (D:E→E)(s:ContDiff ℝ ω D):ContDiff ℝ ω (residual D) :=
  (s.comp contDiff_snd).sub contDiff_fst

theorem jacobian (D:E→E)(s:ContDiff ℝ ω D)(b:E):
    fderiv ℝ (residual D) (D b,b) ∘L ContinuousLinearMap.inr ℝ E E = fderiv ℝ D b := by
  let f:=ContinuousLinearMap.fst ℝ E E
  let g:=ContinuousLinearMap.snd ℝ E E
  have h : HasFDerivAt (residual D) ((fderiv ℝ D b).comp g-f) (D b,b) :=
    ((s.differentiable (by simp) b).hasFDerivAt.comp (D b,b) g.hasFDerivAt).sub f.hasFDerivAt
  rw [h.fderiv]
  ext v
  simp [f,g]

variable [CompleteSpace E] (D:E→E)(s:ContDiff ℝ ω D)(b:E)(live:(fderiv ℝ D b).IsInvertible)
def elected : E→E := ((regular D s).contDiffAt (x:=(D b,b))).implicitFunction (by simp)
  (by rw [jacobian D s b];exact live)

theorem base : elected D s b live (D b)=b := ContDiffAt.implicitFunction_apply_self ..
theorem smooth : ContDiffAt ℝ ω (elected D s b live) (D b) := ContDiffAt.contDiffAt_implicitFunction ..
theorem near : ∀ᶠw in 𝓝 (D b), D (elected D s b live w)=w := by
  have e : ∀ᶠw in 𝓝 (D b),residual D (w,elected D s b live w)=residual D (D b,b) :=
    ContDiffAt.eventually_apply_implicitFunction ..
  filter_upwards [e] with w hw
  simpa [residual,sub_eq_zero] using hw

theorem recovers : ∀ᶠx in 𝓝 b, elected D s b live (D x)=x := by
  have law : ∀ᶠp in 𝓝 (D b,b),residual D p=residual D (D b,b) ↔ elected D s b live p.1=p.2 :=
    ContDiffAt.eventually_apply_eq_iff_implicitFunction ..
  have path : Tendsto (fun x:E=>(D x,x)) (𝓝 b) (𝓝 (D b,b)) := s.continuous.continuousAt.prodMk_nhds tendsto_id
  filter_upwards [path.eventually law] with x hx
  exact hx.mp (by simp [residual])
end YM.Integration.WilsonPositionScaleLawMeasuredIFT
