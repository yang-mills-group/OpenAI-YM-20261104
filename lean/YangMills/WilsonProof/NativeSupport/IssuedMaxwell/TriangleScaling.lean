import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleDerivative
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleVertex
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleScaling
open YM YM.XSpace MeasureTheory
open IssuedMaxwell.TriangleVertex

theorem original (q:ℝ)(hq:q≠0)(c:Shade.Cut)(a:Axis)(u v b:E4)(f g h:E4→ℝ):
    derivative c a u v b f (fun x=>q*g x) (fun x=>q*h x)=
      q^2*derivative c a u v b f g h:=by
  have grad (k:E4→ℝ)(x:E4):YangMills.Maxwell.partialD a (fun x=>q*k x) x=
    q*YangMills.Maxwell.partialD a k x:=TriangleDerivative.original q hq a k x
  unfold derivative
  simp only [mul_add,← integral_const_mul,grad]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply congrArg₂ (·+·)
      · apply integral_congr_ae
        filter_upwards with w
        ring
      · apply integral_congr_ae
        filter_upwards with w
        ring
    · apply integral_congr_ae
      filter_upwards with w
      ring
  · apply integral_congr_ae
    filter_upwards with w
    ring
end IssuedMaxwell.TriangleScaling
end
