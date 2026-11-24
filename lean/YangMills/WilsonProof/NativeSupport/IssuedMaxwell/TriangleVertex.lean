import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleLines
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleVertex
open YM YM.XSpace MeasureTheory

def derivative (c:Shade.Cut)(a:Axis)(u v b:E4)(f g h:E4→ℝ):ℝ:=
  let outside (y:E4)(k:E4→ℝ)(w:E4):=(1-c (w-y))*k (w-y)
  let exterior (w:E4):=outside u (YangMills.Maxwell.partialD a f) w*outside v g w*outside b h w
  let primary (w:E4):=
    let y:=w+u-v
    let z:=w+u-b
    f w*(-(YangMills.Maxwell.partialD a (fun s=>c s) w)*g y*h z-
      c w*(YangMills.Maxwell.partialD a g y*h z+g y*YangMills.Maxwell.partialD a h z))
  let secondary (y z:E4)(k l:E4→ℝ)(w:E4):=k w*c w*YangMills.Maxwell.partialD a f (w+y-u)*l (w+y-z)
  (∫ w,exterior w)+(∫ w,primary w)+(∫ w,secondary v b g h w)+(∫ w,secondary b v h g w)

theorem original (c:Shade.Cut)(a:Axis)(u v b:E4)(f g h:E4→ℝ):
    derivative c a u v b f g h=Season.moving c a u v b f g h:=by
  have pd (j:Axis)(k:E4→ℝ)(x:E4):YangMills.Maxwell.partialD j k x=YM.Maxwell.grad j k x:=rfl
  unfold derivative Season.moving
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · apply congrArg₂ (·+·)
      · rfl
      · apply integral_congr_ae
        filter_upwards with w
        simp only [Season.idle,Season.source,pd]
        ring
    · apply integral_congr_ae
      filter_upwards with w
      simp only [Season.sample,Season.green,pd]
      ring
  · apply integral_congr_ae
    filter_upwards with w
    simp only [Season.sample,Season.green,pd]
    ring
end IssuedMaxwell.TriangleVertex
end
