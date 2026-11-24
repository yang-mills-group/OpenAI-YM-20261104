import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleScaling
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleBulk
open YM YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position
open IssuedMaxwell.TriangleLines IssuedMaxwell.TriangleVertex

def bulk (c:Shade.Cut)(i j k:Fin 3)(u v b:E4):ℝ :=
  ∑ r:Fin 3,∑ a:Axis,∑ e:Axis,Cubic.chiral false r a e *
    (∑ l:Axis,∑ m:Axis,contraction false true r i l m *
      derivative c l u v b (potential m) (single j a) (single k e))

def vertex (c:Shade.Cut)(i j k:Fin 3)(u v b:E4):ℝ:=
  (∑ a:Axis,∑ e:Axis,Cubic.chiral true i a e*single j a (u-v)*single k e (u-b))-2*bulk c i j k u v b

theorem localTerm (c:Shade.Cut)(l m a e:Axis)(j k:Fin 3)(u v b:E4):
    derivative c l u v b (potential m) (single j a) (single k e)=Rose.f^2*
      Season.moving c l u v b (Season.coast m) (Season.line false j a) (Season.line false k e):=by
  have scale (p:Fin 3)(v:Axis):single p v=(fun x=>Rose.f*(Season.line false p v x)):=funext (one p v)
  have hf:Rose.f≠0:=by unfold Rose.f;positivity
  rw [scale,scale,TriangleLines.line,TriangleScaling.original _ hf,TriangleVertex.original]

theorem original (c:Shade.Cut)(i j k:Fin 3)(u v b:E4):vertex c i j k u v b=Rose.aT c i j k u v b:=by
  have paid:bulk c i j k u v b=Rose.wave c i j k u v b:=by
    unfold bulk Rose.wave Season.sweepT Season.parts
    simp only [TriangleAxes.original,qNorm,contracted,localTerm,Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _=>Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun e _=>?_
    refine Finset.sum_congr rfl fun l _=>Finset.sum_congr rfl fun m _=>?_
    ring
  simp only [vertex,Rose.aT,TriangleAxes.original,one,paid]
end IssuedMaxwell.TriangleBulk
end
