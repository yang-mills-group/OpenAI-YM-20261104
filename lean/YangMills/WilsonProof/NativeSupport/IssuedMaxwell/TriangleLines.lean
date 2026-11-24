import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleAxes
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleLines
open YM YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position

def potential (i:Axis)(x:E4):ℝ:= -YangMills.Maxwell.partialD i YangMills.Maxwell.Coordinates.green x
def single (p:Fin 3)(b:Axis)(x:E4):ℝ:=∑ a:Axis,Cubic.chiral false p a b * potential a x
def contraction (s t:Bool)(p r:Fin 3)(a b:Axis):ℝ:=∑ i:Axis,Cubic.chiral s p a i * Cubic.chiral t r b i
def double (p r:Fin 3)(x:E4):ℝ:=∑ a:Axis,∑ b:Axis,contraction true false p r a b * YangMills.Maxwell.partialD a (potential b) x

theorem line (a:Axis):potential a=Season.coast a:=rfl
theorem one (p:Fin 3)(a:Axis)(x:E4):single p a x=Rose.m p a x:=by
  unfold single Rose.m Season.line
  simp only [TriangleAxes.original,qNorm,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,line]
  apply Finset.sum_congr rfl
  intro b hb
  ring
theorem contracted (s t:Bool)(p r:Fin 3)(a b:Axis):
    contraction s t p r a b=Rose.f^2*Season.hatch s t p r a b:=by
  unfold contraction Season.hatch Relief.folds
  simp only [TriangleAxes.original,qNorm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem original (p r:Fin 3)(x:E4):double p r x=Rose.clamp p r x:=by
  unfold double Rose.clamp Season.surfT
  simp only [contracted,line,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change _ * _ * (YM.Maxwell.grad a (Season.coast b) x)= _*(_*(YM.Maxwell.grad a (Season.coast b) x))
  ring
end IssuedMaxwell.TriangleLines
end
