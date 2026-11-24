import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NegativePupil
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.TriangleAxes
open YM YM.XSpace YM.XSpace.Chiral YangMills.MSbar.Position

private def hit {α:Type} [DecidableEq α] (a b:α):ℤ:= if a=b then 1 else 0
private def shown {α:Type} [DecidableEq α] (a b c d:α):ℝ:=
  if a=c ∧ b=d then 1 else 0
private theorem paired {α:Type} [DecidableEq α] (a b c d:α):
    shown a b c d = (hit c a:ℝ)*(hit d b:ℝ):=by
  by_cases h:a=c <;> by_cases k:b=d <;> simp_all [shown,hit,eq_comm]
theorem orientation (i j k:Fin 3):Cubic.orientation i j k = liftedSign i j k:=by
  change shown j k (i+1) (j+1)-shown i k (j+1) (i+1) =
    ((hit (i+1) j*hit (j+1) k-hit (j+1) i*hit (i+1) k:ℤ):ℝ)
  simp only [paired,Int.cast_sub,Int.cast_mul]
theorem original (s:Bool)(i:Fin 3)(a b:Fin 4):
    Cubic.chiral s i a b=qNorm s i a b:=by
  change (Real.sqrt 2)⁻¹ * (shown 0 i.succ a b - shown 0 i.succ b a +
    (if s then 1 else -1) * (shown (i+1).succ (i+2).succ a b-shown (i+1).succ (i+2).succ b a))=
    (Real.sqrt 2)⁻¹ * ((hit a 0*hit b i.succ-hit a i.succ*hit b 0 +
    (if s then 1 else -1)*(hit a (i+1).succ*hit b (i+2).succ-hit a (i+2).succ*hit b (i+1).succ):ℤ):ℝ)
  cases s <;> simp only [paired,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_neg,Int.cast_one,
    Bool.false_eq_true,if_false,if_true] <;> ring
end IssuedMaxwell.TriangleAxes
end
