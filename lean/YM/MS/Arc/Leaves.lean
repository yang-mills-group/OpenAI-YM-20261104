import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace YM.MS.Arc
open MeasureTheory
open scoped Interval

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev Tree (E F:Type):= ℝ×E→ F
def d (f:Tree E F): Tree E F:= fun p=> fderiv ℝ f p (1,0)
def chop (f:Tree E F): Tree E F:= fun p=> ∫ t:ℝ in 0..1, d (d f) (t*p.1,p.2)
end YM.MS.Arc
