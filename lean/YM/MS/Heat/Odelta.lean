import Mathlib.Analysis.Calculus.Deriv.Add
import YM.MS.Heat.Health

set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Plane
variable {A P I : Type} {t : ℝ}

def Zip (F:BF A P) (F':Row A P ℂ) (t:ℝ): Prop:= ∀ w, HasDerivAt (fun x:ℝ=>F x w) (F' w) t
namespace Zip
lemma sum (J:Finset I){F:I→ BF A P}{F':I→ Row A P ℂ}(h:∀ i∈J,Zip (F i) (F' i) t): Zip (fun k=> ∑ i∈ J,F i k) (∑ i∈J,F' i) t:= by intro l; simp_rw [Finset.sum_apply]; exact HasDerivAt.fun_sum (fun i hi=>h i hi l)
end Zip
end YM.MS.Heat
