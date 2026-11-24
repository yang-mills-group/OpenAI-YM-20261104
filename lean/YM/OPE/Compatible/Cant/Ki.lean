import YM.OPE.Compatible.Cant.Foam
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma imagery (p:E→L[ℝ] E)(m:ℕ)(b:ℝ)(x:KernP p b m): ((portC p b m)^1) x=(portC p b m) x:=by rw[pow_one]
end YM.OPE.Hark
