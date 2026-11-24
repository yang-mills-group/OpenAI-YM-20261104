import YM.OPE.Compatible.Cant.Coal
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
lemma forkP (p:E→L[ℝ] E)(z:ℝ)(m i j:ℕ)(x:KernP p z m): ((portC p z m ^(i+j)) x)=(portC p z m^i) ((portC p z m ^j) x):=by rw[pow_add,byway]
end YM.OPE.Hark
