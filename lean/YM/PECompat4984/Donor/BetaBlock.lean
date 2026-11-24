import YM.Push.BETA_TRANSPORT.Block
import YM.Push.BETA_TRANSPORT.Noise

/-! Exact seed helper restoration; retained definitions are imported unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Pressure Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

lemma density_pos (h : S.patch.Branches S.kernel G) (β : ℝ) (U : Config G f) (V) : 0 < S.density β U V :=
  (inv_pos.mpr (noiseCost_pos S _)).trans_le (density_bounds S h le_rfl U V).1

end YM.Push.BetaTransport
end
