import YangMills.WilsonProof.NativeSupport.IssuedBank.WilsonSlope
import YangMills.WilsonProof.NativeSupport.HierarchyBridge

set_option autoImplicit false

namespace IssuedRuns.PhysicalRunning

open Filter YangMills YangMills.Wilson
open scoped Topology
noncomputable section

variable {g : GaugeGroup} (C : YM.Family g.core) (h : C.Makes)
  (hg : g.IsSimple) (B : Maxwell.Reference g)

include h hg B

theorem original : 0 < wilsonOneLoop B ∧ ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ p,
      |(wilsonFamily C).beta N p / Real.log (((wilsonFamily C).mesh N)⁻¹) - 2 * wilsonOneLoop B| < ε := by
  have transfer : 2 * YM.Pert.Asymptotics.b0 g.core = 2 * wilsonOneLoop B := by
    rw [YM.Pert.Asymptotics.b0_normalizes, IssuedBank.WilsonSlope.original B hg]
  refine ⟨IssuedBank.OriginalOneLoop.original B hg, ?_⟩
  intro ε hε
  rw [← transfer]
  filter_upwards [YM.Pert.Asymptotics.zeroUp_bound C h hε] with N hN
  exact fun p => hN N p le_rfl

theorem regular : WilsonRegularity (wilsonFamily C) := by
  obtain ⟨positive, proceeds⟩ := original C h hg B
  refine ⟨⟨2 * wilsonOneLoop B, mul_pos (by norm_num) positive, proceeds⟩,
    fun N p v x => C.continuousO N p v.1 v.2 x,
    fun N p v x => C.invariant h N p v.1 v.2 x, ?_⟩
  intro v
  exact ⟨(C.localSection v.1).stencil, fun N p x => C.localO N p v.1 v.2 x⟩


end
end IssuedRuns.PhysicalRunning
