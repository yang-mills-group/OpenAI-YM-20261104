import YangMills.Geometry
import YM.Gauge.Lie

/-! The matrix group used in the perturbative graph formula. -/

set_option autoImplicit false
noncomputable section
namespace YangMills

def GaugeGroup.core (g : GaugeGroup) : YM.Gauge := ⟨g.n, g.image, g.imageClosed⟩

theorem GaugeGroup.coreSimple {g : GaugeGroup} (hg : g.IsSimple) : g.core.Simple := by
  have h : g.core.lie = g.lieAlgebra := by
    ext m
    exact (g.generates m).symm
  rw [YM.Gauge.Simple, h]
  exact hg

end YangMills
