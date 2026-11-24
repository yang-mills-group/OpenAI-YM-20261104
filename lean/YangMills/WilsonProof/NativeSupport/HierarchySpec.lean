import YangMills.ScalingLimits
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields

import YangMills.WilsonProof.NativeSupport.YangMills.WilsonLattice

import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Centered trace insertions and scaling coordinates for a continuum hierarchy. -/

set_option autoImplicit false

noncomputable section

namespace YangMills

open Function Filter Set MeasureTheory TopologicalSpace

open scoped Topology BigOperators InnerProductSpace Distributions Classical NNReal ContDiff

namespace Hierarchy

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

theorem TraceTest.centeredInsertion (h : T.TraceTest) (s : Option T.Character) {n : ℕ}
    (x : Points (n+1)) (hx : x ∈ WilsonFamily.separated (n+1)) (v : Fin n → T.Tag) :
    T.correlation s (Fin.cons ⟨4, T.centeredTrace⟩ v) x =
      (∑ μ, T.correlation s (Fin.cons ⟨4, T.stress μ μ⟩ v) x) -
        T.correlation (some T.selected) (fun _ : Fin 1 => ⟨4, T.stressTrace⟩) 0 *
        T.correlation s v (WithLp.toLp 2 fun i : Fin n => x i.succ) := by
  obtain ⟨L, hL⟩ := h.linearInsertion s x hx v
  rw [← hL, centeredTrace, map_sub, map_smul, show L T.stressTrace = ∑ μ, L (T.stress μ μ) from map_sum ..]
  simp only [hL, smul_eq_mul, h.unitInsertion s x hx v]


end Hierarchy

end YangMills
