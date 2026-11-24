import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy
import YangMills.WilsonProof.NativeSupport.HierarchySpec

set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory TopologicalSpace
open scoped Topology BigOperators InnerProductSpace Distributions Classical NNReal ContDiff
namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

structure Properties (B : Maxwell.Reference g) (order : ℕ → ℕ) : Prop where
  wilson : C.Converges order (fun v => T.correlation none (T.project ∘ v))
  reconstruction : T.Reconstructed
  ope : T.OperatorProductExpansion
  ward : Nonempty T.StressWardLaws
  nonfree : T.TraceTest
  maxwell : Nonempty (T.MaxwellScaling B)
end Hierarchy

/-- One Wilson family per gauge group, followed by a refinement for every requested
volume sequence. All conclusions concern a single hierarchy on that refinement. -/
def JointExistence : Prop := ∀ g : GaugeGroup, g.IsSimple → ∃ (B : Maxwell.Reference g) (C : WilsonFamily g),
  WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p → ∃ q : ℕ → ℕ, StrictMono q ∧
    ∃ T : Hierarchy C, T.Properties B (p ∘ q)

end YangMills
