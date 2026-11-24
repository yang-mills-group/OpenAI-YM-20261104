import YangMills.CorrelationHierarchy
import YangMills.WilsonProof.HierarchyChannels
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.YangMills.WilsonLattice

/-! Euclidean correlations of the Wilson fields, their phase decomposition, the OPE and the centered trace test. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory TopologicalSpace
open scoped Topology BigOperators InnerProductSpace Distributions Classical NNReal ContDiff


attribute [instance] Hierarchy.fieldAdd Hierarchy.fieldSpace Hierarchy.fieldFinite
  Hierarchy.finiteChannels Hierarchy.characterMetric Hierarchy.characterSets
  Hierarchy.characterBorel Hierarchy.characterCompact

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)





/-- Four-dimensional Euclidean spacetime used by the OPE estimates. -/
abbrev OPEPoint := EuclideanSpace ℝ (Fin 4)

/-- Ordered configurations of `n` insertion points. -/
abbrev OPEPoints (n : ℕ) := PiLp 2 (fun _ : Fin n => OPEPoint)

/-- Complex time coordinates of an analytically continued correlation. -/
abbrev OPEComplexTimes (n : ℕ) := Fin n → ℂ

/-- Spatial coordinates of an analytically continued correlation. -/
abbrev OPESpacePoints (n : ℕ) := Fin n → YangMills.Space













end Hierarchy
end YangMills
