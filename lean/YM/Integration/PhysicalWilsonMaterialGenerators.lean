import YM.Integration.PhysicalWilsonJointMaterial

/-! Every marked and quiet polynomial of the finite connected program inherits the
actual absolute-link material, the complete entering sources and the chart Jacobian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonMaterialGenerators
open Filter Finset Lattice Wilson RG Precision Tree Exterior Marker Multi
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants Next.Rank
open PhysicalWilsonJointMaterial
open scoped Classical BigOperators Topology ContDiff

variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} (W:Bulk.Colors Γ G f)
variable (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices)
local notation "E" => Bulk.Joint S F (G:=G)

theorem generators {I:Type} [Fintype I] [DecidableEq I]
    (y:E) (L:(I→ℝ)→ₗ[ℝ] E) (r:ℕ):
    Assembly.generator y L W.power (Bulk.markFn S F W) (Bulk.geometric K F tag W) r=
      Assembly.generator y L W.power (mark S F W) (measured S F W p P O) r:=by
  have charged (i:Hot Γ) (n:ℕ):
      Assembly.kernelJet y L (Bulk.markFn S F W i) n=Assembly.kernelJet y L (mark S F W i) n:=by
    unfold Assembly.kernelJet
    rw [((marked S F W i).iteratedFDeriv ℝ n).eq_of_nhds]
  have quiet (n:ℕ):
      Assembly.naked y L (Bulk.geometric K F tag W) n=Assembly.naked y L (measured S F W p P O) n:=by
    unfold Assembly.naked
    simp_rw [((geometric (F:=F) W K tag).iteratedFDeriv ℝ _).eq_of_nhds]
  funext s
  simp only [Assembly.generator,charged,quiet]

def board (B:fieldDir G c 1) (r:ℕ):Grade Γ r:=
  Cloud.prescription (K.covariance F tag) (K.symm F tag) 0
    (Assembly.generator (Bulk.stage K F B) (Bulk.hinge F) W.power
      (mark S F W) (measured S F W p P O) r)

theorem original (B:fieldDir G c 1) (r:ℕ):Bulk.Fk K F tag W B r=board W K F tag B r:=by
  unfold Bulk.Fk Assembly.prescription board
  rw [generators W K F tag]

theorem normalized (B:fieldDir G c 1) (r:ℕ):
    Order.logMarked (Bulk.Fk K F tag W B r)=Order.logMarked (board W K F tag B r):=
  congrArg Order.logMarked (original W K F tag B r)

end YM.Integration.PhysicalWilsonMaterialGenerators
end
