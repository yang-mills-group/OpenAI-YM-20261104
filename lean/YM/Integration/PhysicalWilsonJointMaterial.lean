import YM.Integration.PhysicalWilsonAbsoluteHaarPrimitive
import YM.Comparison.RG02.Bulk.Fk

/-! The finite saddle uses the absolute-gauge material and the actual relative Haar density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonJointMaterial
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Tree Exterior
open WilsonCoeffUV FreeResolvent Comparison.RG02 Marker Multi
open scoped Classical BigOperators Topology ContDiff

variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)
variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} (W:Bulk.Colors Γ G f)
variable (p:Clip) (P:PathData G) (O:ChartRatio G)
local notation "E" => Bulk.Joint S F (G:=G)

def coordinates (z:E):TreeVars G f:=flatten (Work.F03.axisLog F z.2)
theorem physical :
    (fun z:E=>mantle (coordinates S F z))=ᶠ[𝓝 0] fun z=>Work.F03.live F z.2:=by
  have h:=(continuous_snd.tendsto (0:E)).eventually (Work.F03.inclusion_works (G:=G) F)
  filter_upwards [h] with z hz
  simpa only [coordinates,placed] using hz

def haarDifference (z:E):ℝ:=unhaar O (coordinates S F z)-Real.log (∏i:F.Free,O.J (z.2.2 i))
def action (z:E):ℝ:=
  let X:=coordinates S F z
  let U:=mantle X
  mainTerm p P U+jointPen G S (Sum.elim X (flatten z.2.1))+
    z.1^2*(loop P U-unhaar O X)+W.vac z.1 U
def measured (z:E):ℝ:=action S F W p P O z+z.1^2*haarDifference S F O z
def mark (i:Hot Γ) (z:E):ℂ:=W.mark i z.1 (mantle (coordinates S F z))
omit [Fintype V] in
theorem marked (i:Hot Γ):Bulk.markFn S F W i=ᶠ[𝓝 0] mark S F W i:=by
  filter_upwards [physical S F] with z h
  exact congrArg (W.mark i z.1) h.symm

private theorem penalty (X:TreeVars G f) (B:fieldDir G c 1):
    jointPen G S (Sum.elim X (flatten B))=noiseTaylor S (represent B) (mantle X) (tac S):=by
  change noiseTaylor S (mantle (flatten B)) (mantle X) (tac S)=_
  rw [placed]

variable {S F p P O} (K:Bulk.Kernel S p P O)
omit [Fintype V] in
theorem geometric (t:S.Choices):
    Bulk.geometric K F t W=ᶠ[𝓝 0] measured S F W p P O:=by
  apply (Bulk.geometric_choice K F t W (tac S)).trans
  filter_upwards [physical S F] with z h
  change mainTerm p P (Work.F03.live F z.2)+
    noiseTaylor S (represent z.2.1) (Work.F03.live F z.2) (tac S)+
    (z.1^2*(loop P (Work.F03.live F z.2)-Real.log (∏i:F.Free,O.J (z.2.2 i)))+
      W.vac z.1 (Work.F03.live F z.2))=_
  rw [←h]
  simp only [measured,action,haarDifference,penalty]
  ring

end YM.Integration.PhysicalWilsonJointMaterial
end
