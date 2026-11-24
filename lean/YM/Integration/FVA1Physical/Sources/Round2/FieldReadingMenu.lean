import YM.Integration.FVA1Physical.Round2.FieldSharpSeason
import YM.Integration.FVA1Physical.Sources.Round2.FieldMasks

/-! Mixed physical stencil readings at every non-bare step on one construction.
The cutoffs precede the torus and independent placements. The forest used
for every field comparison is also the one producing the realized outgoing
vacuum polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint
open Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

abbrev ReadingInputs (n:ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) × Bool
def readingGate (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) (p s L h : ℕ) (part : Bool) : ℝ :=
  if ok:P.Branches K G then (eventually_atTop.mp (inherited_field_season J V cle (chart G) (chart_ok G)
    hG H H' P K ok p s L part (Nat.cast_nonneg H.order) (margin_pos h) (sub_pos.mp (margin_fits p h)))).choose else 0
def readingMenu (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ i:ReadingInputs H.order, |readingGate J V cle hG H H' P K i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2|

/-- A threshold purchased before the period, physical placements and retained background. -/
abbrev readingInvoice (V:Voice G) (cle:Clear G V) (hG:G.Simple) : Goal G :=
  selectedThreshold (G:=G) (readingMenu J V cle hG)

end YM.Integration.FVA1Physical.Round2.Curvature
