import YM.Integration.FVA1Physical.Wilson.FluctuationSharp
import YM.Integration.FVA1Physical.Sources.Round2.FieldReadingMenu
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

theorem fluctuation_hull (G:Gauge) (simple:G.Simple) (L:Side) {D:ℝ} (hD:0 ≤ D) :
    ∀ᶠ x:ℝ in atTop,∀ g:ℝ, Mosaic.lensT (tip G L x) g →
      D*Heath.Cottage.room (tip G L x) ≤ g*Mosaic.hull x := by
  let gy:=Work.E09.betaF_growth G L
  filter_upwards [gy.eventually (hotel_scalar 0 D (by norm_num) hD), Alto.drift_scale simple L,
    gy.eventually_gt_atTop 0] with x radius scale pos
  intro g band
  have H:=radius g band
  simp only [zero_mul,zero_add] at H
  have gp:=((half_pos (inv_pos.mpr (Real.sqrt_pos.mpr pos))).trans_le band.1).le
  apply H.trans (mul_le_mul_of_nonneg_left _ gp)
  have hi : Mosaic.hatW (tip G L x) ≤ 1.1*Mosaic.hatW x := scale.2.2
  have low : 1 ≤ Mosaic.hatW x := scale.1
  change Mosaic.hatW (tip G L x)/32 ≤ 4*(Mosaic.hatW x/32)
  linarith only [hi,low]

def fluctuationGate (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) (p s L h : ℕ) (part : Bool) : ℝ :=
  if ok:P.Branches K G then max (eventually_atTop.mp (fluctuation_hull G hG P.L (Nat.cast_nonneg H.order))).choose
    (eventually_atTop.mp (fluctuation_field_season J V cle (chart G) (chart_ok G)
    hG H H' P K ok p s L part (Nat.cast_nonneg H.order) (margin_pos h) (sub_pos.mp (margin_fits p h)))).choose else 0
def fluctuationMenu (V : Voice G) (cle : Clear G V) (hG : G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ i:ReadingInputs H.order, |fluctuationGate J V cle hG H H' P K i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2|

/-- A threshold purchased before the period, physical placements and retained background. -/
abbrev fluctuationInvoice (V:Voice G) (cle:Clear G V) (hG:G.Simple) : Goal G :=
  selectedThreshold (G:=G) (fluctuationMenu J V cle hG)

end YM.Integration.FVA1Physical.Round2.Curvature
