import YM.Integration.WilsonMatrixTicketFuelCommonBin
import YM.Integration.WilsonMatrixTicketLanesChargeSource

/-! Consume the near-null estimate on a prescribed extracted family, table,
base and presentation, using the derivative map of the given physical final. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketFuelPrice
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Roost
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations
open OPE OPE.Owl MergeProof MergeProof.Accent Next.Extract Dash Extraction
open scoped BigOperators Classical Topology
variable {G:Gauge}

theorem cash {g:G.Simple} {s:Sheet G} {p:MapPrices} {H:Votive.Sponsor G}
    {K:Votive.Seasons H} {a:Axis} {X:Stroke.PriceBook (chart_ok G) K} {t:ℕ→ℕ}
    {U:Rolls (ThroughLaunch.raise s t)} {P:Spells.Pad G} {D:Desk (ThroughLaunch.raise s t) X a g}
    {S:Alloy (ThroughLaunch.bountyV s p t) U}
    (C:FuelV g s p H K a X t U P D S) {ε:ℝ} (hold:C.Opacity ε) :
    FromStrongBin C.Holds := by
  intro f A L B Z tr T E physical projected base bin services
  have submerged := C.fresco T f base projected hold bin
  exact OPE.Lake.Concourse.tender (C.ΔHope T f physical submerged) physical.phase.transport.injection services

theorem lanes (R:Run G) {g:G.Simple} {a:Axis} {ε:ℝ} (hε:0<ε) (hcap:ε≤1/50)
    (funded:Eligible g a ε R.kit):FromStrongBin R.family := by
  obtain ⟨L,hL⟩:=issued R hε hcap funded
  exact L.family_eq ▸ cash L.physical hL

end YM.Integration.WilsonMatrixTicketFuelPrice
