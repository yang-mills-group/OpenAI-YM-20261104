import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
/-!
 # Genuine existential producer on Gauge.Simple. Keep options for further costs.
   issue Use.Origins with full every period. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roost
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple) {K : KernelChoices} (hK : ∀ p:Patch,p.Branches K G)
    (v : ThroughLaunch.Orders) (h : ThroughLaunch.Draft v)

-- Existential Ribbon package to carry exact K/W.P pledge identity (constructed).
structure Arms {G : Gauge} {M : Metals G} (D:Rolls M.p) where
  exchange : ℕ→ℕ→Exchange
  book : ℕ→ℕ→Postage
  scout : Scouts (F:=book)
  scoutL : ℕ→ℝ
  post : ResetPrices
  walls : Return.Wages
  rider : ℕ→ℕ→Cafe
  target : Targets M.p M.K
  expense : Expenses target
  duration : ℕ→ℝ
  shape : Register D expense walls duration
  house : Baton G
  v : Return.Wages
  t : Return.Wages
  span : ℕ→ℕ→ℕ
  booth : ℕ→ℕ→Booth
  prices : Programs M.p
  menu : ℕ→ℕ→JointLoad.Clockwork.Menu
  recordP : ℕ→ℕ→JointLoad.Heir.Record
  auxiliary : ℕ→ℕ→JointLoad.Folio.Aux

-- Pack after Rolls, before calls to *big delays*.
def Factor.books {G :Gauge} {M: Metals G} {D:Rolls M.p} {A:Alloy M D} (P:Factor A):Arms (M:=M) D:=
    ⟨P.exchange,P.book,P.scout,P.scoutL,P.post,P.walls,P.rider,P.target,P.expense,P.duration,P.shape,P.house,P.v,P.t,P.span,P.booth,P.prices,P.menu,P.recordP,P.auxiliary⟩
end YM.PhysicalNext.Repeat.Roost
