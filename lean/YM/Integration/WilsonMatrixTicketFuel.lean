import YM.FullVolume.Cross
import YM.FullVolume.Roll.Fiscal
import YM.OPE.Compatible.Niche.Pique
import YM.OPE.Compatible.Niche.Fur

/-! The physical data needed for the quantitative frame estimates. Every
field and every edge of the kinetic overlay is identified with the one on the
retained construction. The steering profile for larger source purchases
is independent of this interface. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Extract Dash OPE OPE.Owl
variable {G:Gauge}
set_option quotPrecheck false
structure FuelV (g:G.Simple) (s:Sheet G) (p:MapPrices) (H:Votive.Sponsor G)
    (K:Votive.Seasons H) (a:Axis) (X:Stroke.PriceBook (chart_ok G) K) (t:ℕ→ℕ)
    (U:Rolls (ThroughLaunch.raise s t)) (P:Spells.Pad G)
    (D:Desk (ThroughLaunch.raise s t) X a g) (S:Alloy (ThroughLaunch.bountyV s p t) U) where
  y : ℕ→ℝ
  B : Bid.Worth
  cabinet : Factor S
  sat : Bandage cabinet y B
  amp : Bolt S
  refQ : ℕ→ℕ
  shifts : ∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail amp) N p
  nest : Nest cabinet amp
  makes : (Family.mk (Issue.trail amp) (hol G) (Labels.frames G) (localSection G) refQ shifts).Makes
  tell : Votive.Lend s K
  bankL : ∀ i, 16 ≤ (U.L i).val
  turtle : ThroughLaunch.Imperial (s:=s) H.X p H.l S.post S.B.a S.B.M S.B.kin
  costE : BeatV D P S.θ cabinet.books S.delay
  analysisK : TowerCap (M:=ThroughLaunch.bountyV s p t) S.θ S.delay

variable {g:G.Simple} {s:Sheet G} {p:MapPrices} {H:Votive.Sponsor G}
    {K:Votive.Seasons H} {a:Axis} {X:Stroke.PriceBook (chart_ok G) K} {t:ℕ→ℕ}
    {U:Rolls (ThroughLaunch.raise s t)} {P:Spells.Pad G}
    {D:Desk (ThroughLaunch.raise s t) X a g} {S:Alloy (ThroughLaunch.bountyV s p t) U}

namespace FuelV
def Holds (C:FuelV g s p H K a X t U P D S):Family G :=
  Family.mk (Issue.trail C.amp) (hol G) (Labels.frames G) (localSection G) C.refQ C.shifts

theorem time (C:FuelV g s p H K a X t U P D S) (m:ℕ) :
    16 ≤ (C.Holds.S.block m).val := by
  change 16 ≤ (S.B.a.S.block m).val
  rw [Push.PriceCompiler.block_eq S.B.valid m]
  exact C.bankL _

end FuelV
end YM.PhysicalNext.Repeat.Legato
