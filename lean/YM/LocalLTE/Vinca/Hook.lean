import YM.LocalLTE.Vinca.Ports
import YM.LocalLTE.Weave.Tourney
/-! authorise L-floors after base.C.Shapes.Qu.Up t.Kind. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost ConnectedActivityE6
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Mallow
-- α.L.Z prereq only.After allocations after-L high.Appear physical.Level.H.D paying.
structure Elixir (G:Gauge) (M:ℕ) where
    invests {X:Metals G}{D:Rolls X.p}{C:Targets X.p X.K}{Y:Expenses C}{w:Return.Wages}{v:ℕ→ℝ}{T:Protection D} (X':Register D Y w v) (μ:ℝ) (ℓ:ℕ→ℕ→ℕ) (e:ℕ→ℕ→ℕ→ℕ) (Q:Delays T): Prop -- restrict by τ elsewhere
    pays {s:Sheet G} {K: MapPrices}(C:Targets s (ThroughLaunch.bearing s K))(Y:Expenses C)(hc:∀ i j,(C i j).halo=500 ∧ (Y i j).wanting=-(7/16:ℝ)) (μ k:ℝ)(hκ:Reliable G μ k): ∃ L:ℕ→ℕ,∀ l:ℕ→ℕ,L≤l→ ∀ (D:Rolls (ThroughLaunch.raise s l)){w v T}(X':Register D Y w v)(ℓ:ℕ→ℕ→ℕ)(e:ℕ→ℕ→ℕ→ℕ)(Q:Delays T),∃ U:Delays T,DelayLe Q U∧∀ Y,DelayLe U Y→ invests (X:=ThroughLaunch.currency s K l) X' μ ℓ e Y
-- supplies read p tok generation etc.
variable {M:ℕ} (V : Elixir G M) {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}{p:ℕ}{ε:ℝ}(F:Funding R p ε)(W:Trail F M)
noncomputable def Fulfilled := V.invests (X:=X) R.shape F.κ W.footprint W.κT A.delay
noncomputable def tokenX (G:Gauge)(M:ℕ):Elixir G M:=⟨fun _ _ _ _ _ => True,fun _ _ _ _ _ _=>⟨fun _=>0,fun _ _ _ _ _ _ _ _ _ Q=> ⟨_,DelayLe.refl Q,fun _ _=>trivial⟩⟩⟩ -- yaw
end YM.PhysicalNext.Repeat.Legato
