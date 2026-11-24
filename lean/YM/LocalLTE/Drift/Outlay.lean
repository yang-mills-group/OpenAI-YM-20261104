import YM.LocalLTE.Drift.Purse
import YM.LocalLTE.Ticket.Beast
import YM.LocalLTE.Fillet.Whorl
/-!
# Adding the small toll. Sill prepaid.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6
open Mallow Daisy Charity Lotus
variable {G:Gauge}
open YM.LocalLTE.Dilation Push.AbsoluteSums
open LocalLTE LocalLTE.Ticket LocalLTE.Drift LocalLTE.River Extra.Histories
variable (X Y:RG.Stage) (l p r:ℕ) (L:Side) (e:ℝ)
variable {S:Teller G}(Q:ConnectedActivityE6.Target G S)(μ t β:ℝ)(hβ:0< betaF G t L)
noncomputable def smallMeter (G:Gauge) (t:ℝ):= Push.Local.factor (hol G) (localSection G p) X.supportExponent (Cub.title G X) *((L.val:ℝ)^p*2*(sill X.supportExponent l*(betaF G t L)^(-(1/16:ℝ))))
noncomputable def outlay : Drift.TariffX where
    token:=Legato.Spool.budgetV X Y l p r L e Q μ t β hβ
    small:=Legato.Spool.smallMeter X l p L G t
    positive:= mul_nonneg (zero_le_one.trans (factorS G X p)) (mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hβ.le _)))
end YM.PhysicalNext.Repeat.Legato.Spool
