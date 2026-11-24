import YM.LocalLTE.Quay.Flight
import YM.LocalLTE.Orbit.Harvest
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
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
variable {G:Gauge} (M l p r K c d κ₀ :ℕ)(e:ℝ)
open YM.LocalLTE.Vault Animals
lemma jewel_height (q u:ℕ) : ∃ H:Heights,Stature M q e H ∧ u ≤ H.angle 0 0 :=by
   choose a f hv hf using fun i:ℕ=> Fan.heightPlan i q M (-e-1) (i+u)
   let g i n:= Nat.iterate f (n+1) i
   have h i j : g i (j+1)= f (g i j):=by unfold g; exact Function.iterate_succ_apply' ..
   have h1 i:g i 0=f i:=rfl
   let H:= Heights.mk g a (fun i j=> a (g i j)); have hx(i): i ≤ f i:= le_trans (Nat.le_add_right ..) (hv i)
   refine ⟨H,⟨fun d=> hx d, fun d j=> le_trans (hx (g d j)) (h d j).symm.le, fun d=>hf d,fun d j=>?_⟩, (le_add_of_nonneg_left (le_refl 0)).trans (hv 0)⟩
   exact (show HeightPlan (g d j) q M (-e-1) (a (g d j)) (g d (j+1)) from h d j|>.symm ▸ hf (g d j))
end YM.PhysicalNext.Repeat.Legato.Spool
