import YM.OPE.Compatible.Camo.Sow
import YM.OPE.Compatible.Mason.Port
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
open Stroke Ibis Borealis Borealis.Galea
variable (L:Host K T)
structure CoT where
       T:BudgetPoint
       b:ℕ
       F:Config G L.c→ℂ
       a:ℂ→L[ℝ]ℝ
       x: Site L.c
       P:Spells.Pad G
       good:2*(b+1)< L.c.val
namespace CoT
variable {L}
variable (Y:CoT L)(U: Train j)(H:4 ≤ j)(w b:ℝ)
abbrev Note (t:ℝ)(k:ℕ):Prop:=Acceptance Y.x Y.T k Y.F Y.b t
variable (h: Y.Note t (k+6)) {τ:Phase→ℕ}(hx:Aware (k+6) τ)
noncomputable abbrev Ross:= ChiselV hx (Recon Y.x Y.P Y.good Y.T Y.F Y.a K.K U H w h)
-- mark.W pointer normal
abbrev hymn:= Elev Y.T Y.F Y.a Y.x Y.P Y.good w b
abbrev Night(v:Bid.Dir G L.c):= Dark Y.x U H Y.P Y.T Y.F Y.a w Y.good h K.K (charW Y.x v) b
lemma Day : Y.hymn w b= inkM (Goan (vintage G hx b (Y.Ross U H w h hx))) (k+6) Y.x + Night Y U H w b h:= funext fun i=>crossed Y.x U H Y.P Y.T Y.F Y.a w Y.good h hx i K.K b
local notation "Φ"=> Vessel K.K U G L.c H
local notation "Z"=> (Chart.tangent G (Body 1 L.c))
lemma Lodge (p:Phase): GuardB (Chart.tangent G (Body 1 L.c)) Φ 0 (k+1) (skry (Night Y U H w b h) p):=by
       let X:= (flats G L.c).toContinuousLinearMap; let f:= Dark Y.x U H Y.P Y.T Y.F Y.a w Y.good h K.K; have he : Night Y U H w b h=fun i=>f (Charu Y.x X i) b :=by
             funext i; apply congr_arg (fun k=>f k b); simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using climbsF Y.x (flats G L.c).toContinuousLinearMap i
       rw [he]; exact (Mantle Y.x X Z Φ U H K.K Y.b (vessel_c U H) Y.P Y.T w Y.F Y.a Y.good h b p).skids (Nat.zero_le _) (by have h:=p.isLt;omega)
include hx h U H
lemma LapH : Status (hymn Y w b):=by
        have hp:= InkG Y.x (vintage G hx b (Ross Y U H w h hx)).val; let p:= Night Y U H w b h; intro i; rw [Day Y U H w b h hx,BaddH]; exact (Stature.poly (hp i).cost _).add ((Lodge Y U H w b h i).hW)
where BaddH (p q:Bid.Dir G L.c→Token)(i:Phase):skry (p+q) i=skry p i+skry q i:=by fin_cases i<;> rfl
end CoT
end
end YM.OPE.Cameo
