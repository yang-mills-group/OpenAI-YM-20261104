import YM.OPE.Compatible.Chest.Wild
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Factorization through the three phase projections

For a finite-dimensional target, `Trinity` applies `Dismantle` successively
at phases two, one, and zero. Assuming `Aware d τ`, `4 ≤ r`, `1 ≤ Y`, a
polynomial norm bound for `L`, and `Docked X hb L e 3 K`, it writes `L` as
the sum of three maps through `StageM`, each with a polynomial norm bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
open Silt.Phere Silt.Float
section
variable (h:Aware d τ)(X:M→Train r)(hb:r ≥ 4)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (L:M→solar G d τ→L[ℝ] E)
include h
set_option maxHeartbeats 200000 in
lemma Trinity (hz:1 ≤ Y)(hp:Wealth L Y 1)(hx:Docked X hb L e 3 K):∃ S: M→ Terra G τ d 2→L[ℝ] E, ∃ T:M→ Terra G τ d 1→L[ℝ] E, ∃ V:M→ Terra G τ d 0→L[ℝ] E,Wealth S Y 1 ∧ Wealth T Y 1∧Wealth V Y 1 ∧ L=beneath (K:=K) (e:=e) X hb 2 S + beneath (K:=K) (e:=e) X hb 1 T +beneath (K:=K) (e:=e) X hb 0 V :=by
       obtain ⟨S,hS,cS⟩:=Dismantle h X hb L 2 hz hp hx; let Z:= beneath (K:=K) (e:=e) X hb 2 S; have hv: Wealth Z Y 1:=PledgeW hS (StagePrice X hb 2 hz); have hr:= subW hz zero_le_one hp hv 
       obtain ⟨T,hT,cT⟩:=Dismantle h X hb (L-Z) 1 hz hr cS; let W:=beneath (K:=K) (e:=e) X hb 1 T; have hw: Wealth W Y 1:=PledgeW hT (StagePrice X hb 1 hz)
       obtain ⟨V,hV,cV⟩:=Dismantle h X hb (L-Z-W) 0 hz (subW hz zero_le_one hr hw) cT; refine ⟨S,T,V,hS,hT,hV,?_⟩; let P':= beneath (K:=K) (e:=e) X hb 0 V
       have he: L-Z-W-P'=0:=by
             ext1 i; apply ContinuousLinearMap.ext; intro p; exact cV.boom i p (fun y hy=>by omega)
       change L=Z+W+P'; rw [← (show L-Z-W=P' from sub_eq_zero.mp he)]; abel
end
end YM.OPE.Stroke
