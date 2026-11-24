import YM.OPE.Compatible.Tune.Scroll
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Squared-norm estimate for a single frame block

For a map satisfying `Pipes.Stamp` and a perturbation with `|r| ≤ 1`,
`GlowPack.SigmaFares` bounds the deviation of the squared norm of the
perturbed block from `(μ i.val ^ j * ‖x‖) ^ 2`, where `μ` is `lapPrice`.
The quadratic term has a common constant for all blocks and powers `j`.
The cubic term uses `ζCost` of the corresponding diagonal block.
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
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
namespace GlowPack
variable (W:GlowPack Hp Z a (k:=k))
noncomputable abbrev Link (i:Fin (l+1)):= ↥(W.W i.val)
noncomputable abbrev Eagle (i: Fin (l+1)) := Brane (Link Hp Z a W i)

noncomputable abbrev ΦAct : (i:JΛ)→ℕ→ ΦB (Eagle Hp Z a W i):=fun i=>Lore (W.fro i) (Lγ Hp Z a i (W.W i.val) (W.evenK i))
local notation "μ"=>lapPrice (Patch.L P)
lemma SigmaFares :∃ c:ℝ,1 ≤ c ∧ ∀ (i:Fin (l+1))(j:ℕ)(T:Mel (Eagle Hp Z a W)→ₗ[ℝ] Mel (Eagle Hp Z a W)), Pipes.Stamp (μ) (ΦAct Hp Z a W) T j→∀ x:Eagle Hp Z a W i,∀ r:ℝ,|r|≤1→ |‖border r T (Pi.single i x) i‖^2-(μ i.val^j*‖x‖)^2|≤((j:ℝ)*(μ i.val^j)^2*c*r^2 + |r|^3*3*(ζCost (PDiag T i))^2)*‖x‖^2:= by
       exact PortCost (ΦAct Hp Z a W) (fun i=> Kw (W.fro i) (σPulse Z i _ (W.pay i))) W.authL (fun i=>EndFare _ i)
end GlowPack
end YM.OPE.Stroke
