import YM.OPE.Compatible.Tune.Spectra
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Transport between two frames

`EFrame` lifts a source frame vector with `Pel`, applies the given linear
map on tracts, and projects with the target `FirP`. Under the `Ace`
hypothesis on that map, `Marks` proves the order-`r` condition `Stamp` for
`Pong` and shows that `Pong` intertwines the source and target `port` maps.
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
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
-- The source and target share the frame data `W`.

variable {vα:I→ℝ}{A:(x:I)→Alps K T j (vα x)}{V':Z.Ω I vα}{hp':4 ≤ j}{hz: 1≤vα}
variable (D':Cart Hp Z a W V' hz hp' A)(t:I)(U': Tracts G d τ →L[ℝ] Tracts G d τ)
local notation "G!"=> Gauge
noncomputable def Pong := Race (V:=Dux G l W.W) (R:=D.R) D'.F j' t U'.toLinearMap
local notation "T*!"=>LineCt W
noncomputable def EFrame : LineCt W→L[ℝ] LineCt W:= (FirP D' t).comp (U'.comp (Pel D j'))
variable (M':Ace D₀ H hs a (V j') (A t) (zero_le_one.trans (hq j')) (zero_le_one.trans (hz t)) hp hp' r U')
include M'
private abbrev markedMotion :=
  stamped (hq := hq) (hz := hz) (V := V) (A := A) (U := U) (U' := V')
    (A' := W.W) (κ := W.pay) (M' := D.R) (P' := D'.R)
    Hp Z a D.Hexi D'.Hexi U' j' t D'.shapes.choose_spec D'.tally D'.Stable M'
    W.trial D.F D'.F (t := W.evenK)
    (fun i => wrap (W.scope i) (skew a)) (fun i => wrap (W.scope i) (Point a))
    (fun i => (W.fund i).care.base) (fun i => (W.fund i).pins)

set_option maxHeartbeats 200000 in
lemma Marks : Stamp (V:=Dux G l W.W) (lapPrice P.L) (fun e=> Lγ Hp Z a e (W.W e.val) (W.evenK e)) (Pong D j' D' t U') r ∧∀ x:Tracts G d τ, port D'.F t (U' x)= Pong D j' D' t U' (port D.F j' x):=by
  exact markedMotion D j' D' t U' M'
end
end YM.OPE.Stroke
