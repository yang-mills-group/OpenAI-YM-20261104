import YM.OPE.Compatible.Tune.Star
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# The transport identity in normalized frame coordinates

`Araw` identifies the underlying linear map of `EFrame` with `Pong`
expressed in the chosen frames. Under the `Ace` hypothesis, `starWire`
shows that applying the map on tracts and then `FirP` agrees with applying
`EFrame` after `FirP`. `rayT` transfers the order-`r` condition `Stamp` to
this frame map.
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


variable {vα:I→ℝ}{A:(x:I)→Alps K T j (vα x)}{V':Z.Ω I vα}{hp':4 ≤ j}{hz: 1≤vα}
variable (D':Cart Hp Z a W V' hz hp' A)(t:I)(U': Tracts G d τ →L[ℝ] Tracts G d τ)
local notation "G!"=> Gauge
local notation "T*!"=>LineCt W
variable (M':Ace D₀ H hs a (V j') (A t) (zero_le_one.trans (hq j')) (zero_le_one.trans (hz t)) hp hp' r U')
lemma Araw : (EFrame D j' D' t U').toLinearMap= Uptake W.fro (Pong D j' D' t U') := by
     exact (owns D'.F j' t D'.fee (R:=D.R) W.fro U').symm
local notation "Fν"=> EFrame D j' D' t U'
local notation "Lπ"=>FirP D
include M'
lemma starWire (x:Tracts G d τ): FirP D' t (U' x)= EFrame D j' D' t U' (FirP D j' x):= by
     have he:= (Marks D j' D' t U' M').2; have hz : FirP D' t (U' x)= Uptake W.fro (Pong D j' D' t U') (FirP D j' x):= stored D.F D'.F j' t D.fee D'.fee W.fro U' he x; exact hz.trans (congr_arg (fun y:LineCt W→ₗ[ℝ] LineCt W => y (FirP D j' x)) (Araw D j' D' t U').symm) 
set_option maxHeartbeats 200000 in
lemma rayT : Stamp (μ) (ΦAct Hp Z a W) (EFrame D j' D' t U').toLinearMap r:=by
     rw [Araw]; exact transS W.fro W.vnd W.tal (Marks D j' D' t U' M').1
end
end YM.OPE.Stroke
