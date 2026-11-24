import YM.OPE.Compatible.Tune.Globe
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# A right inverse and kernel for the frame map

For a `Cart`, `FitPel` proves that `Pel` is a right inverse of `FirP`, and
`PelCost` gives its uniform polynomial norm bound in `Y`. `FinAura`
identifies the kernel of `FirP` with the terminal subspace `Bay`. `RiseZip`
shows that `FirP` sends the shift `Gift` to the shift `FlowP`.
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

noncomputable abbrev LineCt (W:GlowPack Hp Z a (k:=k)):=Mel (Eagle Hp Z a W)
noncomputable abbrev Disc (W:GlowPack Hp Z a (k:=k)):= Dux G l W.W
noncomputable abbrev FirP:= Pilotπ Hp Z a W U hq hp V D j'
noncomputable def Pel : LineCt W→L[ℝ] Tracts G d τ:= by
     exact ScaledB W.fro D.R j'
lemma Pelleg (x:LineCt W): Pel D j' x=bulk D.R j' ((honors W.fro).symm x):=rfl
lemma FitPel (x:LineCt W): FirP D j' (Pel D j' x)=x:=by
     exact FitSea D.fee W.fro j' x
lemma PelCost : Wealth (fun j=>Pel D j) Y 1:=by
     exact SeaCost D.fee W.fro
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
lemma FinAura (x:F!) : x∈Bay U.flag Sγ (l+1) j' ↔ FirP D j' x=0:=by
       exact Mercy D.fee W.fro j' x
lemma RiseZip (x:F!): FirP D j' (Gift G D₀.aware x)= FlowP (Eagle Hp Z a W) (FirP D j' x):=by
       exact κSym D.fee W.fro j' W.vnd W.tal x
end
end YM.OPE.Stroke
