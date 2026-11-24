import YM.OPE.Compatible.Docks.Slate
import YM.OPE.Compatible.Docks.Mil
import YM.OPE.Compatible.Tune.Theta
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# A right inverse for the perturbed coefficient reading

`FirQi` constructs an eventual right inverse of the zero-parameter map `ZeroPz`
under the `Lineage`, growth, and `Sound` hypotheses with `l < d + 6`. `Fior` bounds
the perturbation to `SpinOrbit`. When its exponent is strictly negative,
`LaunchRank` gives exponent-zero bounds for `SpinOrbit` and its eventual right inverse.
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
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l (d+6) w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
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
open Silt.Phere
open Pill Yolk Spells Silt.Phere
local notation "U!"=> τ
local notation "M*!"=> solar G (d+6) τ
variable {A:Labels.Frame G l}{A0:Source.Hol G}{T':Source.SectionData A}
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
section
local notation "Jθ"=>A.Index
variable (O:I→ A.Index → Asp T' A0 d)(B':Spells.Pad G)(μx:I→M)
variable {η ℓ β:I→ℝ}{f:Filter I}{R':I→BudgetPoint}
variable (hL:Lineage (f:=f) (β:=β) η K.K (fun i:I=> (V (μx i)).gear) hp ℓ R' O (τ 0))
local notation "Bₗ"=> (Bright O B' μx (D₀:=D₀) (V:=V) (hp:=hp))
variable (Yz:Wax β f (Y ∘ μx) 0)
include hL Yz
lemma WinQ (t:Phase) : Wax β f (fun i=> Eψ D (μx i) t) 0:= growUp hL.born (fun i=> Eψ D i t) Y μx (Ecost D t) Yz
noncomputable def ZeroPz (i:I) :=doublet (Eψ D (μx i) 0) ∘L (Bₗ i)
lemma WinTop : Wax β f (ZeroPz D O B' μx) 0:=by
       let Q(i:I) := Eψ D (μx i) 0; have hp₁: Wax β f (fun i=>doublet (Q i)) 0:= twins (WinQ D O μx hL Yz 0); exact Lapμ _ _ (scent O B' μx hL) hp₁
variable {θ:I→ℝ}{s:ℝ}(he:s<0)(ht:Wax β f θ s)
lemma Fior (h: s≤0)(hx:Wax β f θ s): Wax β f ((fun i=>SpinOrbit D O B' μx (θ i) i)-ZeroPz D O B' μx) s:=by
       let E(k):= fun i=> Eψ D (μx i) k; have hP : Wax β f (E 1) 0:=WinQ D O μx hL Yz 1; have hE : Wax β f (E 2) 0:= WinQ D O μx hL Yz 2; have hz:=scent O B' μx (D₀:=D₀) (hp:=hp) hL; exact Poke (Bₗ) (E 0) (E 1) (E 2) hL.born hz hP hE h hx
variable (hT:T'.Sound A0)(hv:l<d+6)
include hT hv
lemma FirQi : ∃ V:I→(OrthoC W×OrthoC W)→L[ℝ] A.Coeff, Wax β f V 0 ∧∀ᶠ i in f, ZeroPz D O B' μx i ∘L V i=ContinuousLinearMap.id ..:=by
        let q:I→Train i:=fun j=>(V (μx j)).gear; let A(i):= GateQ D (μx i); let Y(i):=gLift D (μx i); let X(i):= ζWide O B' q hp D₀ i; refine Yolk.trip (ZeroPz D O B' μx) A X (fun i=>WaveD D O B' μx i) Y (show Wax β f Y 0 from growUp hL.born (fun i=>gLift D i) _ μx (ReserveK D) Yz) (fun i x=>GrovesK D (μx i) x) ?_ ; exact spanROI O B' q hp D₀ hL hT hv
include he ht
lemma LaunchRank : Wax β f (fun i=>SpinOrbit D O B' μx (θ i) i) 0 ∧ ∃ V:I→ (OrthoC W × OrthoC W)→L[ℝ] A.Coeff, Wax β f V 0 ∧∀ᶠ i in f, SpinOrbit D O B' μx (θ i) i ∘L V i=ContinuousLinearMap.id ..:=by
         exact Yolk.FindRise (F:=OrthoC W× OrthoC W) (ZeroPz D O B' μx) (fun i=> SpinOrbit D O B' μx (θ i) i) hL.born he (WinTop D O B' μx hL Yz) (Fior D O B' μx hL Yz he.le ht) (FirQi D O B' μx hL Yz hT hv)
end
end
end YM.OPE.Stroke
