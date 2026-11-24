import YM.OPE.Compatible.Cant.Pion
import YM.OPE.Compatible.Cant.Knit
import YM.OPE.Compatible.Cant.Ki
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Cant.Hoe
/-!
# The first component and phase shift of the one-step map

For the readout maps in a `Bals` decomposition, `YM.OPE.Stroke.SigmaTop` shows that `σPulse` multiplies the first component at grade `e'` by `lapPrice P.L e'.val`.
`SigmaX` shows that the same endomorphism commutes with the phase shift `τΓ`.
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
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "μ"=> lapPrice (Patch.L P)
variable (e':Fin (l+1))
set_option maxHeartbeats 200000 in
lemma SigmaTop {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(x': Jewel (A' e'.val)):σPulse Z e' (A' e'.val) (κ e') x' 0=μ e'.val • (x' 0):=by
      let v:=Plato Z e'.val (A' e'.val) e'.isLt x'; let U:= portC Z.station (μ e'.val) 3; have he : BoxesΦ Z e'.val e'.isLt (U v) 0= _:= (VitaX H hs X B Z.station D₀ (Z.bill e'.val e'.isLt)).body v; change κ e' (U v) 0= _; rw[Bals.headLift Hp Z a C e' _ _ _ he,show κ e' v=x' from C.tricks e'|>.len x']
lemma Fez (e:Fin (l+1))(x:Mint Z e.val) :
     let U:=portC Z.station (lapPrice P.L e.val) 3; let F:=WaneZ Z e.val e.isLt; U (F x)=F (U x):=by
       exact Thruster.oars (X:=VitaX H hs X B Z.station D₀ (Z.bill e.val e.isLt)) x
set_option maxHeartbeats 200000 in
lemma SigmaX {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(u:Jewel (A' e'.val)) :σPulse Z e' _ (κ e') (τΓ _ u)=τΓ _ (σPulse Z e' _ (κ e') u):= by
     let p:= Plato Z e'.val (A' e'.val) e'.isLt; let F:= portC Z.station (μ e'.val) 3; let g:=WaneZ Z e'.val e'.isLt; have ht:κ e' (F (p (τΓ _ u)))= κ e' (F (g (p u))):=congr_arg (κ e') (congr_arg F (sprain Z e'.isLt _ u)); have hh:κ e' (F (g (p u)))=κ e' (g (F (p u))):=congr_arg (κ e') (Fez Z e' (p u)); exact ht.trans (hh.trans (Bals.shift Hp Z a C e' (F (p u))))
end YM.OPE.Stroke
