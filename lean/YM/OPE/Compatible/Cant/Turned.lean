import YM.OPE.Compatible.Cant.Pion
import YM.OPE.Compatible.Cant.Ki
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Cant.Hoe
/-!
# One step in the order of the lifted pairing

For the readout map of a `Bals` decomposition, `YM.OPE.Stroke.aheadU` gives the order-`t + 1` form `Lais` by applying `σPulse` to both arguments of the order-`t` form.
The identity holds at pinned sites on an even lattice satisfying the barrier bound.
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
variable (n:Side)(V':Even n.val)(x y:Site n)
lemma FireH (p:E→F)(q:F→ E)(f:F→F)(g:E→ E)(a:ℕ→E→E→ℝ)(b:ℕ→F→F→ℝ)(hp:∀ x y i,a i x y=b i (p x) (p y))(he:∀ x y i,b (i+1) x y=b i (f x) (f y))(hz:∀ x y i,b i x y=b i (p (q x)) (p (q y)))(hx:∀ x,g x=q (f (p x)))(i:ℕ)(x y:E):a (i+1) x y = a i (g x) (g y):=by rw [hx,hx,hp,hp,he,hz (f (p x)) (f (p y)) i]
set_option maxHeartbeats 200000 in
lemma aheadU (e: Fin (l+1)){κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(hv:barrier P ≤ n.val)(hz:Pins K P x y)(t:ℕ)(i:Phase)(u v:Jewel (A' e.val)):
    let L(r):= Lais Hp Z a e r V' i x y (A' e.val); let g:=σPulse Z e (A' e.val) (κ e); L (t+1) u v=L t (g u) (g v):=by
      intro L g; let P' :=Plato Z e.val (A' e.val) e.isLt; let f:=Soul (P:=P) (e:=e.val) Z.station 1; exact FireH (E:= Jewel (A' e.val)) (F:= ↥(Z.Mint e.val)) (fun x=> P' x) (fun x=>κ e x) f (fun x=>g x) (fun r x y=> L r x y) (fun r p q=> Por Hp Z e.val i V' x y a r p q) (fun u v k=>laEQ Hp Z a e k V' i x y _ u v) (fun u v k=>shootZ Hp Z a V' x y i u v k 1) (fun p q r=>ParD Hp Z a C e V' x y hv hz p q r i) (pulseU Z e (A' e.val) (κ e)) t u v
end YM.OPE.Stroke
