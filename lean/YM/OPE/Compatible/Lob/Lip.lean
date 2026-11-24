import YM.OPE.Compatible.Lob.Dye
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
variable (H:LocalRatio R)(hs:G.Simple)(X:Sailing T P p R b)
variable (B:Medal P G K.K P.J)(h:Aware d τ)
lemma grin (n m n':ℕ)(p:cope G i n)(q:cope G i m)(hp:p.val=q.val)(hv:n'≤m)(he:n'≤n): Flume.Script.tiller G i n n' he d p=Flume.Script.tiller G i m n' hv d q:=by apply part_unique; intro i hI x; change honeyX _ _ _ _ _= honeyX _ _ _ _ _; rw [solid_mono,solid_mono,if_pos hI,if_pos hI]; exact congrArg (fun p=>wholeX p (fun j=>ledge (x j (i j)).val)) hp
lemma peakT {u v:Phase}(hp:u≤v)(x:bed G (d+u.val) (τ u))(he:e≤τ v): stepRead G l e (d+v.val) (τ v) he (Len G h u v hp x)=stepRead G l e (d+u.val) (τ u) (he.trans (h.mono hp)) x:=by
     funext i; let p:=terrace G _ _ i.val (Len G h u v hp x); let V:=terrace G _ _ i.val x; have hz:p.val=V.val:= congr_fun (TurnL h u v hp x) i.val; exact congrArg (coordinateQ G l e i.val) (grin _ _ _ p V hz ((Nat.sub_le ..).trans (he.trans (h.mono hp))) ((Nat.sub_le ..).trans he) (d:=l)) -- hp etc annotate coord
variable (X': Tracts G d τ→L[ℝ] Tracts G d τ) {s r w:ℝ} {d':ℕ}(D:Stern K P τ d' d w)
abbrev Cant (i:ℕ):=Fruition X' (lapPrice P.L i)
variable (J': Crown (p:=p) (b:=b) (T:=T) H hs B D X' r s e)
noncomputable def phaseMap := Eave.Vea (G:=Bead G d') J'
local notation "F!"=>Fruition X' (lapPrice (Patch.L P) e)
lemma rope (j:Phase)(hv:e< d'+1): (Turns D j).Tap e=stepRead G d' e (d+j.val) (τ j) (by have hx:= sternCap D j;omega):= dif_pos hv
lemma carrierT (z:Tracts G d τ)(i j:Phase)(he:i.val+1=j.val)(hx:e<d'+1): (Turns D j).Tap e (Gift G D.aware z j)= (Turns D i).Tap e (z i):=by rw [rope D _ hx,rope D _ hx,tack1 D.aware z i j he]; exact peakT D.aware (by change i.val ≤ j.val;omega) (z i) (by have ht:=sternCap D j;omega)
include J' X
lemma spup (i j:Phase)(hp:i.val+1=j.val) (z:Fruition X' (lapPrice P.L e)):
    phaseMap H hs B X' D J' (Fellow (Gift G D.aware) X' (lapPrice P.L e) (Freedom H hs X B X' D J') z) j=phaseMap H hs B X' D J' z i:=by
        exact carrierT D z.val i j hp (Eave.mark (G:=Bead G d') J')
lemma raw0(z:Fruition X' (lapPrice P.L e)) : phaseMap H hs B X' D J' (Fellow (Gift G D.aware) X' (lapPrice P.L e) (Freedom H hs X B X' D J') z) 0=0:= by
       let U:= Gift G D.aware z.val; change (Turns D 0).Tap e (U 0) = _; rw [show U 0= _ from tack D.aware z.val]; exact map_zero _
end YM.OPE.Quit.Jac
