import YM.OPE.Compatible.Mould.Ash
/-!
# Coerc.G rank stamp selection & radical proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {u ν:M→ℝ}{hp:4 ≤ i}{V:(j:M)→Alps K T i (u j)}
namespace Topic
open Balsam Nestle StageLight Pert.Full
local notation "X!" =>Mint Z e
variable (he:e<l+1)(hv:l+l<k)(ht:∀ i,τ i≤m)(hp:∀ i,Rise.stamp' d G k+44≤τ i)
local notation "Tν"=>portC (Topic.station Z) (lapPrice P.L e) 3
abbrev Zpin (V:Even n.val)(x y:Site n):= boss H hs X B Z.station D₀ (Z.bill e he) V a Hp x y
lemma ZFore (p:X!)(v:Even n.val)(x y:Site n)(hx:Attest G P d k e l m τ n)(hh:Pins K P x y):
     Zpin Hp Z a he v x y (UΦ Z he p 0) (UΦ Z he p 0)=(WingP Hp Z a v x y p p 0).s:= (quotaQ H hs X B Z.station D₀ (Z.bill e he) v a Hp x y hx hh p p).symm.trans (show _= UnitBorn Hp Z a v x y 0 0 p p from flareP Hp Z a p p v x y 0 0)
lemma porShift (p:Mint Z e)(i:Phase)(ht:trims i.val p.val): ∃ y:Mint Z e,p=(fun x=> WaneZ Z e he x)^[i.val] y ∧ UΦ Z he p i=UΦ Z he y 0:=by
       exact Thruster.isNet (VitaX H hs X B Z.station D₀ (Z.bill e he)) i p ((bridgeV Z i.val i.isLt.le he p).1 ht)
lemma gyro (V:Even n.val)(x y:Site n)(hp:Attest G P d k e l m τ n)(hx:Pins K P x y)(i:Phase)(p q:Mint Z e) : (WingP Hp Z a V x y ((fun x=> WaneZ Z e he x)^[i.val] p) q 0).seq i.val=(WingP Hp Z a V x y p q 0).seq 0:=by
      exact soFarV (E:=Fruition Z.station (lapPrice P.L e)) (fun v=> WaneZ Z e he v) (fun x'=> WingP Hp Z a V x y x' q 0) (fun v=> (Polygon0 Hp Z a V x y hx hp 0 he v q).1) p i
end Topic
end YM.OPE.Stroke
