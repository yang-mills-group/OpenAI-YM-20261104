import YM.OPE.Compatible.Roost.Pool
/-! # Horts from project-bearing flights -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} (D₀:Stern K P τ l d w)(Hp: Alps.Crest G P K.K m)
section
variable (H hs)
variable (B':Medal P' G K.K P'.J)
def iotaK (P:Patch)(hv:Mag P.J j)(v: Train P.J):Flight P.J j:=⟨P.L,P.odd_side, P.coarse, hv.1,(by obtain ⟨_,_,h⟩:=hv; omega), (by obtain ⟨_,_,h⟩:=hv; omega),v⟩
lemma iotas (v: Flight P.J j)(hv:v.L=P.L)(hx:Mag P.J j): v=iotaK P hx v.wing:=by
     cases P; cases v; dsimp at hv;subst_vars;rfl
include H
lemma spots (A:Alps K T P'.J v)(D:Alps K T j v')(h:Charm P'.L A D u R): Town A D (charmSeal B' A.gear) R u:=by
     obtain ⟨hx,L,hT,hA,hp,ht⟩:=h; have hh:L=iotaK P' hx A.gear:= hA.symm ▸ iotas L hT hx; subst L; exact courtesy (iotaK P' hx A.gear) rfl hp hx B' ht H
omit H
lemma endV (A:Alps K T P'.J v) (D:Alps K T j v')(h:Mag P'.J j)(he:Charm P'.L A D u R): D.gear=(iotaK P' h A.gear).land:=by
     obtain ⟨_,t,h',ht,hD,_⟩:=he; have hv:t=iotaK P' h A.gear:=(iotas t h' h).trans (congr_arg _ ht.symm); subst t; exact hD
variable {Y Z uα:M→ℝ}
-- fixed counts.All shifts.
open Topic
include H
set_option maxHeartbeats 200000 in
lemma motionAd (V:(j:M)→Alps K T P'.J (Y j))(A:(t:M)→Alps K T j (Z t))(hv:Mag P'.J j)(hp:∀ t,Charm P'.L (V t) (A t) (uα t) R) (B':Medal P' G K.K P'.J) (hY:0≤Y)(hZ:0≤Z)(hm:P'.L=P.L^m)(hk:l+1 ≤ P'.J)(ha:∀ i,Rise.stamp' d G k+44 ≤τ i)(hB:l+l<k)(o:Axis) :
     let T(x):=MotionX H hs (spots H B' (V x) (A x) (hp x)) D₀.aware hv.1 hv.2.1
     Sprint H hs D₀ Y Z o V A hv.1 hv.2.1 hY hZ m T:=by
          intro T'; refine ⟨fun j p=> HexMood H hs _ D₀.aware hv.1 hv.2.1 p, ?_, fun n V' x y _ hh k' z p q=> portGrowth (D₀:=D₀) (V z) H hs (spots H B' _ _ (hp z)) hv.1 hv.2.1 (hY z) (hZ z) V' x y hm hh o p q k' hB ha⟩
          apply Aeon.March.ofSlope
          · intro z; let Q:= iotaK P' hv (V z).gear; exact trimU H hs D₀.aware Q B' hv (by rfl) (endV (V z) _ hv (hp z)) (spots H B' (V z) (A z) (hp z))
          intro z n i hn x hx hx'; let Q:= iotaK P' hv (V z).gear; exact quantit H hs Q B' hv (by rfl) (endV _ _ hv (hp z)) (spots H B' (V z) (A z) (hp z)) D₀ hm n hn hk x i hx hx'
end
end YM.OPE.Stroke
