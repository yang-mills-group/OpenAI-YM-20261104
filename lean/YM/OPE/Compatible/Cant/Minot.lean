import YM.OPE.Compatible.Cant.Pion
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Sect
import YM.OPE.Compatible.Cant.Turned
import YM.OPE.Compatible.Cant.Knit
import YM.OPE.Compatible.Cant.Ki
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Cant.Hoe
/-!
# Positivity and scaling at the selected pair of sites

Under `GlowK`, `YM.OPE.Stroke.Earnings` gives strict positivity of the order-zero, phase-zero form on a nonzero vector supported in its zeroth component.
At the same wrapped sites, `portrate` gives the phase-one pairing at order one as `(lapPrice P.L e'.val)²` times its value at order zero.
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
local notation "μ"=> lapPrice (Patch.L P)
-- Evaluate the forms at the two sites obtained by wrapping the selected axis points.
variable (e':Fin (l+1))(S:Submodule ℝ (Bead G l e'.val))(V₀:Even n.val)
local notation "v*!"=> wrap n (skew a)
local notation "p*!"=> wrap n (Point a)
noncomputable abbrev Lγ (r:ℕ): ΦB (↥S):=TokZ Hp Z a e' S V₀ v*! p*! r
abbrev GlowK :Prop:= Glow H hs X B Z.station D₀ (Z.bill e'.val e'.isLt) a Hp S n V₀ k
set_option maxHeartbeats 200000 in
lemma Earnings (L:GlowK (k:=k) Hp Z a e' S V₀)(x:S)(hx:x≠0): 0 < Lγ Hp Z a e' S V₀ 0 0 (Pi.single 0 x) (Pi.single 0 x):=by
      let q:= (Pi.single 0 x: Jewel S); let u:=Plato Z e'.val S e'.isLt q; have hq:= ZFore Hp Z a e'.isLt u V₀ v*! p*! L.care L.pins; have ht : UΦ Z e'.isLt u 0=x.val:= ((Mway (E:=↥(Fruition Z.station (μ e'.val))) (BoxesΦ Z e'.val e'.isLt) q 0).symm.trans (congr_arg Subtype.val (Pi.single_eq_same ..))); rw [ht] at hq; change 0< TokZ Hp Z a e' S V₀ v*! p*! 0 0 q q; exact lt_of_lt_of_eq (L.rent _ x.property (Subtype.coe_ne_coe.mpr hx)) (hq.trans (tokEq Hp Z a e' S V₀ v*! p*! q q (0:Phase) 0).symm) -- Use the zeroth coefficient of the lifted token. 
lemma portrate (L:GlowK (k:=k) Hp Z a e' S V₀)(x y:Mint Z e'.val):
    let f(i:ℕ):= Por Hp Z e'.val 1 V₀ v*! p*! a i
    f 1 x y=μ e'.val*(μ e'.val)*f 0 x y:=by
       have H':=VitaX H hs X B Z.station D₀ (Z.bill e'.val e'.isLt); exact Thruster.win H' _ (fed H hs X B Z.station D₀ (Z.bill e'.val e'.isLt) a V₀ v*! p*! Hp L.care L.pins) L.rebate (EndFare ..) x y
end YM.OPE.Stroke
