import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Fiscal
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# The transport operator between matched frames

`Stint` expresses the fine-to-coarse motion in frame coordinates.
`StampP` proves its `Ace` condition when the patch side is the specified
power of the base side. For a family with bounded fares, the stage condition
`Mag`, and fine fees of upper rate zero, `StintCost` bounds its upper
exponential rate by zero along a clock tending to infinity.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
variable (V:Foyer L hs a l d) {hk:highStage L hs a V≤ P'.J}{he:highStage L hs a V ≤ j}
variable (X:BankW L hs a V hk p)
namespace MatchZ
section rise
variable (D:MatchZ P' p p' T j R) (B:Medal P' G K.K P'.J)
local notation "Z"=>V.pay.st
abbrev sportB (H:LocalRatio R) := spots H B D.fine.ℳ D.coarse.ℳ D.bound 
noncomputable abbrev Stint := MotionX H hs (sportB (H:=H) D B) V.pay.st.hτ P'.order_cut D.bound.mag.2.1

section
variable {he':highStage L hs a V≤ P'.J}
include he'
set_option maxHeartbeats 200000
lemma StampP (ht:P'.L=V.pay.st.S.L^r): Ace (Z).stars H hs a D.fine.ℳ D.coarse.ℳ (zero_le_one.trans D.fine.positive) (zero_le_one.trans D.coarse.positive) P'.order_cut D.bound.mag.2.1 r (Stint V D B):=by
       let f(_:Unit):=D.fine.ℳ; let g(_:Unit):= D.coarse.ℳ; have hp: l+1 ≤ P'.J:= (show l+1≤ V.pay.st.S.J from le_trans (by omega) (Z).stars.oak).trans he'; have hF:=motionAd H hs (Z).stars f g D.bound.mag (fun _=> D.bound) B (fun _=> zero_le_one.trans D.fine.positive) (fun _=>zero_le_one.trans D.coarse.positive) ht hp (Z).holds (Nat.lt_succ_self _) a
       exact sprintGate _ hF ()
omit he'
end
-- The fare bound is uniform over the family.
variable (S:I→MatchZ P' p p' T j R) (R':ℝ){l₀:Filter I}{v:I→ℝ}{γ:ℝ}(h:∀ i,|MatchZ.fare (S i)|≤R')(ht:Tendsto v l₀ atTop)(hV:RateLE l₀ v (fun i=> (S i).fine.fees) 0)
include h ht hV
lemma StintCost (hh:Mag P'.J j) : RateLE l₀ v (fun i=> Stint V (S i) B) 0:=by
        let f(i):= (S i).fine; let t i:= MatchZ.fare (S i); have he: Wealth t (fun i=>(f i).fees) 1:= ⟨max 0 R',le_max_left ..,0,fun i=>by rw [pow_zero,Pi.one_apply,mul_one,mul_one]; exact (h i).trans (le_max_right ..)⟩; have hT:=MotionFee H hs (fun i=>(S i).fine.ℳ) B V.pay.st.hτ t (fun i=>(S i).fine.clip) hh.2.1 (z:=fun i=>(S i).coarse.fees) (vν:=fun i=>(S i).fine.fees)  (fun i=>(S i).coarse.ℳ) (fun i=>sportB (H:=H) (S i) B) (fun i=>(S i).fine.positive) he 
        exact height_W l₀ v (fun i=> Stint V (S i) B) id hT ht hV
end rise
end MatchZ
end
end YM.OPE.Stroke
