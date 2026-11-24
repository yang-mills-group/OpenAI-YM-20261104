import YM.OPE.Compatible.Lob.Wires
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
variable (h:Aware d τ)
open Finset
lemma lampHeart (x y:Phase)(hp:x≤y)(A:RowB D!)(p:Seat (d+x.val) (τ x) D!):
    lapD A _ _ (armP _ h _ _ hp p)= armP G h x y hp (lapD A _ _ p):=by
          apply lilies_inj; funext i; rw [armL,pulse_i,pulse_i,armL]
lemma lockC (x y: Phase)(hp:x≤y)(A:RowB D!) (t:ℝ)(p:Seat (d+x.val) (τ x) D!):
    boostS A t _ _ (armP _ h x y hp p)= armP G h x y hp (boostS A t _ _ p):=by
         let X:=(lapD A (τ x) (d+x.val)).toLinearMap; let V:=(lapD A (τ y) (d+y.val)).toLinearMap; let p':=armP G h x y hp
         have hl(i:ℕ):(V^i) (p' p)=p' ((X^i) p):=by induction i with | zero=>rfl| succ i ih=> rw [pow_succ',pow_succ',End.mul_apply,End.mul_apply,ih];exact lampHeart h x y hp A _
         change fixExp V t (d+y.val) (p' p)=p' (fixExp X t (d+x.val) p); rw [Hflow,Hflow,map_sum]; have hk: reduces (rooft D! _ _) X:=by simpa only [one_smul] using! lap_deb A 1 (d+x.val) (τ x)
         have hp' :p∈ rooft D! (d+x.val) (τ x) (d+x.val):= ?_; rotate_left
         · exact (sproutV _ _ p).1 -- check syntax
         simp_rw [hl,map_smul]; symm; refine sum_subset (range_mono (show d+x.val+1≤d+y.val+1 from by have ht:x.val≤ y.val:=hp;omega)) ?_ ; intro i hi hx; have he: d+x.val < i:=by have ht:= show i∉Finset.range (d+x.val+1) from hx; rw [Finset.mem_range] at ht;omega
         rw [(iterateD hk hp' i).2 he,map_zero,smul_zero]
lemma tracks (p:T!)(u:Train i)(ht:4 ≤ i)(s:ℝ):
     (Gift G h ∘L Larix G u ht C h s) p=(Larix G u ht C h s ∘L Gift G h) p:=by -- hp redundant
         funext j; apply Subtype.ext; change (Gift G h (Larix G u ht C h s p) j).val=_; rw [show ( (Larix G u ht C h s ∘L Gift G h) p j).val= _ from lavaX G h s u ht (Gift G h p) j]; fin_cases j; erw [tack]; exact (map_zero _).symm
         · erw [tack1 h _ 0 1 rfl,tack1 h p 0 1 rfl]; change armP _ h 0 1 (by decide) ((Larix G u ht C h s p) 0).val = _; rw [lavaX]; exact (lockC h 0 1 (by decide) (atlasF G u ht C) s _).symm
         erw [tack1 h _ 1 2 rfl,tack1 h p 1 2 rfl]; change armP _ h 1 2 (by decide) ((Larix G u ht C h s p) 1).val = _; rw [lavaX]; exact (lockC h 1 2 (by decide) (atlasF G u ht C) s _).symm
lemma Flick (v:Train r)(hv:4 ≤ r)(p:T!): Fallix G h K v hv (Gift G h p)= trellisA G h (Fallix G h K v hv p):=by
     rw [Fallix, ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.trans_apply,social]; apply congrArg; exact (tracks h p v hv (-(1/2:ℝ))).symm
end YM.OPE.Quit.Jac
