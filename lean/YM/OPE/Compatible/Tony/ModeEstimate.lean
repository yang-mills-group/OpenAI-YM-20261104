import YM.OPE.Compatible.Tony.Cime
import YM.OPE.Compatible.Juniper.Bike
/-!
# Big-support playoff.Circle prerequisites. Mark from X.Wall.wallet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
namespace Sleeve
-- Reel coordinates for photon from Physical.Mark Ear Stamp.
local notation "D!"=> Bid.Dir G n
local notation "Z!"=> Shade G
lemma spiritSp (x:D!):‖spool G n x‖ ≤ ‖x‖:=by refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>?_ ); obtain ⟨a,b,c⟩:=i; change ‖x (arkE (a,b)) c‖≤ _; exact (PiLp.norm_apply_le (x _) _).trans (norm_le_pi_norm ..)
variable {τ:Phase→ℕ}(i:Phase)(P:solar G d τ)
lemma ballStamp (p: Page (Shade G) k)(x y:D!)(hx:stamp p≤ m)(he:BlurD G (bark (m+1)) n x= BlurD G (bark (m+1)) n y):render 0 p (fun _=> spool G n x)=render 0 p (fun _=> spool G n y):=by
        refine prod_congr rfl fun i _=>?_ ; let j:=p i; let a: Edge Cover:=(j.1,j.2.1); have hh : size j.1 ≤ stamp p:=by rw [perimeter]; exact (single_le_sum (s:=Finset.univ) (f:=fun i=> size (p i).1) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans (Nat.le_add_left ..)
        have hp(p:Cover) (h:size p ≤ m):p∈Lattice.box m:=by
              have he(i:Axis): (p i).natAbs ≤ m:= ((single_le_sum (s:=univ) (f:=fun i=>(p i).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i))).trans h; rw[box_test]; constructor<;>intro i<;>specialize he i<;>omega
        have hy:=hp _ (hh.trans hx); let q:↥(bark (m+1)):= ⟨a,(cross_def _).mpr ⟨taller (Nat.le_succ _) hy,(up a.1 a.2 hy).1⟩⟩; rw [zero_add]; let H:=congr_fun he q; rw[echoP,echoP] at H; exact congr_arg (fun x:G.Color=>x j.2.2) H
lemma tonerS (hp:Spells.coveredM (Goan P) m)(x y:D!)(hv:BlurD G (bark (m+1)) n x=BlurD G (bark (m+1)) n y):mind P.val n 0 x=mind P.val n 0 y:=by
       let M:=spread G d τ P.val; have he(t:Phase): Flair (M t) (d+t.val) (spool G n x) 0= Flair (M t) (d+t.val) (spool G n y) 0:=by
              apply sum_congr rfl; intro i _; unfold Flume.Script.value scribe; refine tsum_congr fun j=>?_ ; by_cases ht:M t i j=0; rw [ht,zero_mul,zero_mul]; exact congr_arg _ (ballStamp j x y (hp _ _ j ht) hv)
       exact JetS.eta _ _ (he 0) (he 1) (he 2)
lemma topP (p:Script (Shade G) k)(h: Summable p) : Tall (fun x: D!=> Flume.Script.value 0 p (spool G n x)) k :=by
       let f:= (orchestra p (0:Site n)).compContinuousLinearMap (fun _=>(spool G n).toContinuousLinearMap); rw [show (fun x: D!=> Flume.Script.value 0 p (spool G n x))=Tensor.diagonal f from funext fun x=> (instruments p h ..).tsum_eq]; exact Tall.loan f le_rfl
lemma tBody (t:Phase): Tall (fun x:D!=> (mind P.val n 0 x).seq t.val) (d+t.val):=by
        let Y:=spread G d τ P.val; let u(i:ℕ)(x:D!):= Flume.Script.value 0 (Y t i) (spool G n x); let J:= range (d+t.val+1); have hp:= (resin P.val (m:=0) (fun _=> Nat.zero_le _)) t; rw [show (fun x:D! => (mind P.val n 0 x).seq t.val)=∑ i∈J,u i from ?_ ]; rotate_left; · funext i; exact (vein_i ..).trans (Finset.sum_apply i J u|>.symm)
        refine Tall.sums J u (fun i hi=> (topP _ (hp.bound _ i)).mono (by have h:=mem_range.mp hi;omega))
lemma F_single {i':ℕ}{x':ℝ} {p:Script (Shade G) i'} (hc:soot 0 p x') (x:Bid.Dir G n)(hx:‖x‖≤ 1): ‖Flume.Script.value 0 p (spool _ _ x)‖≤ x':=by
       have ht:=hem hc (0:Site n) (spool G n x); apply ht.trans; exact mul_le_of_le_one_right (Sack.coins hc) (pow_le_one₀ (norm_nonneg _) ((spiritSp x).trans hx))
lemma TBounds (t: Phase)(x:D!)(hx:‖x‖≤1): ‖(mind P.val n 0 x).seq t.val‖≤ ↑(d+t.val+1) * ‖P‖:=by
       let U:=Goan P; let v:=t.val; unfold mind; rw [vein_i]; refine (norm_sum_le ..).trans ((sum_le_sum (fun i hi=>F_single ((resin P.val (m:=0) (fun _=> Nat.zero_le _ ) t).2 i) x hx )).trans_eq ?_ ); rw[sum_const,card_range,nsmul_eq_mul]; rfl
end Sleeve
end YM.OPE.Merchant
