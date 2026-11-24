import YM.OPE.Compatible.Waft.Aid
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
namespace PriceZ
variable {W L: Type}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{P:ChartRatio G}{u:ℝ}
lemma ray_norm (H:Even c.val)(X:Plot H)(y:Libra.Keys G X.Free): ‖spool G c (rayS H X G y)‖ ≤‖y‖:=by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; rintro ⟨x,i,a⟩; change ‖(cloak H (X.rollX y) (x,Exterior.coord i)) a‖ ≤‖y‖; apply (PiLp.norm_apply_le (cloak H (X.rollX y) (x,Exterior.coord i)) a).trans -- lemma wrong
      rw [cloak_at]; unfold hover; split <;> rename_i d
      all_goals rw [show X.rollX y _= X.cite 0 y _ from rfl]; unfold Stand.cite; split<;> first|simp|exact norm_le_pi_norm ..
      exact norm_le_pi_norm ..
open Flume.Page
lemma hem [Fintype I]{p:Script I r}{b:ℝ}(h:soot e p b)(x:Site n)(v:deck I n) : ‖Flume.Script.value x p v‖ ≤ b * ‖v‖^r:=by
     let f(i: Page I r):= p i*render x i fun _=>v; have ht:∀ (i:Page I r), ‖f i‖ ≤ ‖p i‖*‖v‖^r:=by
        intro i; have he: ‖render x i (fun _=>v)‖≤ ∏ _j:Fin r,‖v‖:=by unfold render; rw [norm_prod]; exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>norm_le_pi_norm ..)
        unfold f;rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); simpa using he
     have he:=h.mass (payer e); have hb: Summable fun i=>‖p i‖*‖v‖^r:=he.2.1.mul_right _; have hv:=Summable.of_nonneg_of_le (fun i=>norm_nonneg (f i)) ht hb; refine le_trans (norm_tsum_le_tsum_norm hv) ((hv.tsum_le_tsum ht hb).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right he.2.2 (by positivity)
lemma atF_norm (H:Even c.val)(X:Plot H)(y:Libra.Keys G X.Free)(p:Tower (Shade G) d τ)(x:Site c)(j:Phase): ‖((X.charted (cutφ H p x) y).seq j.val)‖ ≤ (d+3:ℕ)*‖p‖*(1+‖y‖)^(d+2):=by
     let V:= (spool G c) (rayS H X G y); let f:= spread G d τ p; change ‖(inkM f d x (rayS H X G y)).seq j.val‖ ≤ _; rw [Paver.vein_i]; apply (norm_sum_le ..).trans; let b:=‖p‖*(1+‖y‖)^(d+2); apply (Finset.sum_le_sum (g:=fun _=>b) (fun i hi=>?_)).trans; rw [Finset.sum_const, Finset.card_range,nsmul_eq_mul, mul_assoc]; apply mul_le_mul_of_nonneg_right _ (show 0 ≤ b from by unfold b; positivity); exact_mod_cast (show d+j.val+1 ≤ d+3 from by have ht:j.val<3:=j.isLt;omega)
     apply (hem (show soot 0 (f j i) ‖p‖ from (resin p (m:=0) (fun _=>Nat.zero_le _) j).2 i) x V).trans; unfold b; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply le_trans (pow_le_pow_left₀ (norm_nonneg _) ((ray_norm ..).trans (le_add_of_nonneg_left zero_le_one)) i); apply pow_le_pow_right₀ (by simp); have ht:j.val<3:= j.isLt; have hk: i< d+j.val+1:= Finset.mem_range.mp hi; omega
lemma earM (p:W→ solar G d τ) (X:W→Side)(H:∀ i,Even (X i).val)(A:∀ i,Plot (H i))(x:(i:W)→Site (X i)) :
    WindT X 0 (d+2) (fun i=>‖p i‖) (fun i=>Stand.charted (A i) (cutφ (H i) (p i).val (x i))):=by
         intro j; refine ⟨⟨(d+3:ℕ),by positivity,fun i v=>?_⟩,fun i=> Stand.composeWard (A i) (CloudH (H i) (p i) (x i)) j.val⟩; apply (atF_norm (H i) (A i) v (p i).val _ j).trans; unfold care; rw [pow_zero,one_mul];exact le_of_eq (mul_assoc ..)
lemma dualWorld (p q: W→ solar G d τ)(X:W→Side)(H:∀ i,Even (X i).val)(A:∀ i,Plot (H i))(x y:(i:W)→Site (X i)):
    WindT X 0 (d+2+(d+2)) (fun i=>‖p i‖* ‖q i‖) (fun i=>isolate (H i) (A i) (p i).val (q i).val (x i) (y i)):= (earM p X H A x).prod (earM q X H A y) (fun i=>norm_nonneg (p i))
end PriceZ
end YM.OPE.Quit
