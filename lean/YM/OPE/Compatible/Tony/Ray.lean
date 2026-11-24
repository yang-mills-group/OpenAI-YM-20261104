import YM.OPE.Compatible.Tony.Hob
/-!
# Arc δ Mercator, declare Work.Core.Health body
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
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
section
variable (G)(n:Side)
noncomputable def kerS : Bid.Dir G n ≃ₗ[ℝ] Bid.Dir G n where
       toFun v i:= costume i.1 • v i
       invFun v i:= (costume i.1)⁻¹ • v i
       map_add' v w:=funext fun _=>smul_add ..
       map_smul' t v:=funext fun i=> smul_comm (costume i.1) t (v i)
       left_inv v:=funext fun i=> by dsimp only; rw [inv_smul_smul₀ (tensile _|>.ne')]
       right_inv v:=funext fun i=> by dsimp only; rw[smul_inv_smul₀ (tensile _|>.ne')]
noncomputable abbrev tellerT : Bid.Dir G n≃L[ℝ] Bid.Dir G n:= (kerS G n).toContinuousLinearEquiv
noncomputable def sillM (b:ℕ): Bid.Dir G n→L[ℝ] Bid.Dir G n:= ContinuousLinearMap.pi fun x=> if pdist x.1 < b then ContinuousLinearMap.proj x else 0
end
noncomputable def Roster (x:Bid.Dir G n):ℝ:= ‖(tellerT G n).symm x‖
lemma ros (x:Bid.Dir G n):0 ≤ Roster x:=norm_nonneg _
variable {c:ℝ}
lemma rentE (x:Bid.Dir G n)(u:Body 1 n): ‖x u‖≤costume u.1 * Roster x:=by
       let y:=(tellerT G n).symm x; nth_rw 1 [← (tellerT G n).apply_symm_apply x]; change ‖costume _ • y u‖≤_; rw [norm_smul,Real.norm_of_nonneg (tensile _|>.le)]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) (tensile _|>.le)
lemma receiveE (x:Bid.Dir G n)(t:ℝ)(he:0 ≤ t)(h:∀ i, ‖x i‖ ≤ costume i.1*t):Roster x ≤ t:=by
        refine (pi_norm_le_iff_of_nonneg he).2 fun j=>?_ ; change ‖(costume j.1)⁻¹ • x j‖≤_; rw [norm_smul, norm_inv,Real.norm_of_nonneg (tensile _|>.le)]; exact (mul_le_mul_of_nonneg_left (h j) (inv_nonneg.mpr (tensile _|>.le))).trans_eq (inv_mul_cancel_left₀ (tensile _|>.ne') _)
lemma herm (x:D!)(t:ℝ):Roster (t • x)=‖t‖*Roster x:=by unfold Roster; rw [map_smul,norm_smul]
lemma spice (x:Bid.Dir G n):Roster x ≤ ‖x‖:= receiveE x _ (norm_nonneg _) fun i=> (norm_le_pi_norm x i).trans (le_mul_of_one_le_left (norm_nonneg _) (privilege _))
lemma reveal (x:D!)(v:Body 1 n)(h:pdist v.1<b): sillM G n b x v=x v:=by unfold sillM; rw[ContinuousLinearMap.pi_apply, if_pos h]; rfl
lemma fade (x:D!)(v:Body 1 n)(h:b ≤ pdist v.1): sillM G n b x v=0:=by unfold sillM;rw [ContinuousLinearMap.pi_apply, if_neg h.not_gt]; rfl
lemma shrink (x:D!)(b:ℕ): Roster (sillM G n b x) ≤ Roster x:=by
       refine receiveE _ _ (ros x) fun i=>?_ ; by_cases h:pdist i.1 < b; rw[reveal x _ h]; exact rentE ..; rw [fade x _ (not_lt.mp h),norm_zero]; exact mul_nonneg (tensile _|>.le) (ros _)
lemma spoolE (x: Bid.Dir G n)(hx:Roster x ≤ c): Revenue c (spool G n x):=by
       constructor; rintro ⟨z,a,t⟩; let i:=arkE (z,a); change ‖x i t‖ ≤ c*costume z; apply (PiLp.norm_apply_le (x i) _).trans; exact ((rentE x i).trans (mul_le_mul_of_nonneg_left hx (tensile _|>.le))).trans_eq (mul_comm ..)
lemma shiftM (x:Bid.Dir G n)(b:ℕ): choir b (spool G n x) (spool G n (sillM G n (b+1) x)):=by constructor; rintro ⟨v,i,j⟩ hi; change x (arkE (v,i)) j=(sillM _ _ _ x (arkE (v,i))) j; rw [reveal _ _ (Nat.lt_succ_of_le hi)]
-- Root Energy
lemma BudgetV (x:Edge Cover)(i:G.ColorIndex): BoundsE (spool G n (functorE 0 x i)) (Moor x n).1 1:=by
       rw [topHere]; constructor
       · intro j hp; have hz:j≠ bench n 0 x i:=by intro h; apply hp; rw[h]; change 0+_=wrap n x.1; rw [zero_add]
         simp [deltaH,hz]
       intro j; unfold deltaH; by_cases h:j=bench n 0 x i; rw[h];simp; simp[h]
end YM.OPE.Merchant
