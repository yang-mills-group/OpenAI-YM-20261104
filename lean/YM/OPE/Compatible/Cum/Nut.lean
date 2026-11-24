import YM.OPE.Compatible.Cum.Pulse
/-!
# script off-camera ledger. Winding across H cold enough
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I:Type}{N:Side}[Fintype I] {n s t:ℕ} {d c b w:ℝ}{a D:Site N}
local notation "K"=> Flume.Script.Tab I N
local notation "Q"=> deck I N
private def lum (p:Page I (n+1))(a:Site N): K:=(a+wrap N (p 0).1,(p 0).2)
lemma riseC (M: Matrix K K ℝ)(i: Site N)(p: Script I (n+2))(x: Fin n→Q)(hc:soot s p b)(h:Cold i i M d s)(hd:0 ≤ d):
     grain N s * ‖routeTap M p x i‖ ≤ 3^s*d*b* ∏ j, ‖x j‖:=by
          have hp:=Tap_reads M p x i (sootS hc); let u(v:Page I (n+2)):= p v*M (lum v i) (lum (mort v) i)*render i (melt v) x; let z:= ∏ j, ‖x j‖; let k:= grain N s; let D:= 3^s*d; have hv:(∑' i,u i)=routeTap M p x i:=hp.tsum_eq; have hz:0≤z:=prod_nonneg fun _ _=>norm_nonneg _; rw [←hv]; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (show Summable u from hp.summable ).norm) (by unfold grain; positivity)).trans
          have hy:0 ≤ D*z := mul_nonneg (mul_nonneg (by positivity) hd) hz; have he(v: Page I (n+2)): k * ‖u v‖ ≤ D*z*(figure s v*‖p v‖):=by
                let a:=lum v i; let j:=lum (mort v) i; have hp : 1+separation a.1 i+ separation j.1 i ≤3*Page.stamp v:=by
                     have hi:separation a.1 i ≤ size (primary v):= roll_near i _; have ht:separation j.1 i ≤ size (primary (mort v)):= roll_near i _; have hp:= v.primary_size; have hx:= Page.primary_size (mort v); have hh:= notched v; have hz:1≤ stamp v:= notch_one _; omega
                have hM:k * ‖M a j‖≤ D*figure s v:=by apply (h a j).trans; unfold D; rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right _ hd; unfold StepN figure poise; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); exact_mod_cast hp
                have hW: ‖render i (melt v) x‖ ≤ z:=by unfold render; rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>norm_le_pi_norm ..)
                calc
                   _= k*‖M a j‖* ‖render i (melt v) x‖ * ‖p v‖:=by unfold u a j; simp only [norm_mul];ring
                   _≤_:=by apply (mul_le_mul_of_nonneg_right (mul_le_mul hM hW (norm_nonneg _) ((mul_nonneg (zero_le_one.trans (grain_b s)) (norm_nonneg _)).trans hM)) (norm_nonneg _)).trans_eq; ring
          rw [← tsum_mul_left]; apply ((hp.summable.norm.mul_left k).tsum_le_tsum he (hc.2.1.mul_left _)).trans; rw [tsum_mul_left]; apply (mul_le_mul_of_nonneg_left hc.2.2 hy).trans_eq; unfold D z;ring
lemma herdC (M:Matrix K K ℝ)(p:Script I (n+1))(q:Script I (t+1))(x:Fin n→Q)(y:Fin t→Q)(i j: Site N)(h:Cold i j M d s)(hd:0≤d)(hp:soot s p b)(hx: soot s q w):
    grain N s * ‖drawP M p q x y i j‖ ≤ (3:ℝ)^s*d*b*w*(∏ i,‖x i‖)*(∏ i,‖y i‖):=by
         have he:= wings (M) (sootS hp) (sootS hx) x y i j; let R:= Page I (n+1) × Page I (t+1); let f(v:R):=p v.1*q v.2 * M (lum v.1 i) (lum v.2 j)*render i (mort v.1) x*render j (mort v.2) y; let C:=∏ i, ‖x i‖; let D:=∏ i,‖y i‖; have hC:0 ≤ C:=prod_nonneg fun _ _=> norm_nonneg _; have hD:0 ≤ D:=prod_nonneg fun _ _=> norm_nonneg _; let a:=3^s*d; have ha:0 ≤ a*C*D:=by unfold a; positivity
         let g:=grain N s; let A (p':Page I (n+1)):= figure s p'*‖p p'‖; let B (q':Page I (t+1)):= figure s q'*‖q q'‖
         have hR:Summable f:=he.summable; rw [← show ∑' i,f i= _ from he.tsum_eq]; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hR.norm) (by unfold grain; positivity)).trans; have hh(v:R):g*‖f v‖ ≤ a*C*D*(A v.1* B v.2):=by
              let u:=lum v.1 i; let z:=lum v.2 j; have hw : 1+ separation u.1 i+ separation z.1 j ≤3* Page.stamp v.1 * Page.stamp v.2:=by
                   have hp:separation u.1 i≤ Page.stamp v.1:= (roll_near i (primary v.1)).trans v.1.primary_size; have hx:separation z.1 j≤ Page.stamp v.2:=(roll_near j (primary v.2)).trans v.2.primary_size; have hc:1≤ stamp v.1:= notch_one _; have hd:1 ≤ stamp v.2 := notch_one _; nlinarith
              have hp' : g*‖M u z‖ ≤ a * (figure s v.1* figure s v.2):=by apply (h u z).trans; unfold a; rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right _ hd; unfold StepN figure poise; rw [←mul_pow,←mul_pow]; apply pow_le_pow_left₀ (by positivity); exact_mod_cast (hw.trans_eq (mul_assoc ..))
              have hW {t:ℕ} (p:Page I t)(x: Fin t→Q)(i:Site N):‖render i p x‖ ≤ ∏ k,‖x k‖:=by unfold render; rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>norm_le_pi_norm ..)
              have hF:= mul_le_mul (hW (mort v.1) x i) (hW (mort v.2) y j) (norm_nonneg _) hC; have hk := mul_le_mul hp' hF (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((mul_nonneg ((zero_le_one.trans (grain_b s))) (norm_nonneg _)).trans hp')
              calc
                 _=(g*‖M u z‖ * (‖render i (mort v.1) x‖* ‖render j (mort v.2) y‖))* (‖p v.1‖*‖q v.2‖):=by unfold f u z; simp only [norm_mul];ring
                 _≤ _:=by apply (mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ ‖p v.1‖ * ‖q v.2‖)).trans_eq; unfold A B C D;ring
         have hS : Summable fun v:R=> A v.1*B v.2 := hp.2.1.mul_of_nonneg hx.2.1 hp.1 hx.1
         rw [← tsum_mul_left]; apply ((hR.norm.mul_left _).tsum_le_tsum hh (hS.mul_left _)).trans; rw [tsum_mul_left,hS.tsum_prod]; simp_rw [tsum_mul_left]; rw [tsum_mul_right]; apply (mul_le_mul_of_nonneg_left (mul_le_mul hp.2.2 hx.2.2 (tsum_nonneg hx.1) (Sack.coins hp)) ha).trans_eq; unfold a C D;ring
end YM.OPE.Libra.Shell
