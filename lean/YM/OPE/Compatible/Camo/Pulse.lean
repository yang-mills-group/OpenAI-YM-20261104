import YM.OPE.Compatible.Crib.Lease
import YM.OPE.Compatible.Ice.Guru
/-! # compensated vertical-coarse natural-beta sensor reports. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set Finset
open scoped Topology BigOperators Classical ContDiff
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Spells Radial Stranded Crown
variable {V E:Type}{r s t c x C D:ℝ}{i j k:ℕ}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
section
variable (W:JetS E)(c:ℝ)
noncomputable abbrev Ebox : JetS E:= ⟨W.s,W.l,W.h+(c/2) • W.s⟩
lemma Ebulb (f:E→ℝ): Jpiece (Ebox W c) f= Jpiece W f + ⟨0,0,(c/2)*pointD W.s f W.s⟩:=by
       apply JetS.eta
       · simp [Jpiece]
       · simp [Jpiece]
       change fderiv ℝ f W.s (W.h+(c/2) • W.s)+_ = ((fderiv ℝ f W.s W.h)+_) + (c/2)*fderiv ℝ f W.s W.s; rw [_root_.map_add,_root_.map_smul,smul_eq_mul]; unfold Ebox; dsimp only; ring
lemma Cert (h:TagN W≤t):TagN (Ebox W c)≤(1+‖c/2‖)*t:=by
       have hz:‖W.s‖ ≤ t:= le_trans (le_trans (le_trans (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_right (norm_nonneg W.l))) (le_add_of_nonneg_right (norm_nonneg W.h))) h; have hx:= mul_le_mul_of_nonneg_left hz (norm_nonneg (c/2)); have ht:=norm_add_le W.h ((c/2) • W.s); rw[norm_smul] at ht; change 1+‖W.s‖+‖W.l‖+‖_‖≤_; unfold TagN at h; linarith only [ht,h,hx]
def rebate (c η ε C:ℝ):=(‖η-1-ε^2*(c/2)‖+ ‖η-1‖*(ε+ε^2))*C
private lemma credits (η:ℝ)(ε:ℝ): η • (W.atK ε)-(Ebox W c).atK ε=(η-1-ε^2*(c/2)) • W.s+(η-1) • (ε • W.l+ε^2 • W.h):=by
       unfold JetS.atK Ebox; simp only[smul_add,sub_smul,one_smul,mul_smul]; abel
lemma Coupon (η:ℝ)(h:TagN W≤ C)(x:E)(he:0≤t)(hp:‖x-W.atK t‖≤ r): ‖η • x- (Ebox W c).atK t‖ ≤ ‖η‖*r + rebate c η t C:=by
      apply (norm_sub_le_norm_sub_add_norm_sub _ (η • W.atK t) _).trans; rw [← smul_sub,norm_smul]; refine add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) ?_; rw [credits,rebate,add_mul]; apply (norm_add_le ..).trans; simp only [norm_smul]; apply add_le_add (mul_le_mul_of_nonneg_left _ (norm_nonneg _)); swap; · unfold TagN at h; linarith only [h,norm_nonneg W.l,norm_nonneg W.h]
      rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (norm_add_le ..).trans; rw [norm_smul_of_nonneg he,norm_smul_of_nonneg (sq_nonneg _),add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (by unfold TagN at h; linarith only[h,norm_nonneg W.s,norm_nonneg W.h]) he) (mul_le_mul_of_nonneg_left (by unfold TagN at h; linarith only [h,norm_nonneg W.s,norm_nonneg W.l]) (sq_nonneg _))
abbrev γX (x ε:ℝ):= (Nat.factorial 3:ℝ)*(3*x)^3*ε^3
lemma floorR (p:E→ℝ)(hp:Velvet p r 0)(w:E)(ht:0<t)(he:t≤1)(hx:TagN (Ebox W c)≤ C)(hy:‖w-(Ebox W c).atK t‖ ≤ D) : ‖p w - (Jpiece (Ebox W c) p).atK t‖ ≤ r*(D + γX C t):=by
       let v:=Ebox W c; have hz:0≤D:=(norm_nonneg _).trans hy; let x:=D/t^3; have hh:0 ≤ x:=div_nonneg hz (pow_nonneg ht.le _); have hk: D=x*t^3:=(div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')).symm; apply (Flare v x (TagN v+x) r hp.roll le_rfl hh hp.pos (fun i hi p _=>by simpa only[pow_zero,mul_one] using hp.seats i hi p) w t ht he (hy.trans_eq hk)).trans
       have hb:(3*TagN v)^3≤ (3*C)^3:=pow_le_pow_left₀ (mul_nonneg (by norm_num) (zero_le_one.trans (VatR v))) (mul_le_mul_of_nonneg_left hx (by norm_num)) _; unfold γX; exact ((mul_le_mul_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_left hb (mul_nonneg (by exact_mod_cast (Nat.zero_le _)) hp.pos)) _) (pow_nonneg ht.le _))).trans_eq (by rw [hk]; ring)
end
end YM.OPE.Cameo
