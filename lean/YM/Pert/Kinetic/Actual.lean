import YM.Pert.Kinetic.Polynomial
import YM.Pert.Spatial.CrowdPay
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {G:Gauge} (C:Family G) (hG:G.Simple)
include hG
local notation "A" => C.path.levels
local notation "P" => (A).clock
lemma paid_tail (h : YM.MergeProof.Ribbons.Plenty C) :
    ∀ᶠ i : ℕ in atTop, ∀ N p, (Quotes ((A).budget i) ((A).params i).width ((A).params i).paths ((P).loopCap i) ((P).allowance i) (2*(P).hatBeta i)) ∧ (C.path.Conv N p i → |(C.path.rep N p i).beta| ≤ 2*(P).hatBeta i) := by
   have hmon : ∀ᶠ i in atTop, (A).clock.monitor i ≤ (A).clock.hatBeta i := by
      filter_upwards [(Next.Rank.Station.hat_rate A hG).eventually (Vac.Numbers.cost 1 1 one_pos)] with i hi; simpa [Vac.Numbers.P, Calendar.monitor] using hi
   have hB := YM.MergeProof.Ribbons.coverGrowth C hG
   let F:=(A).budget
   have he:∀ᶠ i:ℕ in atTop,(F i).supportExponent⁻¹ ≤ (P).hatBeta i := by
      filter_upwards [(Next.Rank.Station.hat_rate A hG).eventually_ge_atTop (((A).params 0).supportExponent)⁻¹] with i hi
      change ((A).params i).supportExponent⁻¹ ≤ _;exact (inv_anti₀ ((A).params 0).price_pos ((A).fits.deepExp (Nat.zero_le _))).trans hi
   have hPath(m) : max ((A).params (m+1)).paths (((A).params (m+1)).width)⁻¹ ≤ ((A).S.block m |>.val : ℝ) := by
     let x :=(A).params (m+1); let j:= ((P).J (m+1):ℝ); let v:ℝ:= ((A).S.block m).val
     have hj : 1 ≤ j:= by dsimp only [j];exact_mod_cast (show 1≤(P).J (m+1) from (by linarith only [(P).adm (m+1)]))
     have h := (A).fits.logCost m; have hr : Real.log v ≥ 0:=Real.log_nonneg (by dsimp only [v];exact_mod_cast ((A).S.block m).pos)
     have hx₁:=x.width_pos;have hx₂:=x.paths_pos;have hx₃:=x.columns_ge;have hx₄:=x.price_pos;have hx₅:=x.clip.radius_pos
     let t:=1+x.paths+x.width⁻¹+x.columns+x.clip.relaxation+x.supportExponent
     change Real.log t / Real.log v ≤ (j^2)⁻¹ at h
     apply le_trans (max_le ?_ ?_) ?_
     swap; exact show x.paths≤t by unfold t; linarith only [hx₃,hx₄,hx₅,hx₁,hx₂,inv_pos.mpr hx₁]
     · exact show x.width⁻¹≤t by unfold t; linarith only [hx₂,hx₃,hx₄,hx₅]
     apply (Real.log_le_log_iff (show 0<t by positivity) (by positivity)).mp
     have hL := (A).S.block_large m
     have hy : (j^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (by nlinarith)
     refine le_trans ?_ (mul_le_of_le_one_left hr hy)
     apply (div_le_iff₀ ?_).1 h
     apply Real.log_pos
     unfold v; exact_mod_cast (show (1:ℕ) < ((A).S.block m).val from by omega)
   filter_upwards [hmon, he, hB.eventually_le_const (by norm_num : (0:ℝ) < 1), eventually_gt_atTop 0] with i hM he hB ht N p
   let s:=(P).hatBeta i
   have hs:0<s:=zero_lt_one.trans ((A).fits.delayed i)
   let v : ℝ:= ((A).S.block (i-1)).val
   have hx : max ((A).params i).paths (((A).params i).width)⁻¹ ≤ v := Nat.sub_add_cancel ht ▸ hPath (i-1)
   have hℓ:=h i; change ((F i).supportExponent+1)*v^4 ≤ Real.sqrt s at hℓ
   have hv : 1≤v:= by unfold v;exact_mod_cast ((A).S.block (i-1)).pos
   have hk : 1 ≤ s:=((A).fits.delayed i).le
   have hv' : v ≤ s := by
      have hpow:=pow_le_pow_right₀ hv (show 1≤4 by decide)
      nlinarith only [hv,hk,hℓ,mul_le_mul_of_nonneg_right (show (1:ℝ)≤(F i).supportExponent+1 by linarith only [(F i).exponent_pos]) (pow_nonneg (zero_le_one.trans hv) 4),hpow,Real.sqrt_nonneg s,Real.sq_sqrt hs.le]
   have hC0 : (((A).budget i).B:ℝ) ≤ s := by
      change _ / (P).hatBeta i ≤ 1 at hB
      have hz:=freq_le (s:=1+(((A).budget i).B:ℝ)) (by linarith) 1 8 (by decide); rw [pow_one] at hz
      have hB := (div_le_iff₀ hs).1 hB; linarith
   have hMon : 1 ≤ (P).monitor i:= Real.one_le_exp (sq_nonneg _)
   refine ⟨⟨by linarith only [hk],?_, ((le_max_right ..).trans hx).trans (by linarith), ?_,?_,?_,?_, by linarith only [hC0,hs], by linarith only [he,hs], ?_⟩,?_⟩ -- second slot paths positivity mismatched order
   · exact ((A).params i).width_pos
   · rw [abs_of_pos ((A).params i).paths_pos]; exact ((le_max_left ..).trans hx).trans (by linarith)
   · refine mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hMon ?_).trans (le_trans (Real.rpow_one ..).le hM)) zero_le_two;refine ((A).fits.thetaRange i).2.trans ?_; exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ (A).clock.J i from (by linarith only [(A).clock.adm i])))
   · unfold Calendar.allowance; 
     calc _ ≤ 1 := Real.rpow_le_one (by unfold Calendar.hatCoupling; positivity) (by unfold Calendar.hatCoupling; exact (inv_le_one₀ (Real.sqrt_pos.mpr hs)).2 (Real.le_sqrt_of_sq_le (by norm_num [hk]))) (by norm_num)
          _ ≤ _ := by linarith
   · unfold Calendar.allowance Calendar.hatCoupling; positivity
   · change ((A).clock.hatCoupling i*(P).monitor i)⁻¹ ≤ _; refine (inv_anti₀ (show 0<(P).hatCoupling i from by unfold Calendar.hatCoupling; positivity) (le_mul_of_one_le_right (by unfold Calendar.hatCoupling; positivity) hMon)).trans ?_; unfold s at *; unfold Calendar.hatCoupling; rw [inv_inv]; nlinarith only [hs,Real.sq_sqrt hs.le,hk]
   intro h; dsimp only [s] at hs; apply abs_le.mpr; exact ⟨by change _ ≤ C.path.β N p i; linarith only [h.band.1,hs], h.band.2⟩
end YM.Pert.Kinetic
