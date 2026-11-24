import YM.RG12.Rail.Tracks
import YM.Next.SCHEDULE.Levels
import YM.RG12.Common.Short
/-! Apertures and rates charged in Rank bills. Calc for any C whose hierarchy has Slugg
 (we later finance that, it isn't implied by arbitrary calendar Fit). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Next.Rank.Value
open Glimmer Prayer Configuration Perch Marker Glyph Cells Market Read Dock Camp Beamer Normal
open Wall Maxwell CellsInt Real
open scoped Topology BigOperators Classical
variable {G:Gauge}(Y:Levels G)(h:G.Simple)
set_option quotPrecheck false
local notation "yK" k:max=> Y.clock.hatBeta k
local notation "pK" k:max=> Y.clock.monitor k
local notation "cost" x:max k:max=> bill x (yK k)
local notation "width" k:max=> ((Y.S.block k).val:ℝ)
def Slugg (Z:Levels G) : Prop := ∀ s:ℝ,0 < s → ∀ᶠ k:ℕ in atTop, ((Z.S.block k).val:ℝ) ≤ Perch.bill s (Z.clock.hatBeta k)
lemma width_three(k): (3:ℝ) ≤ width k:=by exact_mod_cast (Y.S.block_large k)
include h
lemma liftClock(k:ℕ): yK k ≤ yK (k+1):=by
   have hp: 1 < width k:= lt_of_lt_of_le (by norm_num) (width_three Y ..)
   unfold Calendar.hatBeta; rw [Schedule.scale_succ]; nlinarith only [Real.log_pos hp,Gauge.slopeConstant_pos h]

private lemma moderation (hs:Slugg Y) : ∀ᶠ k in atTop, yK (k+1) ≤ 2*yK k:=by
   have he:=hat_rate Y h
   have hx:Tendsto (fun k=>Perch.boil (yK k) * G.slopeConstant/(yK k)) atTop (𝓝 0):=by
      let f(x:ℝ):= Real.log (Real.log x)^2
      have ht : Tendsto (fun t:ℝ=> (f t/Real.log t)) atTop (𝓝 0):=by simpa only [one_mul,f,YM.Vac.Numbers.P] using (YM.Vac.Numbers.monitor 1)
      have hh:= (((ht.const_mul G.slopeConstant).mul (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero)).comp he)
      simp only [mul_zero,id_eq] at hh
      exact hh.congr' ((he.eventually_gt_atTop 1).mono (fun k hk=> by dsimp only [Function.comp_apply,id_eq]; unfold boil Perch.y f; field_simp [(Real.log_pos hk).ne']))
   filter_upwards [hx.eventually (ge_mem_nhds zero_lt_one), hs 1 zero_lt_one] with k hx hk
   have hL:= (zero_lt_one.trans (lt_of_lt_of_le (by norm_num) (width_three Y k)))
   have ht:= Real.log_le_log hL hk; rw [bill,Real.log_exp,mul_one] at ht
   have hm:=zero_lt_one.trans (Y.fits.delayed k)
   rw [div_le_one hm] at hx
   calc yK (k+1)= yK k + G.slopeConstant * Real.log (width k):= by unfold Calendar.hatBeta Levels.S; rw [Schedule.scale_succ]; ring
        _ ≤ _ :=by nlinarith only [mul_le_mul_of_nonneg_left ht (Gauge.slopeConstant_pos h).le,hx]

-- slowly-varying mag/amplification between adjacent k (even unbounded L, provided Slugg so hat drift linear on windows). 
lemma neighboring (hs:Slugg Y)(b:ℝ)(_hb:0<b): Tendsto (fun i=> mag Y b (i+1) /mag Y b i) atTop (𝓝 1) :=by
   let x(i):= yK i
   let Δ(i):ℝ:=boil (x (i+1))-boil (x i)
   have he:=hat_rate Y h
   have hp:=Real.tendsto_log_atTop.comp he
   -- increment y=loglog charged by log 2/logx
   have hQ : ∀ᶠ i in atTop, 0 ≤ Δ i ∧ Δ i ≤ 3*(log 2)*(Perch.y (x i))/log (x i):=by
      filter_upwards [moderation Y h hs, he.eventually_gt_atTop 1, (Perch.y_rate.comp he).eventually_ge_atTop 1,hp.eventually_ge_atTop (Real.log 2)] with i hh hz hk hx
      change 1 ≤ Perch.y (x i) at hk
      change log 2 ≤ log (x i) at hx
      let q:= x i;let r:=x (i+1);let a:= log q;let c:= log r
      have hA:0<a:=Real.log_pos hz; have hE:q ≤ r:=liftClock Y h _;have hR:0<q:=zero_lt_one.trans hz
      have hK:a ≤ c:=Real.log_le_log hR hE; have hC:=hA.trans_le hK
      have hT:c ≤ a+log 2:= by
         apply (Real.log_le_log (hR.trans_le hE) hh).trans_eq; rw [Real.log_mul (by norm_num) hR.ne',add_comm]
      have hρ: log a ≤ log c:=Real.log_le_log hA hK
      have hy:log c-log a ≤ log 2/a := by
         rw [← Real.log_div hC.ne' hA.ne']
         refine (Real.log_le_sub_one_of_pos (div_pos hC hA)).trans ?_; rw [sub_le_iff_le_add,div_le_iff₀ hA,add_mul,div_mul_cancel₀ _ hA.ne', one_mul]; rwa [add_comm] -- test
      change 0 ≤ log c^2-log a^2 ∧ _
      change 1 ≤ log a at hk
      have hh':log c≤2*log a:=by have he : log 2/a ≤ 1:=(div_le_one hA).mpr hx; linarith
      constructor; · have ht:= pow_le_pow_left₀ (zero_le_one.trans hk) hρ 2; linarith only [ht]
      change log c^2-log a^2 ≤ 3*log _ * log a/a
      calc log c^2-log a^2 = (log c-log a)*(log c+log a):=by ring
           _ ≤ (log 2/a)*(3*log a):=mul_le_mul hy (by linarith only [hh']) (by linarith) (by positivity)
           _ = 3*log _*log a/a:=by ring
   have hy:=Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hp
   have hK:Tendsto (fun i=> 3*(log 2)*(Perch.y (x i))/log (x i)) atTop (𝓝 0):=by
      have hx:=hy.const_mul (3*Real.log 2); rw [mul_zero] at hx; exact hx.congr (fun _=>by unfold Perch.y;dsimp only [Function.comp_apply,id_eq];ring)
   have hv:= squeeze_zero' (hQ.mono (fun i h=>h.1)) (hQ.mono (fun i h=>h.2)) hK
   simp_rw [mag_bill,bill,← Real.exp_sub,←sub_mul]
   have hq := Real.continuous_exp.continuousAt.tendsto.comp (hv.mul_const b)
   change Tendsto _ _ (𝓝 (exp (0*b))) at hq; rw [zero_mul,Real.exp_zero] at hq; exact hq
lemma bill_mono {b:ℝ}(hb:0 ≤ b) : ∀ᶠ i in atTop,cost b i ≤ cost b (i+1):=by
   filter_upwards [(Real.tendsto_log_atTop.comp (hat_rate Y h)).eventually_ge_atTop 1,(hat_rate Y h).eventually_gt_atTop 0] with i hi hh
   unfold bill boil Perch.y; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.log_nonneg hi) (Real.log_le_log (zero_lt_one.trans_le hi) (Real.log_le_log hh (liftClock Y h _))) _) hb)

lemma moderation_inclusive (hs:Slugg Y) : ∀ᶠ k in atTop, yK (k+1) ≤ 2*yK k:=moderation Y h hs
end YM.RG12.Rail
