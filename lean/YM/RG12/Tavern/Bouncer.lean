import YM.RG12.Tavern.Steward
/-! # Price the at-most log response and arbitrary frame conversion polynomial on Slugg -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Tavern
open Frames Alidade Function Filter Set Finset RG Lattice Rail Real
open Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}(Y:Levels G)(h:G.Simple)(b:ℝ)(hb:0<b)(N:ℕ)(hN:0<N)
local notation "χ"=>Y.clock.hatBeta
local notation:max "t!"=>torchR Y b N
set_option quotPrecheck false
local notation "W(" k ")"=>((Y.S.block k).val :ℝ)
include h hN hb
lemma block_dial (hs:Slugg Y):∀ᶠ k in atTop,
    1 ≤ t! k/t! (k+1) ∧ t! k/t! (k+1) ≤2*W(k) ∧ W(k) ≤ Y.clock.monitor k:=by
   have hT:=sitespec h hs hb N hN (Y:=Y)
   filter_upwards [hT.2,(tendsto_add_atTop_nat 1).eventually hT.2, Rail.bill_mono Y h hb.le, hs 1 zero_lt_one] with i H ht hB hx
   have hδ:= across_torch b N i hN (Y:=Y)
   rw [jumped_at] at hδ
   change drift Y b N (i+1)*(t! i/(t! (i+1))) = W(i)*(drift Y b N i)/(mag Y b (i+1)/mag Y b i) at hδ
   refine ⟨(one_le_div (hT.1 _)).mpr H.2.1,?_,?_⟩
   · have hm :1 ≤ mag Y b (i+1)/mag Y b i:=by rw [one_le_div (mag_pos ..)]; simp only [mag_bill];exact hB
     have he := mul_le_mul_of_nonneg_left H.1.2 (Nat.cast_nonneg (Y.S.block i).val (α:=ℝ))
     have hv := div_le_self (mul_nonneg (Nat.cast_nonneg (Y.S.block i).val (α:=ℝ)) (show 0 ≤ drift Y b N i from (drift_pos Y b N hN i).le)) hm
     have hy : 0 ≤ t! i/t! (i+1) := (div_pos (hT.1 i) (hT.1 _)).le
     have ht := le_mul_of_one_le_left hy ht.1.1
     linarith -- watch
   rw [fire_bill]; exact hx
lemma ratios (hs:Slugg Y)(d:ℕ)(K:ℝ):∀ᶠ k in atTop,
    let s:=t! k / t! (k+1);
    Real.log s ∈ Set.Icc 0 (2*Alidade.slice Y k) ∧ K*s^d ≤ epoch Y k^3:=by
   set c:= b
   let ε:=epoch Y
   have hT : χ=(fun i=>Y.clock.bar + G.slopeConstant*(ε i-1)* Real.log 3):=by
       ext x;change Y.clock.bar+G.slopeConstant*Y.S.scale x=_;unfold ε epoch; field_simp; ring
   let z:=(|K|+1)*(2:ℝ)^d * (Y.clock.bar + G.slopeConstant*Real.log 3)
   have he:= (epoch_late Y).eventually_ge_atTop z
   have hG(k):= year Y k
   have hf : ∀ᶠ k in atTop,Y.clock.monitor k ^ d ≤ Real.sqrt (χ k):=by
      -- ratio_throttle only C
      filter_upwards [(year_late Y h).eventually (YM.Vac.Numbers.cost (d:ℝ) (1/2) (by norm_num))] with i hi
      rw [Real.rpow_natCast,←Real.sqrt_eq_rpow] at hi; exact hi
   filter_upwards [he,hf,block_dial Y h b hb N hN hs] with k hk ht hx s
   constructor
   · refine ⟨Real.log_nonneg hx.1,(Real.log_le_log (zero_lt_one.trans_le hx.1) hx.2.1).trans ?_⟩
     have hp: (2:ℝ) ≤ W(k):= by linarith only [width_three Y k]
     have hl := Real.log_le_log (show (0:ℝ)<2 by norm_num) hp
     unfold Alidade.slice; rw [Real.log_mul (by norm_num) (by linarith only [hp])]; linarith
   have hv :1≤ε k:=begun Y k
   have hi :1 ≤ χ k:=delay Y k
   have ha :Real.sqrt (χ k) ≤ χ k:=by nlinarith only [Real.sq_sqrt (zero_le_one.trans hi),hi]
   let p:=Y.clock.bar;let q:=G.slopeConstant* Real.log 3
   have hp:p ≥ 0:=Y.clock.bar_pos.le; have hq:0 ≤ q:=mul_nonneg (Gauge.slopeConstant_pos h).le arc3.le
   have hr:χ k ≤ ε k*(p+q):=by rw [hT];change p+G.slopeConstant*(ε k-1)*Real.log 3 ≤ _; nlinarith [mul_le_mul_of_nonneg_right hv hp, arc3]
   have hs':s^d ≤2^d*Y.clock.monitor k^d:=(pow_le_pow_left₀ (zero_le_one.trans hx.1) (hx.2.1.trans (mul_le_mul_of_nonneg_left hx.2.2 zero_le_two)) _).trans_eq (mul_pow ..)
   calc _ ≤ (|K|+1)*(2^d*(ε k*(p+q))) := mul_le_mul ((le_abs_self _).trans (by linarith)) (hs'.trans (mul_le_mul_of_nonneg_left ((ht.trans ha).trans hr) (by positivity))) (pow_nonneg (zero_le_one.trans hx.1) _) (by positivity)
        _=z*ε k:=by unfold z p q; ring
        _ ≤ ε k ^3:= by apply (mul_le_mul_of_nonneg_right hk (zero_le_one.trans hv)).trans; nlinarith [le_self_pow₀ hv (show (3:ℕ)≠0 by norm_num),pow_le_pow_right₀ hv (show (2:ℕ)≤3 by norm_num)]
end YM.RG12.Tavern
