import YM.RG20.Scene
import YM.RG20.Swale
/-!
 # Advances and credit.K (MARK) at THE SAME through-discount S
 Head Ticket: NOT asserting from Burst which only reads weight, and not a
 transfer of membership in a different branch. Arithmetic steps credit adaptation
 from `YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Little` and `YM.Push.LOCAL_SPLITTING.Delay`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open YM.UVExtension Eyelet UVExtension.Rainfall Lacing Lacing.RoutesF Guard MergeProof
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace Edict
private def mon20 (x : ℝ) := Real.exp ((Real.log (Real.log x))^2)
private def gasRate (x : ℝ) := Real.exp (- ((mon20 x) ^ ((1 : ℝ)/5)))

private theorem power_delay (C : ℝ) (k : ℕ) : ∀ᶠ x : ℝ in atTop, C*x^k*Real.sqrt (gasRate x) ≤ 1 := by
  have h := Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1:ℝ),(h.comp h).eventually_ge_atTop 10, h.eventually_ge_atTop (2*((k:ℝ)+|C|)+1)] with x hx he hL
  dsimp only [Function.comp_apply] at he
  let l := Real.log x; let L := Real.log l
  have hp : 0 < l := Real.log_pos hx
  have hy : l^2 ≤ (mon20 x)^((1:ℝ)/5) := by
    rw [mon20,← Real.exp_mul, ← show Real.exp (2*Real.log (Real.log x)) = l^2 from (Real.exp_nat_mul L 2).trans (by simp [L, Real.exp_log hp])]
    apply Real.exp_le_exp.mpr; nlinarith
  rw [gasRate, Real.sqrt_eq_rpow,← Real.exp_mul, ← Real.exp_log (zero_lt_one.trans hx), ← Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hx),mul_assoc, ← Real.exp_add]
  calc
    _ ≤ Real.exp |C| * Real.exp (-|C|) := mul_le_mul ((le_abs_self _).trans (by linarith [Real.add_one_le_exp |C|])) (Real.exp_le_exp.mpr (by dsimp only [l] at hp hy; nlinarith [abs_nonneg C])) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]

private def width (x : ℝ) := ((((Nat.ceil ((Real.log x)^2))+(Nat.ceil ((Real.log x)^2))+1)^4 : ℕ):ℝ)


lemma knotBills (k : ℕ) : ∀ᶠ x : ℝ in atTop, width x * glyph x ≤ (x^k)⁻¹/2:=by
  filter_upwards [power_delay (2*5^4) (8+k), eventually_gt_atTop (1:ℝ)] with x hh hx
  have hL:= Real.log_pos hx; have hp:= zero_lt_one.trans hx
  have hC : ((Nat.ceil ((Real.log x)^2)):ℝ) ≤ 2*x^2 := by
    nlinarith [Real.log_le_sub_one_of_pos hp,Nat.ceil_lt_add_one (sq_nonneg (Real.log x))]
  have he:width x ≤ (5*x^2)^4:=by unfold width; push_cast; exact pow_le_pow_left₀ (by positivity) (by nlinarith : _+_+1 ≤ 5*x^2) 4
  refine (mul_le_mul_of_nonneg_right he (glyphpos _).le).trans ?_; rw [le_div_iff₀ (by norm_num : (0:ℝ)<2),← one_div,le_div_iff₀ (pow_pos hp k)] -- maybe le_inv_iff? 
  change 2*5^4*x^(8+k)*glyph x ≤ 1 at hh; rw [pow_add] at hh
  nlinarith only [hh]
lemma power20 (k : ℕ) : ∀ᶠ x : ℝ in atTop, glyph x ≤ (x^k)⁻¹/2:=by
  filter_upwards [power_delay 2 k,eventually_gt_atTop (0:ℝ)] with x hh hx
  rw [le_div_iff₀ (by norm_num : (0:ℝ)<2),← one_div,le_div_iff₀ (pow_pos hx k)]
  change 2*x^k*glyph x ≤ 1 at hh; linarith only [hh]
lemma hits_paid {G:Gauge}(h:G.Simple)(L:Levels G)(t:ℕ) : ∀ᶠ i in atTop,
     Push.Local.hitWidth (L.budget i) * Real.sqrt (L.clock.forcedAllowance i) ≤ ((L.clock.hatBeta i)^t)⁻¹/2 ∧
     Real.sqrt (L.clock.forcedAllowance (i+1)) ≤ ((L.clock.hatBeta i)^t)⁻¹/2:=by
     have he := Next.Rank.Station.hat_rate L h
     filter_upwards [he.eventually (knotBills t),(he.comp (show Tendsto (fun i:ℕ=>i+1) atTop atTop from tendsto_atTop_mono (f:=fun x=>x) (fun _=> Nat.le_succ _) tendsto_id)).eventually (power20 t)] with i hi hi'
     refine ⟨hi, le_trans (show _ ≤ ((L.clock.hatBeta (i+1))^t)⁻¹/2 from hi') ?_⟩
     refine div_le_div_of_nonneg_right (inv_anti₀ (pow_pos (zero_lt_one.trans (L.fits.delayed _)) _) (pow_le_pow_left₀ (zero_lt_one.trans (L.fits.delayed _)).le ?_ _)) zero_le_two
     exact YM.RG20.Loan.climbs (hG:=h) L (Nat.le_succ _)
-- DECAL
variable {G:Gauge} {P:Teller G} {L:Side}
private lemma rate_cash (Q:ConnectedActivityE6.Target G P)(d b : ℕ)(η σ:ℝ)(ht:0<η) (hs:0<σ) :
    ∀ᶠ x in atTop, ∀ (c:Side)(R:Rep G c)(S:Cloud R),let m:= R.p.mass S.live.crest S.live.weight; let k:= jewelDebt S.live Q L x;(glyph x)⁻¹*((L.val:ℝ)^d*(k+k)*straw σ L G x) ≤ ((x^b)⁻¹/2)*(η*m):=by
   let A:ℝ:= L.val^d -- type coercion! change
   have he : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):=by
     refine Rate.congr Rate.power ((Delay.shift_pos G L).mono fun x hx=>?_); exact (Real.rpow_neg hx.le Q.rate).symm
   have hh:= (((he.mul (efferv (G:=G) hs (Q.rate-↑b-1))).mul_left (L:=L) (4* ((L.val:ℝ)^d))).mul (Rate.hat.pow b)); have hσ:=hh.below (by linarith) η ht
   filter_upwards [Delay.shift_pos G L,hσ,eventually_gt_atTop (0:ℝ)] with x hy hh hr c R S' m D
   let e:=Real.exp (-Q.ε*coverNumber R.p.B S'.live.crest); let w:=m*e; let g:=Q.goal L x; have hp : e≤1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (by positivity))
   let y:= betaF G x L; have hf:0≤ m:= (S'.live.profit).trans (R.p.loMass _ _ S'.live.profit); have hg:0<g:= Real.rpow_pos_of_pos hy _; have hF:0≤w:=mul_nonneg hf (Real.exp_pos _).le
   have hw: w ≤ m:= mul_le_of_le_one_right hf hp
   let c' := (glyph x)⁻¹; let s:= straw σ L G x; let ℓ:=(L.val:ℝ)^d; have hc':0<c':= inv_pos.mpr (glyphpos x); have hS:0≤ s:=mul_nonneg zero_le_two (Real.exp_pos _).le
   have hm:= (le_abs_self _).trans hh; change 4*ℓ*(g⁻¹* (c' * s))*y^b ≤ η at hm
   have hz:x ≤ y:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
   have hb':4*ℓ*(g⁻¹* (c' * s))*x^b ≤ η:=(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hz b) (by unfold ℓ; positivity)).trans hm
   have hk':4*ℓ*(g⁻¹*(c'*s)) ≤ (x^b)⁻¹ * η:= ((le_div_iff₀ (pow_pos hr b)).mpr hb').trans_eq (by rw [div_eq_mul_inv, mul_comm])
   change c'*(ℓ*(w/g+w/g)*s) ≤ _; rw [div_eq_mul_inv]; linarith only [(mul_le_mul hk' hw hF (mul_nonneg (inv_nonneg.mpr (pow_pos hr b).le) ht.le))]

open Daisy.Charity.RG12
-- coin pays FULL per panel. Fixed-length fiat. Ess pairing with ANY decal in prior reports

def promise (Q:ConnectedActivityE6.Target G P) (L:Side) (μ:ℝ)(D:RG.Stage)(i:ℕ)(x:ℝ):Prop:=
    ∀ d≤ i,∀ b≤ i,∀ (c:Side)(R: Rep G c) (S:Cloud R),let m:=R.p.mass S.live.crest S.live.weight; let k:=jewelDebt S.live Q L x;
       (Blush.glyph x)⁻¹*((L.val:ℝ)^d*(k+k)*straw μ L G x) ≤ ((x^b)⁻¹/2)*(coinFee G D d L*m)
def ribbon20 (G:Gauge) : Decal G where
    rub _ Q _ L _ μ _ h i x := promise Q L μ h i x
    good _ Q _ :=by
       refine ⟨0,fun L _ W μ o h i _ _ hμ=>?_⟩
       filter_upwards [(Finset.range (i+1)).eventually_all.mpr (fun d _=>(Finset.range (i+1)).eventually_all.mpr (fun b _=> rate_cash Q d b (coinFee G h d L) μ (coin_pos ..) hμ (L:=L)))] with x hx
       exact fun d hd b hb=> hx d (mem_range.mpr (Nat.lt_succ_of_le hd)) b (mem_range.mpr (Nat.lt_succ_of_le hb))
end Edict
end YM.PhysicalNext.Repeat.Graces
