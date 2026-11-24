import YM.MatchingLedger.Hessian.Fabric
import YM.MatchingLedger.Review.Clock

/-!
# Wall and strip payments from this realized calibration

Work on *any* rep k≤N (including top-target one-step use later). Do not require `Plenty`; do
require the actual C is invited in Pins, alongside any Couture/rolling bills. We pay via k−1 at
first for elasticity, while q^ powers displayed read k+1. The period and actual β then consume.
All `Eventually` estimates across levels simultaneously uniform at every period.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MatchingLedger.Spring.Fares
open Function Filter Lattice Wilson RG Precision Pressure Work.F03 Pert Pert.Kinetic Pins Home Kiosk
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (C:Family G)(hG:G.Simple)
local notation "L" => C.path.levels
local notation "V" => C.path.levels.clock
local notation "S" => C.S
local notation "W" => C.path.levels.params

def curb (q:ℝ):= (q^5)⁻¹

def tour (q:ℝ) := Nat.ceil ((2*q^7):ℝ) -- makes λtour/2 ≥ q²

include hG in
lemma ruler_money : Tendsto (fun i : ℕ=>(V).hatBeta (i+1)) atTop atTop:= (Review.Clock.hat_deep C hG).comp (Filter.tendsto_add_atTop_nat 1)
lemma curb_pos {q:ℝ}(he:0<q) : 0<curb q:=inv_pos.mpr (pow_pos he _)

include hG
lemma rises (i:ℕ) : (V).hatBeta i≤ (V).hatBeta (i+1):= by unfold Calendar.hatBeta; rw [Schedule.scale_succ]; apply add_le_add_right; apply mul_le_mul_of_nonneg_left _ (Gauge.slopeConstant_pos hG).le; apply le_add_of_nonneg_right; exact Real.log_nonneg (by exact_mod_cast ((S).block i).pos)
-- adapt `RG01.Vacuum.Flat.nextComparable`
lemma next : ∀ᶠ i in atTop, (V).hatBeta (i+1) ≤ 2*(V).hatBeta i := by
  let T:= L
  filter_upwards [T.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),T.S.divergent.eventually_gt_atTop 0] with i hi he
  have hS : Real.log (T.S.block i).val ≤ T.S.scale i := by
      have hh : Real.log (T.S.block i).val / T.S.scale i ≤ 1 := hi; simpa using (div_le_iff₀ he).mp hh
  have hg := Gauge.slopeConstant_pos hG
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]; nlinarith only [T.clock.bar_pos, mul_le_mul_of_nonneg_left hS hg.le]

omit hG
-- logCost, Hess.L priced after J,L, get a coarse number: compare `Kinetic.paid_tail.hPath`
lemma bracketL (k:ℕ): max ((W) (k+1)).paths ((W (k+1)).width)⁻¹≤ ((S).block k |>.val:ℝ):=by
  let X:=(W) (k+1); let v:ℝ:=((S).block k).val; let j:ℝ:=(V).J (k+1)
  let y : ℝ:= 1+X.paths+X.width⁻¹+X.columns+X.clip.relaxation+X.supportExponent
  have hv : 0 < Real.log v := Real.log_pos (by
    have hh : (3:ℝ) ≤ v:= by unfold v; exact_mod_cast (S).block_large k
    linarith)
  have hj: 1≤j := by unfold j; exact_mod_cast (show 1≤(V).J (k+1) from by linarith only [(V).adm (k+1)])
  have h: Real.log y ≤ Real.log v:= (div_le_one hv).mp (le_trans (show Real.log y / Real.log v ≤ (j^2)⁻¹ from (L).fits.logCost k) (inv_le_one_of_one_le₀ (one_le_pow₀ hj)))
  have hp := X.paths_pos; have hu := inv_pos.mpr X.width_pos; have hh := X.clip.radius_pos; have ht := X.columns_ge; have hs := X.price_pos
  refine le_trans (?_ : max X.paths X.width⁻¹ ≤ y) ((Real.log_le_log_iff (by unfold y; linarith) (by positivity : 0<v)).mp h); unfold y; rw [max_le_iff]; exact ⟨by linarith,by linarith⟩

variable (P : Prepared (invite G) C.path.levels)

include P
lemma future_payment {i : ℕ} (hi : 0 < i) : max (W i).paths ((W i).width)⁻¹ ≤ ((V).coverSize i : ℝ):= by
  cases i with
  | zero=>omega
  | succ i=>
    have h := (show earned ((V).op i 0).patch (V).kernel G ((V).hatBeta (i+1)) from P i 0 0 (Nat.zero_le _)).2.1
    apply (bracketL C i).trans
    apply Nat.cast_le.mpr; unfold macroR at h; change _ + 4*((S).block i).val≤ (V).coverSize (i+1) at h; omega

-- plenty not required (cost L_{i-1} from prepared). Keep photocopy of quote proof.
include hG P
lemma purchases : ∀ᶠ k:ℕ in atTop,
   Quotes ((L).budget k) ((W k).width) ((W k).paths) ((V).loopCap k) ((V).allowance k) (2*(V).hatBeta k) := by
   have hmon : ∀ᶠ i in atTop, (V).monitor i ≤ (V).hatBeta i := by
      filter_upwards [(Review.Clock.hat_deep C hG).eventually (Vac.Numbers.cost 1 1 one_pos)] with i hi; simpa [Vac.Numbers.P, Calendar.monitor] using hi
   have hB := YM.MergeProof.Ribbons.coverGrowth C hG
   let F:=(L).budget
   have he:∀ᶠ i:ℕ in atTop,(F i).supportExponent⁻¹ ≤ (V).hatBeta i := by
      filter_upwards [(Next.Rank.Station.hat_rate L hG).eventually_ge_atTop (((W) 0).supportExponent)⁻¹] with i hi
      change ((W) i).supportExponent⁻¹ ≤ _;exact (inv_anti₀ ((W) 0).price_pos ((L).fits.deepExp (Nat.zero_le _))).trans hi
   filter_upwards [hmon, he, hB.eventually_le_const (by norm_num : (0:ℝ) < 1), eventually_gt_atTop 0] with i hM he hB ht
   let A:= L; let s:=(V).hatBeta i
   have hk : 1 ≤ s:=((L).fits.delayed i).le; have hs:0<s:=zero_lt_one.trans_le hk
   have hC0 : (((A).budget i).B:ℝ) ≤ s := by
      change _ / (V).hatBeta i ≤ 1 at hB
      have hz:=freq_le (s:=1+(((L).budget i).B:ℝ)) (by linarith) 1 8 (by decide); rw [pow_one] at hz
      have hB := (div_le_iff₀ hs).1 hB; linarith
   have hx : max (W i).paths ((W i).width)⁻¹ ≤ s := (future_payment C P ht).trans hC0
   have hMon : 1 ≤ (V).monitor i:= Real.one_le_exp (sq_nonneg _)
   refine ⟨by linarith only [hk], ((A).params i).width_pos, (le_max_right ..|>.trans hx).trans (by linarith), ?_,?_,?_,?_, by linarith only [hC0,hs], by linarith only [he,hs], ?_⟩
   · rw [abs_of_pos ((A).params i).paths_pos]; exact ((le_max_left ..).trans hx).trans (by linarith)
   · refine mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hMon ?_).trans (le_trans (Real.rpow_one ..).le hM)) zero_le_two;refine ((A).fits.thetaRange i).2.trans ?_; exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ (A).clock.J i from (by linarith only [(A).clock.adm i])))
   · unfold Calendar.allowance
     calc _ ≤ 1 := Real.rpow_le_one (by unfold Calendar.hatCoupling; positivity) (by unfold Calendar.hatCoupling; exact (inv_le_one₀ (Real.sqrt_pos.mpr hs)).2 (Real.le_sqrt_of_sq_le (by norm_num [hk]))) (by norm_num)
          _ ≤ _ := by linarith
   · unfold Calendar.allowance Calendar.hatCoupling; positivity
   change ((V).hatCoupling i*(V).monitor i)⁻¹ ≤ _; refine (inv_anti₀ (show 0<(V).hatCoupling i from by unfold Calendar.hatCoupling; positivity) (le_mul_of_one_le_right (by unfold Calendar.hatCoupling; positivity) hMon)).trans ?_; unfold s at *; unfold Calendar.hatCoupling; rw [inv_inv]; nlinarith only [hs,Real.sq_sqrt hs.le,hk]

omit P in
lemma cover_pay (i:ℕ): ((V).coverSize i:ℝ) ≤ 2*ruler C i^2:= by
    let b:=(V).hatBeta (i+1); let q:=Home.clock b
    have hh(k):= (L).fits.delayed k; have hb: 1≤b:= (hh (i+1)).le
    have h : (V).hatBeta i ≤ 8*b:= by linarith only [rises C hG i,hb]
    have he := Real.log_le_log (zero_lt_one.trans (hh i)) h
    have hy := Real.log_nonneg (hh i).le
    have hz: 1≤ q := by unfold q Home.clock; linarith only [he,hy]
    have hm : Real.log ((V).hatBeta i) ≤ q:= by unfold q Home.clock; linarith only [he]
    refine le_trans (Nat.ceil_lt_add_one (sq_nonneg _)).le ?_; exact (add_le_add_left (pow_le_pow_left₀ hy hm 2) _).trans (by change _≤2*q^2; nlinarith only [hz,one_le_pow₀ (n:=2) hz])
lemma compass_price : ∀ᶠ i:ℕ in atTop,
   let z:=curb (ruler C i); let b:=(L).budget i; 0<z ∧ z≤1 ∧ z≤ (W i).width ∧ z*(6*(b.B:ℝ)+2)≤ b.supportExponent/2 := by
  let e := ((L).budget 0).supportExponent
  filter_upwards [(Review.Clock.ruler_deep C hG).eventually_ge_atTop (2:ℝ), (Review.Clock.ruler_deep C hG).eventually_ge_atTop (32/e),eventually_gt_atTop 0] with i hq he hi
  dsimp only; let q:=ruler C i; have h : 1≤q:= show 1≤ruler C i by linarith
  have hp:=curb_pos (zero_lt_one.trans_le h)
  have he0: 0<e:= ((L).budget 0).exponent_pos
  have hE0 : e ≤ ((L).budget i).supportExponent := (L).fits.deepExp (Nat.zero_le _)
  let u:=(L).budget i; let w:=(W i).width
  have hx : (u.B:ℝ)≤2*q^2:= cover_pay C hG i
  have ht:q^5*q^0=q^5:= by rw [pow_zero,mul_one]
  have h₃ : 2*q^2≤q^3:= by rw [pow_succ' q 2]; exact mul_le_mul_of_nonneg_right (show 2≤q from hq) (sq_nonneg _)
  refine ⟨hp,inv_le_one_of_one_le₀ (one_le_pow₀ h),(inv_le_comm₀ (by exact pow_pos (zero_lt_one.trans_le h) 5) (W i).width_pos).2 ?_,?_⟩ -- want q^−5 ≤ w ↔ w^-1 ≤ ...
  · exact ((le_max_right ..).trans (future_payment C P hi) |>.trans hx).trans (h₃.trans (pow_le_pow_right₀ h (by decide)))
  have he':= (div_le_iff₀ he0).1 he
  refine (inv_mul_le_iff₀ (show 0<q^5 from by positivity)).2 ?_
  apply le_trans _ (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hE0 zero_le_two) (by positivity));
  have hh : 14*q^2 ≤ q^5*(e/2):= by
     apply le_trans (?_ : _ ≤ q^3*(e/2)) (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h (by decide)) (by positivity))
     nlinarith only [mul_le_mul_of_nonneg_left he' (sq_nonneg q),sq_nonneg q]
  apply le_trans _ hh; nlinarith only [hx,one_le_pow₀ (n:=2) h]
end YM.MatchingLedger.Spring.Fares
