import YM.MatchingLedger.Periodical.Blister
import YM.MatchingLedger.Platform

/-!
# Purchases on the reference β margin. Bed and birth data stays native.

Keep future for each d and P(block ratio/kernel resolution), THEN use the given order-indexed
supply on a Schedule. Use realized beta, including all periods, in the requested windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Kiosk
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Periodical Books Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge}

-- pay with lower positive bound over all actual β in band
structure Span (b t : ℝ) : Prop where
  starts : 1≤ t
  minimum : b/2 ≤ t^2
  roof : t^2 ≤ 2*b

lemma infinite_meter : Tendsto Home.clock atTop atTop := tendsto_atTop_add_const_left atTop 1 (Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<8)))
lemma measure_exp {b : ℝ}(h:0<b) : Real.exp (Home.clock b)= Real.exp 1 * (8*b) := by unfold Home.clock; rw [Real.exp_add, Real.exp_log (by positivity)]
lemma Span.height {b t:ℝ} (h : Span b t) : t ≤ Real.exp (Home.clock b) := by
  obtain ⟨ht,he,hb⟩:= h; have hb':0<b:=by nlinarith only [hb, ht]
  rw [measure_exp hb']; exact (le_trans (le_self_pow₀ ht (by decide)) hb).trans (le_trans (by linarith only [hb']: 2*b ≤ 8*b) (le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity))))
lemma fund (u:ℝ)(d:ℕ) : ∀ᶠ b:ℝ in atTop, ∀ t:ℝ, Span b t → u* Home.clock b^d ≤ t := by
  let v:= |u|^2* (16 * Real.exp 1)
  filter_upwards [infinite_meter.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ), ((Real.tendsto_exp_div_pow_atTop (d+d)).comp infinite_meter).eventually_ge_atTop v] with b hb hp hV t hh
  let Z:= Home.clock b; have hz:0<Z:= zero_lt_one.trans_le hb
  have h : v * Z^(d+d) ≤ Real.exp Z := (le_div_iff₀ (pow_pos hz _)).mp hV
  rw [pow_add, measure_exp hp] at h
  let m:=(Home.clock b)^d
  have h' : (|u| * Z^d)^2 ≤ t^2:= by
    have he : |u|^2 * Z^(d+d) ≤ b/2 :=by
      rw [pow_add]; apply le_of_mul_le_mul_right _ (show 0<16*Real.exp 1 by positivity); unfold v at h; linarith only [h]
    rw [mul_pow,pow_two (a:= Z^d),← pow_add]; exact he.trans hh.minimum
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hz.le _)).trans ((sq_le_sq₀ (mul_nonneg (abs_nonneg _) (pow_nonneg hz.le _)) (zero_le_one.trans hh.starts)).mp h')
lemma fund_small (u:ℝ)(hu:0<u)(d : ℕ) : ∀ᶠ b:ℝ in atTop, ∀ t:ℝ, Span b t → t⁻¹*Home.clock b ^ d ≤ u:= by
  filter_upwards [fund u⁻¹ d] with b hb t ht; rw [inv_mul_le_iff₀ (zero_lt_one.trans_le ht.starts),mul_comm]; exact (inv_mul_le_iff₀ hu).mp (hb t ht)

lemma survives (u:ℝ)(_hu:0≤u)(i:ℕ) : ∀ᶠ b:ℝ in atTop, ∀ t:ℝ, Span b t → u*t^i * Real.exp (-(Home.clock b)^2) ≤ 1:= by
  filter_upwards [infinite_meter.eventually_ge_atTop 1, infinite_meter.eventually_ge_atTop u, infinite_meter.eventually_ge_atTop (i+1:ℝ)] with b hb hu' he t ht
  let q:= Home.clock b; have h0:1≤q:= hb
  have hu : u ≤ Real.exp q:= le_trans (show u≤q from hu') (le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp q))
  have hm : u*t^i ≤ Real.exp ((i+1:ℝ)*q):= by
    calc u*t^i ≤ Real.exp q * Real.exp q ^i := mul_le_mul hu (pow_le_pow_left₀ (zero_le_one.trans ht.starts) ht.height _) (pow_nonneg (zero_le_one.trans ht.starts) _) (Real.exp_pos _).le
         _ = _:=by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; ring
  rw [Real.exp_neg, ← div_eq_mul_inv,div_le_one (Real.exp_pos _)]
  apply hm.trans; apply Real.exp_monotone; rw [pow_two]; exact mul_le_mul_of_nonneg_right he (zero_le_one.trans h0)

lemma market_le (G : Gauge)(P : Patch){v : ℝ}(hp:0≤v) (d : ℕ) : ∃ u : ℝ, 0≤u ∧
    ∀ t : ℝ,1≤t→∀ Z:ℝ, 0≤Z → Z ≤ t → 1+proximity G P v t Z d ≤ u*t^(d+d+d+2):= by
  let a (i:ℕ):= gradientBill G P v (i+2) + gradientBill G P v i; let u:= ∑ i∈ Finset.range (d+1), a i
  let p:= park (belt P); let k:= 2*v*p; let c:= dawn G; let w : ℝ:= (d+d:ℕ)
  let m:= u+k+c+w
  have he (i:ℕ) : 0≤ a i:= add_nonneg (nonneg_bill G P hp _) (nonneg_bill G P hp _)
  have hu : 0 ≤ u:= Finset.sum_nonneg fun _ _=> he _; have hp0 : 0≤p:= park_nn ..
  have hh:0≤k:=by unfold k; positivity
  have hM:0≤ m:= add_nonneg (add_nonneg (add_nonneg hu hh) (dawn_pos G)) (Nat.cast_nonneg _)
  refine ⟨1+m,by linarith only [hM],fun t ht Z hz hZ=>?_⟩
  let T:= t^(d+d+2)
  have h0:1≤T:= one_le_pow₀ ht; have ht':0<t:= zero_lt_one.trans_le ht
  have h : readingsPrice G P v t Z d ≤ u*T:= by
    unfold readingsPrice u; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i hi
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (he i); apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz hZ _) (pow_nonneg ht'.le _)); unfold T; rw [← pow_add]; apply pow_le_pow_right₀ ht; have hi:=Finset.mem_range.mp hi; omega
  have hC : Periodical.cost P v t≤ k*T:= by
    have hx:t^2+1 ≤ 2*T:=by
      have ht':t^2≤ T:= pow_le_pow_right₀ ht (by omega); linarith only [ht',h0]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx hp) hp0).trans_eq (by unfold k; ring)
  have hw : readingsPrice G P v t Z d + Periodical.cost P v t + dawn G + w ≤ m*T:= by unfold m; rw [add_mul,add_mul,add_mul]; exact add_le_add (add_le_add (add_le_add h hC) (le_mul_of_one_le_right (dawn_pos G) h0)) (le_mul_of_one_le_right (by unfold w; positivity) h0)
  rw [add_mul, one_mul]; apply add_le_add (one_le_pow₀ ht); exact (mul_le_mul_of_nonneg_right hw (pow_nonneg ht'.le _)).trans_eq (by unfold T; rw [mul_assoc, ← pow_add]; congr 2; omega)

end YM.MatchingLedger.Kiosk
