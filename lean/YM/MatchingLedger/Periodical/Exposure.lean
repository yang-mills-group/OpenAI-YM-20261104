import YM.MatchingLedger.Periodical.Pulp

/-!
# Read everywhere, not only tiny chart

Post prices. Finite integral, forest cost on φ derivatives; all shadow paths/hard flags still
included in measure. Outside gate pay THIS factor of unrestricted t in pressure estimate next.
The incoming cost after iterating with any additional resampling step would have to be added
separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric
open MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices) (hB:S.patch.Branches S.kernel G)
    {A : ChartRatio G} (Y : Chip (Page G c)) {t Z : ℝ} (i : Needle F G)(k d : ℕ) (H : Budget G A (d+3))
variable (ht:1≤t)(hZ:1≤Z)(hY:‖Y‖≤ Z)
variable {R : Support c}
    (hr : t⁻¹*Z≤dial A) (hh:t⁻¹*Z ≤ H.space S.patch S.kernel)
    (p : Token (Needle F G))(hd : heft p≤d)(he:k≤d) (U : F.Slice G)
local notation "a" => (t⁻¹*Z)
local notation "ι" => Needle F G
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)
local notation "V" => edition F s A Y
local notation "M" => H.income S.patch S.kernel
local notation "ξ" => fieldTest (G:=G) F R
local notation "P" => notice F s Y i k (mark p) A t
local notation "E" => milled F s A (t⁻¹ • Y) t a R i (mark p)
local notation "J" => run F A t P

-- lead costs Z≤t on the schedule where these will be paid. for now keep both explicit

def readingsPrice (G : Gauge)(p : Patch)(v t Z : ℝ)(k:ℕ) := ∑ j∈ Finset.range (k+1),
  (gradientBill G p v (j+2)+gradientBill G p v j) * Z^(j+1) * t^(j+1)
def proximity (G : Gauge)(p : Patch)(v t Z : ℝ)(d:ℕ) :=
    (readingsPrice G p v t Z d + cost p v t + dawn G + (d+d:ℕ))*t^d
lemma price_ge (G : Gauge)(p : Patch){v t Z : ℝ}(hp:0≤t)(hv:0≤v)(hz:0≤Z)(d:ℕ):0≤readingsPrice G p v t Z d:= Finset.sum_nonneg (fun _ _=> mul_nonneg (mul_nonneg (add_nonneg (nonneg_bill G p hv _) (nonneg_bill G p hv _)) (pow_nonneg hz _)) (pow_nonneg hp _))
lemma prox_ge (G : Gauge)(p : Patch){v t Z : ℝ}(hp:0≤t)(hv:0≤v)(hz:0≤Z)(d:ℕ) : 0 ≤ proximity G p v t Z d:=by unfold proximity; positivity [dawn_pos G,cost_nn (t:=t) p hv,price_ge G p hp hv hz d]
include ht
lemma prime (X : Poly ι) (he:X.totalDegree ≤ d) : ‖run F A t X U‖ ≤ fare X * t^d:= read_bounded he (Finset.Subset.refl _) ht _
   (fun i _=> by rw [Pi.smul_apply, norm_smul_of_nonneg (zero_le_one.trans ht)]; exact mul_le_of_le_one_right (zero_le_one.trans ht) ((norm_le_pi_norm _ _).trans (crawl_all F A U)))
include hZ hB hY he H
lemma runs_out : ‖run F A t (readings F s Y i k A t) U‖≤ readingsPrice G S.patch M t Z d:= by
  let B(j):= (gradientBill G S.patch M (j+2)+gradientBill G S.patch M j); let g:=t⁻¹
  have hz: 0≤Z:= zero_le_one.trans hZ; have ht':0<t:=zero_lt_one.trans_le ht; have h0:1≤ M:= H.income_one ..
  have hu(j) :0≤ B j := add_nonneg (nonneg_bill G S.patch (zero_le_one.trans h0) _) (nonneg_bill G S.patch (zero_le_one.trans h0) _)
  let W(j:ℕ):= B j* Z^(j+1)*t^(j+1);
  have hw (j) : 0 ≤ W j:= mul_nonneg (mul_nonneg (hu j) (pow_nonneg hz _)) (pow_nonneg ht'.le _)
  have hv (j:ℕ) (hh:j≤k) : ‖g^j * run F A t (pderiv i (V j)) U‖≤ W j:=by
    have hd : ‖g^j‖≤1:=by rw [Real.norm_of_nonneg (show 0≤g^j by unfold g; positivity)]; exact pow_le_one₀ (inv_pos.mpr ht').le (inv_le_one_of_one_le₀ ht)
    rw [norm_mul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) hd); cases j with
    | zero=>
      have he:= Ticket F H Y i (tip_paid F s H hB H.nn (.inl i)) hZ hY
      apply le_trans (prime F (2-1) ht U _ he.degree)
      change _≤(B 0*Z^1)*t^1; have hp : gradientBill G S.patch M 2≤ B 0:= le_add_of_nonneg_right (nonneg_bill G S.patch (zero_le_one.trans h0) _)
      exact mul_le_mul_of_nonneg_right (he.limit.trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hz _))) (pow_nonneg ht'.le _)
    | succ j=>
      have h0 := slope_ticket F s hB Y H (show j+1+2≤d+3 from by omega) i (Nat.zero_lt_succ j) Z hZ hY
      apply le_trans (prime F (j+1+1) ht U _ h0.degree); exact mul_le_mul_of_nonneg_right h0.limit (pow_nonneg ht'.le _)
  unfold run; rw [current_entry]; simp_rw [_root_.map_sum,_root_.map_smul,smul_eq_mul]; apply (norm_sum_le ..).trans
  apply (Finset.sum_le_sum (g:= W) (fun i hi=> hv i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))).trans; unfold readingsPrice; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ he)) (fun i _ _=> hw i)
omit H he hB hY hZ
include hd
lemma current_word : ‖run F A t (mark p) U‖≤ t^d:= le_trans (prime F d ht U (mark p) ((mark_weight p).trans_le hd)) (by rw [fare_mark,one_mul])
lemma word_prime : ‖run F A t (pderiv i (mark p)) U‖≤ d*t^d:= le_trans (prime F d ht U _ ((total_pderiv_mark ..).trans (le_trans (Nat.sub_le ..) hd))) (mul_le_mul_of_nonneg_right ((fare_pderiv_mark ..).trans (Nat.cast_le.mpr hd)) (pow_nonneg (zero_le_one.trans ht) _))

include hZ hY he hr hh H hB
lemma bump_bill : ‖J U - E U‖≤ proximity G S.patch M t Z d:=by
  let f:= run F A t (mark p) U; let g:= run F A t (pderiv i (mark p)) U
  let q:= run F A t (readings F s Y i k A t) U
  have hp: 0 < t:= zero_lt_one.trans_le ht; have ha:0<Z:=zero_lt_one.trans_le hZ; have hC: 0<a:= by positivity
  have hf := current_word F (A:=A) d ht p hd U; have hg:= word_prime F (A:=A) i d ht p hd U
  have h :0 ≤ M:=zero_le_one.trans (H.income_one ..)
  let v:= readingsPrice G S.patch M t Z d
  have hv:0≤v:=price_ge G S.patch hp.le h ha.le d
  have hx: ‖q‖≤v:= runs_out F s hB Y i k d H ht hZ hY he U
  have hJ : ‖J U‖≤ (v+d)* t^d:=by
    rw [show J U=q*f - g from by unfold run notice f g q; rw [_root_.map_sub,read_mul]; rfl,add_mul]
    exact (norm_sub_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul hx hf (norm_nonneg _) hv)) hg)
  let M₁:= cost S.patch M t; let Y':= t⁻¹ • Y
  have hZ': 0≤ dawn G:= dawn_pos G; have hc: 0≤ M₁:=cost_nn S.patch h
  have hE : ‖E U‖ ≤ (dawn G + M₁ + d)*t^d:= by
    by_cases he:U∈ξ a
    · rw [milled, indicator_of_mem he,radix]; let S':= column F A (t⁻¹ • Y) R U
      have hx : ‖distill F s A t i S'‖≤ M₁:= (sample F s t i H (le_trans (column_range F Y' hr (by unfold Y'; rw [norm_smul_of_nonneg (inv_pos.mpr hp).le]; exact mul_le_mul_of_nonneg_left hY (by positivity)) he) hh)).value
      have ha0 (b:ℝ): ‖t⁻¹*b‖ = t⁻¹*‖b‖ := by rw [norm_mul,Real.norm_of_nonneg (inv_pos.mpr hp).le]
      have hb : ‖t⁻¹ * arrow F A a i U‖≤ dawn G:= by
        rw [ha0]; exact (mul_le_mul_of_nonneg_left (dawn_use hC _ _ (grain ..|>.le)) (inv_pos.mpr hp).le).trans (by rw [← mul_assoc t⁻¹]; field_simp; exact (le_mul_of_one_le_left hZ' hZ))
      have hs : ‖scatter F A a i U‖≤1:= by unfold scatter; rw [Real.norm_of_nonneg (show _ from cut_low ..)]; exact cut_high ..
      have hM : ‖t⁻¹ * distill F s A t i S'‖≤ M₁:=by rw [ha0]; exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ht)).trans hx
      apply (norm_sub_le ..).trans ((add_le_add (le_trans (norm_mul_le ..) (mul_le_of_le_one_left (norm_nonneg _) hs)) ((norm_mul_le ..).trans (mul_le_mul hb hf (norm_nonneg _) hZ'))).trans ?_)
      exact add_le_add_left ((norm_sub_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul hf hM (norm_nonneg _) (pow_nonneg hp.le _))) hg)) _ |>.trans_eq (by ring)
    rw [milled,indicator_of_notMem he,norm_zero]; positivity
  apply (norm_sub_le ..).trans ((add_le_add hJ hE).trans_eq ?_); unfold proximity M₁ v; push_cast; ring
end YM.MatchingLedger.Periodical
