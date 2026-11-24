import YM.RG04B.Envelope
import YM.Trace.Physicalv2.GermLedger

/-!
# Cost/length of physical descent toward a report, on any N-trajectory

Includes emitted backward column products and the coupling-power payment for an
*entire* close or soft window. `close` admits rougher post-block powers, `soft`
needs the pre-paid/geometric matrix estimates. Windows always on one schedule.
No cone or matching assumptions to get these bills. Any root/marker cost not
included in invoices still needs to be re-checked by the producer. Proof also
checks existence (there are actual levels meeting these windows despite moving
ratio).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open Function Filter Lattice RG Finset Real
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (hG : G.Simple)

-- use s spacing not levels; endpoint names m=fine and i=bottom

def age (a : Levels G) (i m : ℕ) := a.S.scale m - a.S.scale i

def close (a : Levels G) (r : ℝ) (m i : ℕ) : Prop := i ≤ m ∧ age a i m ≤ r * geo a m
def soft (a : Levels G) (r : ℝ) (m i : ℕ) : Prop := i ≤ m ∧ age a i m ≤ r * logSize a m

section Geometry
variable {a : Levels G}

set_option quotPrecheck false
local notation "T" => a.clock
local notation "L" => ratio a
local notation "s" => a.S.scale
local notation "ℓ" => logSize a
local notation "Y" => geo a

lemma sub {i j k : ℕ} : age a i k = age a i j + age a j k := by unfold age; ring
lemma age_step {i j : ℕ} : age a i (j+1) = age a i j + stride a j := by
  unfold age; rw [distance_step a]; ring
lemma age_first {i m : ℕ} : age a i m = age a (i+1) m + stride a i := by
  unfold age; rw [distance_step a]; ring
lemma age_nonneg {i k : ℕ} (h : i ≤ k) : 0 ≤ age a i k := by
  induction k,h using Nat.le_induction with
  | base => simp only [age,sub_self,le_refl]
  | succ k hk IH => rw [age_step]; exact add_nonneg IH (stride_pos ..).le
lemma Span.admits {j i k : ℕ} {r : ℝ} (h : close a r k i) (hj : i ≤ j) (hk : j ≤ k) : close a r k j := by
  refine ⟨hk, le_trans ?_ h.2⟩
  linarith only [sub (i:=i) (j:=j) (k:=k) (a:=a),age_nonneg (a:=a) hj]
lemma age_prod {i k : ℕ} (h : i ≤ k) (z : ℝ) :
    ∏ j ∈ Ico i k, L j ^ z = Real.exp (z * age a i k) := by
  induction k,h using Nat.le_induction with
  | base => simp [age]
  | succ k hk IH =>
    rw [show Finset.Ico i (k+1)=insert k (Finset.Ico i k) by ext; simp; omega, prod_insert (by simp), IH, age_step]
    rw [Real.rpow_def_of_pos (show 0<L k by linarith [ratio_lo a k]), mul_add, Real.exp_add, mul_comm, mul_comm (Real.log _)]
    rfl
lemma ySmall (m : ℕ) : geo a m ≤ logSize a m := by
  rw [geo_eq]; linarith [Real.log_le_sub_one_of_pos (zero_lt_two.trans_le (logSize_hi a m))]
lemma close_inside {r : ℝ} (hr : 0≤r) (i m : ℕ) (hi : close a r m i) : soft a r m i :=
  ⟨hi.1,(hi.2).trans (mul_le_mul_of_nonneg_left (ySmall m) hr)⟩

include hG
/-- Stops at *real* meshes with overshoot ≤ log Y(m), no sharp plateau approximation
presumed. Uniform over a finite-demand set of such soft/close targets (can use z
varying over them). -/
theorem crossing {V : Fees} (h : stripe V a) {r : ℝ} (k lo : ℕ) : ∀ᶠ m in atTop,
    ∀ z : ℝ, 0 ≤ z → z ≤ r * ℓ m ^ k →
      ∃ i : ℕ, lo ≤ i ∧ i ≤ m ∧ z ≤ age a i m ∧ age a i m ≤ z + Real.log (geo a m) := by
  have hr : Tendsto (fun m => r*(ℓ m ^ k/s m)) atTop (𝓝 0) := by
    simpa using (Tendsto.const_mul r (indexPrice a hG k))
  filter_upwards [eventually_ge_atTop lo, hr.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2)),
    a.S.divergent.eventually_ge_atTop (2*s lo), a.S.divergent.eventually_gt_atTop 0]
      with m hm ht hf hw z hz hx
  have hs := (div_le_iff₀ hw).1 (show r*ℓ m^k/s m ≤ 1/2 by rw [mul_div_assoc]; exact ht)
  -- maximize mesh meeting length
  let S := (Finset.Icc lo m).filter fun i => z ≤ age a i m
  have hp : lo ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hm⟩,show z≤age a lo m from (by unfold age; linarith)⟩
  let i := S.max' ⟨lo,hp⟩
  have hi:i ∈ S:= S.max'_mem _
  obtain ⟨hy,hX⟩:= mem_filter.mp hi
  obtain ⟨hi,hI⟩:= mem_Icc.mp hy
  refine ⟨i,hi,hI,hX,?_⟩
  rcases hI.eq_or_lt with h'|h'
  · rw [h',age, sub_self]; exact add_nonneg hz (Real.log_nonneg (geo_hi ..))
  rcases lt_or_ge (age a (i+1) m) z with hK|hK
  · have hL : stride a i ≤ Real.log (geo a m) := Real.log_le_log
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (ratio_lo ..)) ((limitRatio h i).trans (monotone_geo a hG hI))
    exact age_first.le.trans (add_le_add hK.le hL)
  have ha : i+1∈S:= mem_filter.mpr ⟨mem_Icc.mpr ⟨hi.trans i.le_succ,h'⟩,hK⟩
  exact False.elim (Nat.not_succ_le_self _ (Finset.le_max' S (i+1) ha))

omit hG in
lemma ageMesh {i k : ℕ} : exp (age a i k)= a.S.a i / a.S.a k := by
  unfold age Schedule.scale
  rw [Real.exp_sub,Real.exp_log (inv_pos.mpr (a.S.a_pos _)),Real.exp_log (inv_pos.mpr (a.S.a_pos _)), inv_div_inv]
/-- qalg's capture bottom (strictly advancing tail to keep pair gates).
Physical aᵦ and prescribed relative radius ρ in shape units up to Λ^B. -/
theorem capture {V : Fees} (h : stripe V a) (lo B : ℕ) : ∀ᶠ m in atTop,
    ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ ℓ m ^ B →
      ∃ b : ℕ, lo ≤ b ∧ close a ((B:ℝ)+1) m b ∧
        a.S.a m * ρ ≤ a.S.a b ∧ a.S.a b ≤ geo a m * (a.S.a m * ρ) := by
  filter_upwards [crossing hG h (r:=(B:ℝ)) 1 lo] with m hh ρ hr hρ
  have hz:0 < ρ:= zero_lt_one.trans_le hr
  have ht:= Real.log_le_log hz hρ; rw [Real.log_pow] at ht
  let y:= geo a m
  have hy:1 ≤ y:= geo_hi ..
  have hv : Real.log (ℓ m) ≤ y := le_add_of_nonneg_left zero_le_one
  obtain ⟨b,hb,hs,h₁,h₂⟩:= hh (Real.log ρ) (Real.log_nonneg hr) (ht.trans (mul_le_mul_of_nonneg_left
    (hv.trans ((ySmall m).trans (by rw [pow_one]))) (Nat.cast_nonneg B)))
  refine ⟨b,hb,⟨hs,?_⟩,?_,?_⟩
  · have h' := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hy); linarith [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α:=ℝ) B)]
  · have hg := Real.exp_monotone h₁
    rw [ageMesh, Real.exp_log hz,le_div_iff₀ (a.S.a_pos _), mul_comm] at hg; exact hg
  have hg := Real.exp_monotone h₂
  rw [ageMesh, Real.exp_add, Real.exp_log hz,Real.exp_log (zero_lt_one.trans_le hy),div_le_iff₀ (a.S.a_pos _)] at hg
  exact hg.trans_eq (by ring)

end Geometry

section Coupons
variable {C : Family G}
open Trace.Physical.GermGraph
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "L" => ratio C.path.levels
local notation "ℓ" => logSize C.path.levels
local notation "cash" => ticket C.path.levels
local notation "s" => C.S.scale

/-- On the soft stretch of any fixed announced length factor (*not* Λ²
when exact inverse products after each defect are counted), L powers from
stock/log gate cost arbitrary small in g across *all* subproducts,
no dependence on the ultraviolet distance. Includes B^*Λ_b age. -/
theorem backward (hC : C.Makes) (hG : G.Simple) (r : ℝ) (hr : 0 ≤ r)
    {ε η : ℝ} (he : 0 < ε) (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ N p i, m ≤ N → soft P r m i →
      (∏ j ∈ Ico i m, 4 * (C.path.levels.params (j+1)).columns) * gAt C N p m ^ ε ≤ η := by
  let w:= ε/(16*(r+1)); have hw:0<w:= by unfold w; positivity
  obtain ⟨J,hJ⟩:= eventually_atTop.1 (factor_large C w hw)
  filter_upwards [indices P hG J 1 r,
      (persist P hG).eventually_ge_atTop (- (Real.log η) / (ε/8)), runningLogs hC hG] with m hm ht hh N p i hN hi
  have hx : J ≤ i := (hm i hi.1 (by simpa only [age,pow_one] using hi.2)).1
  apply le_trans (mul_le_mul_of_nonneg_right (show (∏ j ∈ Ico i m, 4*(C.path.levels.params (j+1)).columns) ≤ ∏ j ∈ Ico i m, L j ^ w from ?_) (Real.rpow_nonneg (running_pos hC _ p _ hN).le _))
  · have hw₀:= ((hh N p hN).2)
    have hl:= mul_le_mul_of_nonneg_left hi.2 hw.le
    have hs : w * r ≤ ε/8 := by
      unfold w; rw [div_mul_eq_mul_div, div_le_iff₀]; nlinarith; positivity
    rw [div_le_iff₀ (by linarith : 0<ε/8)] at ht
    rw [age_prod hi.1, Real.rpow_def_of_pos (running_pos hC _ _ _ hN),← Real.exp_add]
    apply (Real.exp_monotone ?_).trans_eq (Real.exp_log hη)
    linarith only [ht,hl,mul_le_mul_of_nonneg_right hs (zero_le_two.trans (logSize_hi P m)),
      mul_le_mul_of_nonneg_right hw₀ he.le]
  exact prod_le_prod (fun i _=> mul_nonneg (by norm_num) (zero_le_one.trans (P|>.params _|>.columns_ge)))
    fun j hj=> (hJ j (hx.trans (mem_Ico.mp hj).1)).2

/-- Rough (post-block, marker polynomial, widened support, allocated
geometry powers) costs recoverable across an entire close stretch, even
when every step is charged the most advanced ticket. -/
theorem localCoupon (k : ℕ) {c r : ℝ} (hc : 0 ≤ c)
    :
    ∀ m i, close P r m i → (cash c k m)^(m-i) ≤
        cash (r/(Real.log 3)*c) (k+1) m := by
  intro m i hi
  have hx := (stepsPay P hi.1).trans hi.2
  let y := geo P m
  have hl : 0<Real.log 3 := Real.log_pos (by norm_num)
  have he : ((m-i:ℕ):ℝ) ≤ (r / Real.log 3 * y):= (le_div_iff₀ hl|>.mpr hx).trans_eq (by ring)
  unfold ticket; rw [← Real.exp_nat_mul]; apply Real.exp_monotone
  apply le_trans (mul_le_mul_of_nonneg_right he (mul_nonneg hc (pow_nonneg (zero_le_one.trans (geo_hi ..)) _)))
  apply le_of_eq; unfold y; ring

/-- Bound a physical close product from ticket bounds. Costs include geometry even
if every step charges the beam/ticket of the finest scale. -/
theorem receipt (hC : C.Makes) (hG : G.Simple) {u : ℕ→ℝ} (h : Budgeted P u) {r : ℝ} (hr : 0 ≤ r)
    {ε η : ℝ} (he : 0 < ε) (hη : 0 < η) : ∀ᶠ m in atTop, ∀ N p i, m ≤ N → close P r m i →
       (∏ j ∈ Ico i m, u j) * gAt C N p m ^ ε ≤ η := by
  obtain ⟨c,hc,k,H⟩:=h
  obtain ⟨u₀,h₀⟩:=eventually_atTop.1 H
  let A : ℝ:= r/(Real.log 3)*c
  have hA:0≤A:= by unfold A; exact mul_nonneg (div_nonneg hr (Real.log_nonneg (by norm_num))) hc
  filter_upwards [keepPaid hC hG he hη (prepaid P A (k+1) hA),indices P hG u₀ 1 r] with m hx hY N p i hN hh
  have hp : u₀ ≤ i := (hY i hh.1 (by rw [pow_one]; exact (close_inside hr i m hh).2)).1
  have hU : ∏ j ∈ Ico i m, u j ≤ ∏ _j ∈ Finset.Ico i m, cash c k m :=
    prod_le_prod (fun i hi=> (h₀ i (hp.trans (mem_Ico.mp hi).1)).1) fun i hi=>
      (h₀ i (hp.trans (mem_Ico.mp hi).1)).2.trans (Real.exp_monotone <| mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (geo_hi ..)) (monotone_geo P hG (mem_Ico.mp hi).2.le) _) hc)
  simp only [prod_const,Nat.card_Ico] at hU
  exact le_trans (mul_le_mul_of_nonneg_right (hU.trans (localCoupon k hc m i hh))
    (Real.rpow_nonneg (running_pos hC _ p _ hN).le ε)) (hx N p hN)

end Coupons
end YM.RG04B
