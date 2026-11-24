import YM.FormalOPE.RG10.Transit.Meeting

/-!
# Age-budget arithmetic, including issue of choosing a coarse estimate stop under spacing caps
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function Real
open scoped Topology BigOperators Classical
variable {U : ℕ → Type} {X : Type}
namespace Scale
variable (W : Scale X U) {ξ τ : ℝ} {R C : ℝ} {δ : ℕ} {k i j N : ℕ}
local notation "μ" => W.μ
local notation "Y" => W.Y C R

def ticks (i j : ℕ) := log (W.μ i/W.μ j)
def fade (ξ : ℝ) (N i : ℕ) := Real.exp (-ξ*W.ticks i N)
local notation "ε" => W.fade ξ N

lemma ticks_pos (h : i ≤ j) : 0 ≤ W.ticks i j := log_nonneg ((one_le_div (W.positive _)).2 (W.decrease h))
@[simp] lemma ticks_self (j) : W.ticks j j=0 := by simp [ticks,(W.positive j).ne']
lemma ticks_add (j : ℕ) : W.ticks i N = W.ticks i j + W.ticks j N := by
  unfold ticks; rw [← log_mul];
  · congr 1; field_simp [(W.positive j).ne']
  · exact (div_pos (W.positive _) (W.positive _)).ne'
  exact (div_pos (W.positive _) (W.positive _)).ne'
lemma ticks_cost (h:Hours W R C δ k N) (a b : ℕ) : W.ticks a b=Y b - Y a := eq_sub_of_add_eq' (W.age R C h.base a b).symm
lemma ticks_exp (i j : ℕ) : exp (W.ticks i j) = W.μ i/W.μ j := exp_log (div_pos (W.positive _) (W.positive _))

lemma fade_nn : 0 ≤ ε i := (exp_pos _).le
lemma fade_low (h:0 ≤ ξ) (hi:i ≤ N) : ε i ≤ 1 := Real.exp_le_one_iff.mpr (by have := W.ticks_pos hi; apply mul_nonpos_of_nonpos_of_nonneg <;> linarith)
lemma fade_le (h:0 ≤ ξ) (hi:i ≤ j) : ε i ≤ ε j := by
  unfold fade; apply Real.exp_monotone; rw [ticks_add W j]; nlinarith [W.ticks_pos hi]
lemma fade_rpow : ε i = (μ N/μ i)^ξ := by
  rw [Real.rpow_def_of_pos (div_pos (W.positive _) (W.positive _)), show μ N/μ i=(μ i/μ N)⁻¹ from by rw [inv_div]]; unfold fade ticks; rw [log_inv]; ring_nf

-- quantify annulus counts independent of earlier poly widths
lemma ticks_step (i) : (2:ℝ)⁻¹ ≤ W.ticks i (i+1) := by
  rw [ticks];
  calc
    _ ≤ Real.log 2 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (2:ℝ)⁻¹ by norm_num); rw [Real.log_inv] at h; linarith
    _ ≤ _ := log_le_log (by norm_num) ((le_div_iff₀ (W.positive _)).mpr (W.thick _))
lemma reach_time (h : i ≤ j) : (j:ℝ)-i ≤ 2*W.ticks i j := by
  induction j,h using Nat.le_induction with
  | base=>simp
  | succ j h ih=>rw [ticks_add W j]; push_cast; linarith [ticks_step W j]
lemma ticks_number (h : Hours W R C δ k N) (hj:k ≤ i) (hi:i ≤ j) : ((Ico i j).card : ℝ) ≤ (Y j)^2 := by
  rw [Nat.card_Ico,Nat.cast_sub hi]
  have ht:= W.reach_time hi; rw [W.ticks_cost h] at ht
  nlinarith [h.richAt hj,h.richAt (hj.trans hi)]

/-- Choose a comparison mesh between j and N. Avoid needing a bounded ratio schedule here;
use the neighboring polynomial bound for this same step. -/
theorem nearer (h : Hours W R C δ k N) (hk:k ≤ i) (hn:i ≤ N) (ht:0 ≤ τ) (hu:τ<1) :
    ∃ l∈ Icc i N, W.ticks i l ≤ τ* W.ticks i N ∧ μ l ≤ ((Y N)^δ*W.fade τ N i)*μ i := by
  classical
  let u:= (Finset.Icc i N).filter (fun l => W.ticks i l ≤ τ* W.ticks i N)
  have h0:= W.ticks_pos hn
  have he : i∈u:= by apply mem_filter.mpr; simp [hn, mul_nonneg ht h0]
  let l := u.max' ⟨i,he⟩; have hl := mem_filter.mp (max'_mem u ⟨i,he⟩); obtain ⟨hx,hN⟩:= mem_Icc.mp hl.1
  refine ⟨l,hl.1,hl.2,?_⟩
  have hv:= W.positive i; have hT:= W.positive N; have hr:=h.richAt (hk.trans hn)
  have hy : 1 ≤ Y N:=by linarith
  by_cases H : l=N
  · have HH : W.ticks i N=0 := by have he : W.ticks i l ≤ τ* W.ticks i N := hl.2; rw [H] at he; nlinarith
    rw [H,fade,HH,mul_zero, exp_zero,mul_one]; exact (W.decrease hn).trans (le_mul_of_one_le_left hv.le (one_le_pow₀ hy))
  have h1 : l+1 ≤ N:=by change l≤N at hN; omega
  have hr : τ * W.ticks i N ≤ W.ticks i (l+1) := le_of_not_gt (fun ht'=> by
    have he : l+1∈u:= mem_filter.mpr ⟨mem_Icc.mpr ⟨(show i ≤ l from hx).trans (Nat.le_succ _),h1⟩,ht'.le⟩; exact Nat.not_succ_le_self l (le_max' _ _ he))
  apply le_trans (h.neighbor l (mem_Ico.mpr ⟨hk.trans hx,h1⟩)); rw [mul_assoc]
  apply mul_le_mul (pow_le_pow_left₀ (h.paid (hk.trans hx)) (W.sees R C h.base hN) δ) ?_ (W.positive _).le (pow_nonneg (h.paid (hk.trans hn)) _)
  rw [fade, ← div_le_iff₀ hv, neg_mul, exp_neg, show μ (l+1) / μ i = (μ i / μ (l+1))⁻¹ from by rw [inv_div], ← ticks_exp]
  exact inv_anti₀ (exp_pos _) (Real.exp_monotone hr)

-- optional refine absorb Y(N) large powers into half a fixed aging factor
lemma paylog {Z : ℝ} (r : ℕ) {t : ℝ} (h : 0 ≤ t) (hy : 1 ≤ Z) (ht : 0< τ) :
    (Z+t)^r ≤ ((Z * (1+r/τ))^r) * exp (τ*t) := by
  obtain rfl|hr := r.eq_zero_or_pos
  · simp [mul_nonneg ht.le h]
  have hp : (0:ℝ)<r:=by exact_mod_cast hr
  have h1 := Real.add_one_le_exp (τ*t/r); have h0:= Real.one_le_exp (show 0 ≤ τ*t/r by positivity)
  suffices Z+t ≤ Z*(1+(r:ℝ)/τ)*Real.exp (τ*t/r) by
    apply (pow_le_pow_left₀ (by linarith) this r).trans
    apply Eq.le; rw [mul_pow,← Real.exp_nat_mul]; congr 2; field_simp
  have hi : t ≤ ((r:ℝ)/τ)*exp (τ*t/r) := by field_simp; field_simp at h1; rw [mul_comm t τ]; nlinarith
  have he':1+(r:ℝ)/τ ≤ Z*(1+(r:ℝ)/τ):=le_mul_of_one_le_left (by positivity) hy
  -- cannot drop Z+t difference -- actually above loose but if Z>> exp small
  rw [mul_add,mul_one,add_mul]; nlinarith [mul_le_mul_of_nonneg_right hi (zero_le_one.trans hy)] -- inspect
lemma trade (h:Hours W R C δ k N) (hh:k ≤ i) (ht : i ≤ N) (r : ℕ) (he : 0 < ξ) :
    (W.Y C R N)^r * (W.fade ξ N i) ≤ (W.Y C R i * (1+r/(ξ/2)))^r * (W.fade (ξ/2) N i) := by
  unfold fade
  have hu : 1 ≤ W.Y C R i:= le_trans (by norm_num) (h.richAt hh)
  nth_rw 1 [show W.Y C R N=W.Y C R i + W.ticks i N from W.age R C h.base i N]
  apply le_trans (mul_le_mul_of_nonneg_right (paylog (τ:=ξ/2) r (W.ticks_pos ht) hu (by positivity)) (Real.exp_pos _).le)
  exact Eq.le (by rw [mul_assoc,← Real.exp_add]; ring_nf)
end Scale
end YM.FormalOPE.RG10.Transit
