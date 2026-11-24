import YM.FormalOPE.RG10.Transit.Window

/-!
# Summations on a geometric time slab

Arithmetic only. Fixed demands powers, includes real log-age of spacings (not just steps) and
allowed reference/tolerance parameter. Applications choose ages *before* constants...; any post
cost inequalities with pre-cost demands are external inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U : ℕ→ Type} {X : Type}
namespace Scale
variable (W : Scale X U) (R C : ℝ)
local notation "μ" => W.μ
def Y (C R : ℝ) (i : ℕ) := C+Real.log (R/W.μ i)
local notation "A" => W.Y C R
variable {b i j k N : ℕ}
variable (h : W.μ b ≤ R) (hk : b ≤ k) (hc : 2 ≤ C)
include h in
lemma intends : 0<R := (W.positive b).trans_le h
include hc h in
lemma rich (hi : b ≤ i) : 2 ≤ A i := (le_add_of_nonneg_right (Real.log_nonneg ((one_le_div (W.positive i)).2 ((W.decrease hi).trans h)))).trans' hc -- inspect
include h in
lemma sees (hi : i ≤ j) : A i ≤ A j := add_le_add (le_refl C) (Real.log_le_log (div_pos (W.intends R h) (W.positive i))
    (div_le_div_of_nonneg_left (W.intends R h).le (W.positive j) (decrease W hi)))
include h in
lemma age (i j : ℕ) : A j = A i + Real.log (μ i / μ j) := by unfold Y; rw [add_assoc,← Real.log_mul (div_ne_zero (W.intends R h).ne' (W.positive _).ne') (div_ne_zero (W.positive _).ne' (W.positive _).ne')]; congr 2; field_simp [(W.positive i).ne']

private lemma doubles (K : ℝ) (h : 2 ≤ K) (i : ℕ) : (i:ℝ)+1 ≤ K^i := by
  induction i with
  | zero=> norm_num
  | succ i ih => push_cast; rw [pow_succ]; nlinarith

/-- Polynomial in log length may at one corner spend a single power of raw length to consume an
arbitrary through-time polynomial demand. Do NOT use per-step adding to the primitive rates. -/
lemma loft {K t : ℝ} (hk : 2 ≤ K) (ht : 1 ≤ t) (p : ℕ) : (1+Real.log t)^p ≤ K^(p*p) * t := by
  have hi := (show (0:ℝ)<2 by norm_num).trans_le hk
  by_cases h : p=0
  · simpa [h] using ht
  have hh : 1 ≤ (p:ℝ):=by exact_mod_cast (show 1 ≤ p by omega)
  have he : 0 < (p:ℝ):= zero_lt_one.trans_le hh
  let x:= Real.log t
  have hx : 0 ≤ x := Real.log_nonneg ht
  have hT : 1+x≤ p*Real.exp (x/p) := by
    have hl := Real.add_one_le_exp (x/(p:ℝ)); field_simp at hl; linarith -- inspect
  have hu : Real.exp (x/p)^p=t := by rw [← Real.exp_nat_mul,mul_div_cancel₀ _ he.ne',Real.exp_log (zero_lt_one.trans_le ht)]; -- inspect
  rw [pow_mul]; apply (pow_le_pow_left₀ (show 0≤1+x by linarith) hT p).trans; rw [mul_pow,hu]
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans ht); exact pow_le_pow_left₀ (by positivity) (by linarith [doubles K hk p]) _
include h hc in
lemma long (hk:b ≤ i) (hj:i ≤ j) (p:ℕ) : (A j)^p ≤ (A i)^(p+p*p) * (μ i/μ j) := by
  have hu: 1 ≤ μ i/μ j := (one_le_div (W.positive _)).2 (W.decrease hj); have he := Real.log_nonneg hu
  have ha:=W.rich R C h hc hk
  have h' : 0<A i:=by linarith
  have hu' := W.rich R C h hc (hk.trans hj)
  apply (pow_le_pow_left₀ (show 0≤A j by linarith) (show A j ≤ A i*(1+Real.log (μ i/μ j)) from (W.age R C h i j) ▸ (by nlinarith)) p).trans
  rw [mul_pow,pow_add, mul_assoc]; exact mul_le_mul_of_nonneg_left (loft ha hu p) (by positivity)

lemma anneals (h:i≤N) : (∑ j∈ Ico i N, μ j) ≤ 2*μ i := by
  suffices (∑ j∈ Ico i N, μ j) + 2*μ N ≤ 2*μ i by linarith [W.positive N]
  induction N,h using Nat.le_induction with
  | base=> simp
  | succ j h ih => rw [Finset.sum_Ico_succ_top h]; linarith [W.thick j]
def absorb (u : ℕ) := u + u*u+1

include hc h in
/-- A step-position sum including arbitrary order-sized log polynomials. -/
theorem shorten (t u : ℕ) (ht : 2 ≤ t) (hi : b ≤ i) (hn:i ≤ N) :
    ∑ j∈ Finset.Ico i N, (A j)^u * (μ j/R)^t ≤ (A i)^absorb u * (μ i/R)^t := by
  have hp:= W.positive i
  have ha:=W.rich R C h hc hi
  have ha' : 0≤A i:=by linarith
  let Y:= (A i)^(u+u*u)*(μ i/R)^t
  have hR := W.intends R h
  have hY : 0 ≤ Y:=by unfold Y; positivity
  apply le_trans (b:=∑ j∈Ico i N,Y/μ i*(μ j)) (sum_le_sum fun j hj => ?_) ?_ -- Lean order inspect
  swap
  · have hk : i ≤ j:= (mem_Ico.mp hj).1
    have hr := W.positive j
    apply (mul_le_mul_of_nonneg_right (W.long R C h hc hi hk u) (by positivity)).trans
    let x:=μ j/μ i; have hu : x≤1:=(div_le_one hp).2 (W.decrease hk)
    have hx : 0<x:= div_pos hr hp
    have h0 : μ j/R=μ i/R*x:=by unfold x; field_simp
    have h1 : μ i/μ j=x⁻¹:=by unfold x; rw [inv_div]
    rw [h0,h1,mul_pow]
    calc
      _ ≤ ((A i)^(u+u*u)*x⁻¹)*((μ i/R)^t * x^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx.le hu ht) (by positivity)) (by positivity)
      _ = Y / μ i * μ j := by unfold Y x; field_simp
  rw [← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left (W.anneals hn) (by positivity)).trans; calc
    _ = 2*Y := by field_simp
    _ ≤ (W.Y C R i)*Y := mul_le_mul_of_nonneg_right ha hY
    _ = _ := by unfold Y absorb; rw [pow_succ]; ring
end Scale
end YM.FormalOPE.RG10.Transit
