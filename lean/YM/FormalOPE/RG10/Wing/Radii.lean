import YM.FormalOPE.RG10.Wing.Patrol
/-! # Costing Ward-flow generators. Canons as above with absolute library sparks.
 All momentum units same Tier. Width paid before reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Patrol
open Function PowerSeries Finset Route Cycle HStein Tier Submarine
open scoped Topology BigOperators Classical
variable {Y : Type} [Fintype Y] (u:Y→Channel Y) (F:Tier) (w:Y→ℝ)
local notation "T"=>Channel Y
local notation "D"=> kick u
variable (P:Channel Y){k j t d:ℕ}
variable {u F}
omit [Fintype Y] in
lemma β_one (F:Tier)(w:Y→ℝ) (i:ℕ) : F.gain w (PowerSeries.X ^ i : Channel Y) k ≤ 1 := by
 rw [all_gain,X_pow_eq]; simp_rw [coeff_monomial]; by_cases h:i ≤ k
 · rw [sum_eq_single i]; · rw [if_pos rfl,Tier.unit]
   · intro j _ he; rw [if_neg he,Tier.zero]
   simp [h]
 apply le_trans (le_of_eq (sum_eq_zero fun j hj=> show F.valueOf w _=0 from by rw [if_neg (show j≠i from fun hz=> h (hz ▸ Nat.le_of_lt_succ (mem_range.mp hj))),Tier.zero])) zero_le_one

variable {M:ℝ}
variable (h:0≤w) (hv:Targeted F w w u k M) (he:Targeted Tier.free w w u k M) (hh:∀ i,Guard (u i) k 1)
variable (H:2≤M)(H': (k+1:ℝ)≤ M)
variable (hp: Guard P k d)
include hv he h H hp
def season (d k:ℕ):= 2*(d+3*k)+1
local notation "β"=> season d k

lemma push_day : F.gain w (D P) k ≤ M^season d k * F.gain w P k:= by
 have hh : 0 ≤ M := le_trans (by norm_num) H
 rw [F.near_eq (U:=D (∑ i∈range (k+1),PowerSeries.monomial i (coeff i P))) w _ (skew u (Facets.paper P k)), map_sum]; apply (F.sumUp w h _ _).trans; nth_rw 1 [all_gain]; rw [mul_sum]; -- order inspect
 apply sum_le_sum; intro i hi; have hS:= hp.slim i (Nat.le_of_lt_succ (mem_range.mp hi))
 rw [Facets.radical, Derivation.leibniz, Derivation.leibniz_pow, X_charged, smul_zero, smul_zero, smul_zero,add_zero,smul_eq_mul];
 apply (F.gain_mul w h _ _).trans
 apply (mul_le_of_le_one_left (F.collect w h _ ) (β_one F w i)).trans; apply (sails w h hv he hh _ _ hS).trans
 apply mul_le_mul_of_nonneg_right _ (F.lower _ h _)
 unfold season; rw [pow_succ,pow_mul]; gcongr; nlinarith
include hh
lemma power_fee : F.gain w (powers (kick u) j P) k ≤ M^(season d k*j)* F.gain w P k:= by
 induction j with
 | zero=> rw [steady]; simp
 | succ j ih=> rw [newDay]; apply (push_day w _ h hv he H (closed_powers u P hh d hp j)).trans; rw [Nat.mul_succ,Nat.add_comm, pow_add,mul_assoc]; exact mul_le_mul_of_nonneg_left ih (pow_nonneg (by linarith) _)
lemma cost_card : F.gain w (Cycle.numeral (kick u) j P) k ≤ M^(season d k*j)* F.gain w P k:= by
 unfold Cycle.numeral; rw [LinearMap.smul_apply,coin_steady,norm_inv,Complex.norm_natCast]; refine le_trans (mul_le_of_le_one_left (F.collect w h _) ?_) (power_fee w P h hv he hh H hp); exact inv_le_one_of_one_le₀ (by exact_mod_cast j.factorial_pos)
lemma propulsion (t:ℕ): F.gain w (tender u t P) k ≤ (t:ℝ)*(M^(season d k*t)* F.gain w P k):= by
 have hu :1 ≤ M := le_trans (by norm_num) H
 rw [touch]; apply (F.sumUp w h _ _).trans; refine le_trans (sum_le_sum ?_) (le_of_eq (show (∑ _∈ range t,M^(β*t)* F.gain w P k)=_ from by simp)); intro i hi; exact (cost_card w P h hv he hh H hp).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hu (Nat.mul_le_mul_left _ (mem_range.mp hi).le)) (F.collect w h _))
omit hp
include H'
def total (k:ℕ):=4+season 1 k*cycle 1 k
lemma changes (a:Y) : F.gain w (lane u k a) k ≤ M^total k * F.value (w a):= by
 have h1 : 0≤ M:=by linarith
 apply (propulsion w (sprout a) h hv he hh H (allowed a) _).trans; rw [recital F w a h]; unfold total;rw [pow_add,mul_assoc]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg h1 _) (F.cp (h a)))
 unfold cycle; push_cast; -- bound (2+3k)(k+1) ≤ M^4 etc
 nlinarith [sq_nonneg (M-k), show M^4 ≥ 4*M^2 from by nlinarith [pow_nonneg h1 3, mul_nonneg (show 0≤ M^2-4 by nlinarith) (sq_nonneg M)]] -- inspect
end YM.FormalOPE.RG10.Wing.Patrol
