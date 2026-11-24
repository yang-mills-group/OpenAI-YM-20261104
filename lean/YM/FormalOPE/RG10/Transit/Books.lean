import YM.FormalOPE.RG10.Transit.Stability

/-!
# Explicit costing of distant and nearby step in one chosen unit

Order-by-order traversal exponent can be funded by finite extra moments of each coefficient
operation. Coherent parameters C etc. These do not price a sum over capture centers or horizons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U : ℕ → Type} {X : Type}
namespace Hours
variable {W : Scale X U} {R C : ℝ} {δ b j N a k : ℕ} (h : Hours W R C δ b N)
local notation "Y" => W.Y C R
local notation "μ" => W.μ
include h
lemma richAt (hi : b ≤ j) : 2 ≤ Y j := W.rich R C h.base h.rich hi
lemma paid (hi : b ≤ j) : 0 ≤ Y j := by linarith [h.richAt hi]
lemma near1 (hi : b ≤ j) : 1 ≤ R/μ j := (one_le_div (W.positive _)).mpr ((W.decrease hi).trans h.base)
lemma zees (hi:b ≤ j) : C ≤ Y j := le_add_of_nonneg_right (Real.log_nonneg (h.near1 hi))
lemma R_pos : 0 < R := W.intends R h.base
lemma exchange (hi : j ∈ Ico b N) : R/μ (j+1) ≤ Y j^δ * (R/μ j) := by
  rw [← mul_div_assoc, div_le_div_iff₀ (W.positive _) (W.positive _)]
  apply (mul_le_mul_of_nonneg_left (h.neighbor j hi) h.R_pos.le).trans
  exact le_of_eq (by ring)

lemma further (i l : ℕ) (hi : i∈Ico b N) (p) :
    Y (i+1)^p * (R/μ (i+1))^l ≤ Y i^(δ*p+δ*l) * (R/μ i)^l := by
  have hh := W.positive i
  have hm := W.positive (i+1)
  have ha := h.paid (mem_Ico.mp hi).1; have hx := h.R_pos
  rw [pow_add, mul_assoc, pow_mul, pow_mul, ← mul_pow];
  exact mul_le_mul (pow_le_pow_left₀ (h.paid ((mem_Ico.mp hi).1.trans (Nat.le_succ _))) (h.year i hi) p) (pow_le_pow_left₀ (by positivity) (h.exchange hi) l) (by positivity) (by positivity)

lemma earlier {i j p l : ℕ} (hi : b ≤ i) (hk : i ≤ j) :
    Y i^p*(R/μ i)^l ≤ Y j^p*(R/μ j)^l := by
  have ha := h.paid hi; have hh := h.paid (hi.trans hk); have hx := h.R_pos; have ht := W.positive i; have hj := W.positive j
  gcongr
  · exact W.sees R C h.base hk
  exact W.decrease hk

local notation "L" => R/C^δ
lemma reap (hi:b ≤ j) (M N' K : ℕ) (H : M ≤ N') {x:ℝ}
    (hx : tip (L/μ j) N' * x ≤ Y j^K*(R/μ j)^M) :
    x ≤ Y j^(K+δ*N')*(μ j/R)^(N'-M) := by
  have hA : 0 < C:=by linarith [h.rich]
  have hy := h.paid hi
  have ht := W.positive j; have hr:= h.R_pos
  have he : 0 < L/μ j := by positivity
  have hh : x ≤ C^(δ*N') * Y j^K * (μ j/R)^(N'-M) := by
    by_cases hp: x < 0
    · apply le_trans hp.le; positivity
    have hp : 0 ≤ x:= le_of_not_gt hp
    have hk : (L/μ j)^N'*x ≤ Y j^K * (R/μ j)^M := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he.le (by linarith) _) hp).trans hx -- inspect
    rw [← mul_le_mul_iff_right₀ (pow_pos he N')]; apply hk.trans; apply le_of_eq
    rw [div_pow _ _ N',div_pow _ _ N',div_pow,div_pow]; field_simp
    nth_rw 1 [show W.μ j ^ N' = W.μ j ^ M*W.μ j^(N'-M) from (Eq.symm ((pow_add (W.μ j) M _).symm.trans (by rw [Nat.add_sub_of_le H])))]
    have he : R^N'=R^M*R^(N'-M):= Eq.symm ((pow_add R M _).symm.trans (by rw [Nat.add_sub_of_le H]))
    rw [he,← pow_mul]
    ring
  rw [pow_add, mul_comm (Y j^K)]
  exact hh.trans (by gcongr; exact zees h hi)
end Hours
end YM.FormalOPE.RG10.Transit
