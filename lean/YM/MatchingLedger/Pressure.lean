import YM.MatchingLedger.Ensemble
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absorb the (arbitrarily correlated!) boundary chord fluctuations in a local replacement estimate

Log ratio convolution. This gets rid of a boundary supremum/deterministic boundary bill,
without translation invariance or independence hypotheses on the physical law. Keeping the
shifted coupling charge in this step will matter when the external field is populated.
Applied below to actual nonlinear densities with weights and likelihoods on *full* fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger
open Set Filter Function RG MeasureTheory
open scoped Topology BigOperators

section account
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ}
    (hf : Weight μ f)

include hf in
lemma pressureBill_step {x y : V → ℝ} (hx : Envelope x) (hy : Envelope y)
    {C D Z : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (h : pressureBill μ f (fun v => C * x v - D * (y v - x v)) ≤ Z) :
    pressureBill μ f (fun v => C * x v) ≤
      C / (C+D) * Z + D / (C+D) * pressureBill μ f (fun v => C * y v) := by
  let p := C/(C+D); let q:=D/(C+D)
  have hc : 0<C+D := add_pos_of_pos_of_nonneg hC hD
  have hp : 0 ≤ p := by unfold p; positivity
  have hq : 0 ≤ q := by unfold q; positivity
  let W v := C*x v - D*(y v-x v)
  rw [show (fun v=>C*x v)=(fun v=>p*W v + q * (C*y v)) by funext v; unfold W p q; field_simp; ring]
  refine (pressure_blend hf ?_ ((Envelope.const C).mul hy) hp hq ?_).trans (by gcongr)
  · exact envelope_sub ((Envelope.const C).mul hx) ((Envelope.const D).mul (envelope_sub hy hx))
  unfold p q; field_simp

private lemma expenses {a : ℕ → ℝ} {g : ℕ → ℝ} {q w M : ℝ} (hq : 0 ≤ q) (hq' : q < 1)
    (h : ∀ r, a r ≤ g r*w + q * a (r+1)) (ht : ∀ r, a r ≤ M)
    (summ : Summable (fun r : ℕ => q^r * g r)) :
    a 0 ≤ (∑' r, q^r * g r) * w := by
  have hn (n : ℕ) : a 0 ≤ (∑ r ∈ Finset.range n, q^r*g r)*w + q^n*a n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      refine ih.trans (le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (h n) (pow_nonneg hq n)) ((∑ r ∈ Finset.range n, q^r*g r)*w)) (le_of_eq ?_))
      ring
  have hh : Tendsto (fun n : ℕ => (∑ r ∈ Finset.range n, q^r*g r)*w + q^n*M) atTop
      (𝓝 ((∑' r, q^r*g r)*w)) := by
    simpa only [zero_mul, add_zero] using
      (summ.hasSum.tendsto_sum_nat.mul_const w).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq').mul_const M)
  apply ge_of_tendsto' hh
  intro n; exact (hn _).trans (add_le_add_right (mul_le_mul_of_nonneg_left (ht n) (pow_nonneg hq n)) _)

def fee (d : ℕ) (C D : ℝ) :=
  ∑' n : ℕ, (D/(C+D))^n * (((n:ℝ)+1)^d * (C/(C+D)))

lemma fee_nonneg (d : ℕ) {C D : ℝ} (hc : 0 ≤ C) (hd : 0 ≤ D) : 0 ≤ fee d C D :=
  tsum_nonneg (fun i => by positivity)

lemma weighted_sum (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    Summable (fun n : ℕ => r ^ n * ((n:ℝ)+1)^d) := by
  rcases eq_or_lt_of_le hr with hr|hr
  · rw [← hr]; exact summable_of_ne_finset_zero (s:={0}) (fun i hi=>by rw [Finset.mem_singleton] at hi; rw [zero_pow hi,mul_eq_zero_of_left (rfl) _])
  let f (n : ℕ) := (n:ℝ)^d * r^n
  have h := (summable_nat_add_iff (f:=f) 1).mpr (summable_pow_mul_geometric_of_norm_lt_one d (by rwa [Real.norm_of_nonneg hr.le]))
  refine (h.mul_left r⁻¹).congr (fun n => ?_)
  unfold f; push_cast; rw [pow_succ]; field_simp

include hf in
/-- Deterministic log-pressure iteration on any sequence of regions (and no requirement of fit
for boundary outside the torus). `M` is any legitimate finite full-volume upper exponent,
can depend on every parameter and is not paid in the result. -/
theorem staircase {x : ℕ → V → ℝ} (hx : ∀ n, Envelope (x n)) {M : ℝ} (hm : ∀ n v, x n v ≤ M)
    {C D Z : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (d : ℕ)
    (h : ∀ n : ℕ, pressureBill μ f (fun v => C * x n v - D*(x (n+1) v-x n v)) ≤ ((n:ℝ)+1)^d * Z) :
    pressureBill μ f (fun v => C * x 0 v) ≤ fee d C D * Z := by
  let p := C/(C+D); let q := D/(C+D)
  have hc : 0 < C+D := by linarith only [hC, hD]
  have hq : 0 ≤ q := by unfold q; positivity
  have hz : q < 1 := (div_lt_one hc).2 (by linarith only [hC])
  refine expenses (g:=fun n => ((n:ℝ)+1)^d * p) (M:=C*M) (a:=fun n=>pressureBill μ f fun v=>C*x n v) hq hz (fun r=> ?_) (fun r=> ?_) ?_
  · refine (pressureBill_step hf (hx r) (hx (r+1)) hC hD (h r)).trans_eq ?_
    dsimp only [q,p]; ring
  · exact (pressure_mono hf ((Envelope.const C).mul (hx r)) (Envelope.const (C*M)) (fun v=>mul_le_mul_of_nonneg_left (hm r v) hC.le)).trans_eq (pressure_const hf _)
  exact ((weighted_sum d hq hz).mul_right _).congr (fun i=> mul_assoc (q^i) _ p)

end account
end YM.MatchingLedger
