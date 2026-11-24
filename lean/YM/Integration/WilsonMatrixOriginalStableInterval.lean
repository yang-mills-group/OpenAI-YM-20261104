import YM.Integration.WilsonMatrixTicketLanesReportedCurrency
import YM.Integration.WilsonMatrixOriginalGermReturn

/-! A signed stable source has a geometric error on any length of the original history.
Its terminal cost is retained. Each local error is evaluated at the original measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalStableInterval
open Filter Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open Pert.Asymptotics
variable {G : Gauge} (R : Run G)

private theorem hats (simple : G.Simple) (A : Levels G) : Monotone A.clock.hatBeta := by
  refine monotone_nat_of_le_succ fun i => ?_
  have block : (1:ℝ) ≤ (A.S.block i).val := by exact_mod_cast (A.S.block i).pos
  have extra := mul_nonneg (Gauge.slopeConstant_pos simple).le (Real.log_nonneg block)
  unfold Calendar.hatBeta
  rw [show A.clock.schedule.scale (i+1) = A.S.scale i + Real.log (A.S.block i).val from A.S.scale_succ i]
  linarith only [extra]

theorem local_coupling (simple : G.Simple) (m i N p : ℕ) (hmi : m ≤ i) (hin : i ≤ N) :
    0 < regulatorRun R.family N p m ∧
    regulatorRun R.family N p i ≤ 2 * regulatorRun R.family N p m := by
  let A := R.family.path.levels
  let β := R.family.path.β N p
  have bₘ := (R.makes.wilson.represents N p m (hmi.trans hin)).band
  have bᵢ := (R.makes.wilson.represents N p i hin).band
  have hm : 0 < β m := (half_pos (zero_lt_one.trans (A.fits.delayed m))).trans_le bₘ.1
  have hi : 0 < β i := (half_pos (zero_lt_one.trans (A.fits.delayed i))).trans_le bᵢ.1
  have hβ : β m ≤ 4 * β i := calc
    β m ≤ 2 * A.clock.hatBeta m := bₘ.2
    _ ≤ 2 * A.clock.hatBeta i := by gcongr; exact hats simple A hmi
    _ ≤ 4 * β i := by
      have lower : A.clock.hatBeta i / 2 ≤ β i := bᵢ.1
      linarith only [lower]
  have roots : sqrt (β m) ≤ 2 * sqrt (β i) := by
    exact (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp (by
      simpa only [mul_pow, sq_sqrt hm.le, sq_sqrt hi.le, show (2:ℝ)^2=4 by norm_num] using hβ)
  change 0 < (sqrt (β m))⁻¹ ∧ (sqrt (β i))⁻¹ ≤ 2*(sqrt (β m))⁻¹
  refine ⟨inv_pos.mpr (sqrt_pos.mpr hm), ?_⟩
  rw [←one_div,←div_eq_mul_inv]
  exact (div_le_div_iff₀ (sqrt_pos.mpr hi) (sqrt_pos.mpr hm)).mpr (by simpa using roots)

private theorem geometric {u A : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (n : ℕ) (x : ℕ → ℝ)
    (step : ∀ j < n, x j - A ≤ u*(x (j+1)-A)) : x 0 ≤ u^n*x n + A := by
  have soFar : ∀ k ≤ n, x 0 - A ≤ u^k*(x k-A) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      calc
        x 0 - A ≤ u^k*(x k-A) := ih (by omega)
        _ ≤ u^k*(u*(x (k+1)-A)) := mul_le_mul_of_nonneg_left (step _ (by omega)) (pow_nonneg hu _)
        _ = u^(k+1)*(x (k+1)-A) := by ring
  have upper := (soFar n le_rfl).trans (mul_le_mul_of_nonneg_left (sub_le_self _ hA) (pow_nonneg hu _))
  linarith only [upper]

/-- The scale at capture is m+n. The physical cutoff N and period p are arbitrary. -/
theorem priced (simple : G.Simple) (m n N p : ℕ) (live : m+n ≤ N)
    (γ ν C : ℝ) (hγ : 0 < γ) (hν : 0 ≤ ν) (hC : 0 ≤ C) (cost : ℕ → ℝ)
    (nonneg : ∀ i, m ≤ i → i ≤ m+n → 0 ≤ cost i)
    (one_step : ∀ i, m ≤ i → i < m+n →
      cost i ≤ exp (-γ * log (R.family.S.block i).val) * cost (i+1) +
        C * (regulatorRun R.family N p (i+1))^ν) :
    let θ := exp (-γ * log 3)
    cost m ≤ θ^n * cost (m+n) + C*(2*regulatorRun R.family N p m)^ν / (1-θ) := by
  let θ := exp (-γ * log 3)
  have ht : 0 < θ := exp_pos _
  have small : θ < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hγ) (log_pos (by norm_num)))
  let cash := C*(2*regulatorRun R.family N p m)^ν
  let A := cash/(1-θ)
  have gm := (local_coupling R simple m m N p le_rfl (by omega)).1
  have pos : 0 ≤ A := div_nonneg (mul_nonneg hC (rpow_nonneg (by positivity) _)) (sub_pos.mpr small).le
  have fixed : cash = (1-θ)*A := calc
    cash = (cash/(1-θ))*(1-θ) := (div_mul_cancel₀ cash (sub_pos.mpr small).ne').symm
    _ = (1-θ)*A := mul_comm ..
  apply geometric ht.le pos n (fun j => cost (m+j))
  intro j hj
  have hi : m+j < m+n := by omega
  have block : (3:ℝ) ≤ (R.family.S.block (m+j)).val := by exact_mod_cast R.family.S.block_large (m+j)
  have decay : exp (-γ*log (R.family.S.block (m+j)).val) ≤ θ :=
    exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.log_le_log (by norm_num) block) (neg_nonpos.mpr hγ.le))
  have g := local_coupling R simple m (m+j+1) N p (by omega) (by omega)
  have gi := (local_coupling R simple (m+j+1) (m+j+1) N p le_rfl (by omega)).1
  have noise : C*(regulatorRun R.family N p (m+j+1))^ν ≤ cash :=
    mul_le_mul_of_nonneg_left (rpow_le_rpow gi.le g.2 hν) hC
  have bound := (one_step _ (by omega) hi).trans
    (add_le_add (mul_le_mul_of_nonneg_right decay (nonneg _ (by omega) (by omega))) noise)
  change cost (m+j)-A ≤ θ*(cost (m+j+1)-A)
  linarith only [bound,fixed]

end YM.Integration.WilsonMatrixOriginalStableInterval
