import YM.Integration.WilsonReceivedCloseHard
import YM.Integration.WilsonRootedKioskCloseClock

/-! The actual dated hard quote pays the original forced divisor after
restoring the complete physical marker wallet at its reported coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseForcedPrice
open Filter Lattice Wilson RG QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset Push.PriceCompiler Pert.Asymptotics LocalComparison
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)

include simple in
theorem original (degree a p : ℕ) {Q ε : ℝ} (cap : 0 ≤ Q) (allow : 0 < ε) (way : WayStation R.kit) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per, b ≤ N →
      ∀ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (H : (i:ℕ) → Rep G (R.family.side i per))
          (start k:ℕ), start ≤ m → Concourse R.alloy R.kit R.T π Γ start N per k H →
      ∀ i, m ≤ i → i < b → ∀ Ω : ℝ, 0 ≤ Ω → Ω ≤ budgetR R i →
        (Ω^6)^a * quoteR R (H (i+1)).beta i ≤
          ε*(regulatorRun R.family N per b)^p * forcedDivisor R.family i := by
  let e := ε/(3:ℝ)^(p+1)
  have ep : 0 < e := div_pos allow (pow_pos (by norm_num) _)
  filter_upwards [WilsonReceivedCloseInterval.purchased R simple degree (6*a) cap (η:=1) (by norm_num),
    WilsonRootedKioskCloseClock.original R simple degree a (p+1) cap ep way]
      with b roof quote m mb close N per top π Γ H start k floor course i mi ib Ω op paid
  let x := regulatorRun R.family N per b
  let f := regulatorRun R.family N per (i+1)
  let κ := forcedDivisor R.family i
  have κ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have x0 : 0 ≤ x := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have f0 : 0 ≤ f := inv_nonneg.mpr (Real.sqrt_nonneg _)
  obtain ⟨strip, temp⟩ := roof m mb close N per top
  have single : budgetR R i ≤ PaceR.roof R i b := by
    rw [PaceR.roof_step R ib]
    exact le_mul_of_one_le_right (zero_le_one.trans (budget_pos R)) (PaceR.roof_ge ..)
  have factor : (Ω^6)^a ≤ x⁻¹ := by
    have many : PaceR.roof R i b ^ (6*a+2) ≤ x ^ (-(1:ℝ)) := strip i mi ib.le
    rw [Real.rpow_neg x0,Real.rpow_one] at many
    rw [← pow_mul]
    exact (pow_le_pow_left₀ op (paid.trans single) _).trans
      ((pow_le_pow_right₀ (PaceR.roof_ge ..) (by omega : 6*a ≤ 6*a+2)).trans many)
  have held : quoteR R (H (i+1)).beta i ≤ e*f^(p+1)*κ :=
    ((quote.2 m mb close).2.2 i mi ib N per top).2 π Γ H start k floor course
  have near : f ≤ 3*x := temp (i+1) (by omega) (by omega)
  have compensated : x⁻¹*x^(p+1) ≤ x^p := by
    by_cases zero : x=0
    · rw [zero, inv_zero, zero_mul]
      positivity
    · rw [pow_succ, ←mul_left_comm, inv_mul_cancel₀ zero, mul_one]
  calc
    _ ≤ (Ω^6)^a*(e*f^(p+1)*κ) := mul_le_mul_of_nonneg_left held (pow_nonneg (pow_nonneg op _) _)
    _ ≤ x⁻¹*(e*(3*x)^(p+1)*κ) := by
      apply mul_le_mul factor _ (mul_nonneg (mul_nonneg ep.le (pow_nonneg f0 _)) κ0) (inv_nonneg.mpr x0)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ f0 near _) ep.le) κ0
    _ = ε*(x⁻¹*x^(p+1))*κ := by
      have cancel : e*(3:ℝ)^(p+1)=ε := div_mul_cancel₀ _ (by positivity)
      rw [mul_pow,← cancel]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left compensated allow.le) κ0

end YM.Integration.WilsonReceivedCloseForcedPrice
