import YM.Integration.WilsonPhysicalHistoryFiniteTicketPrice
import YM.Pert.Asymptotics.RawAxis

/-! Spend the finite-name and quiet reserve at the true finite-cutoff coupling
of the original physical family, on all future regulators and tori. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFiniteTicketTarget
open Filter Real Lattice Wilson RG Source Pert.Asymptotics
open scoped Topology

theorem physical {G : Gauge} (C : Family G) (m : C.Makes) (simple : G.Simple)
    (names p h : ℕ) {b ε : ℝ} (hb : 0 ≤ b) (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ j, k ≤ j → ∀ N n, j ≤ N → ∀ Θ : ℝ,
      Θ ≤ b * (regulatorRun C N n j)⁻¹^h →
      C.path.levels.clock.forcedAllowance j + names * (Θ*sqrt (C.path.levels.clock.forcedAllowance j)) ≤
        ε*(regulatorRun C N n j)^p := by
  have two (a : ℕ) : 0 < (2:ℝ)^a := by positivity
  have purchase := WilsonPhysicalHistoryFiniteTicketPrice.all_late C.path.levels simple names p h
    (mul_nonneg hb (two h).le) (div_pos he (two p))
  filter_upwards [purchase] with k funding
  intro j late N n eligible Θ intake
  let hat := sqrt (C.path.levels.clock.hatBeta j)
  let here := sqrt (C.path.β N n j)
  have hat_pos : 0 < hat := sqrt_pos.mpr (WardBin.hot C.path.levels j)
  have here_pos : 0 < here := sqrt_pos.mpr (Overlay.beta_positive m.wilson eligible)
  have bound := (m.wilson.represents N n j eligible).band.2
  have measured : here ≤ (2:ℝ)*hat := by
    calc
      here ≤ sqrt (4*(C.path.levels.clock.hatBeta j)) := sqrt_le_sqrt
        (bound.trans (mul_le_mul_of_nonneg_right (by norm_num) (WardBin.hot C.path.levels j).le))
      _ = 2*hat := by rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num [hat]
  have billed : Θ ≤ (b*2^h)*(C.path.levels.clock.hatCoupling j)⁻¹^h := by
    change Θ ≤ (b*2^h)*(hat⁻¹)⁻¹^h
    change Θ ≤ b*(here⁻¹)⁻¹^h at intake
    rw [inv_inv] at intake ⊢
    simpa only [mul_pow, mul_assoc] using intake.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ here_pos.le measured h) hb)
  have output := funding j late Θ billed
  have running : hat⁻¹ ≤ 2*here⁻¹ := by
    field_simp [hat_pos.ne', here_pos.ne']
    simpa only [mul_comm hat] using measured
  refine output.trans ?_
  change (ε/2^p)*(hat⁻¹)^p ≤ ε*(here⁻¹)^p
  calc
    _ ≤ (ε/2^p)*(2*here⁻¹)^p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hat_pos).le running p) (div_pos he (two p)).le
    _ = _ := by rw [mul_pow]; field_simp

end YM.Integration.WilsonPhysicalHistoryFiniteTicketTarget
end

