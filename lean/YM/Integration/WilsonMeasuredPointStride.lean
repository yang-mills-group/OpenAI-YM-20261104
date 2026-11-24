import YM.Integration.WilsonOlderFreshGraphPreimageFee
import YM.Integration.WilsonOlderFreshGraphChildDensity

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointStride
open Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
variable {j N per:ℕ}
local notation "stride₄" => ((R.family.path.levels.S.block (j+1)).val:ℝ)^4
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
theorem native (cut:j+1≤N) (late:WilsonMeasuredLandedCurrency.first R simple≤j)
    (room:WilsonOlderFreshGraphPreimageFee.first R simple slow 4≤j+1) :
    0 ≤ stride₄ ∧ 0 < g₀ ∧ stride₄*g₀^2 ≤ 8 := by
  have band:=WilsonMeasuredLandedCurrency.native R simple per cut late
  have bound: stride₄ ≤ R.alloy.B.a.clock.hatBeta ((j+1)+1) := by
    have levels : R.family.path.levels=R.alloy.B.a := rfl
    rw [levels]
    simpa only [Real.rpow_one] using (eventually_atTop.mp (WilsonOlderFreshGraphSlowPreimages.block
      R simple slow 4 (show 0<(1:ℝ) by norm_num))).choose_spec (j+1) room
  exact ⟨by positivity,band.2.1,(mul_le_mul_of_nonneg_right bound (sq_nonneg _)).trans band.2.2.1⟩

theorem rescaled {L x ε g n:ℝ} (q:ℕ) (pos:0≤L) (ep:0≤ε) (gp:0≤g) (np:0≤n)
    (rate:L*g^2≤8) (source:x≤(ε/8)*g^(q+2)*n) : L*x≤ε*g^q*n := by
  calc
    _≤ L*((ε/8)*g^(q+2)*n) := mul_le_mul_of_nonneg_left source pos
    _= (L*g^2)*((ε/8)*g^q*n) := by ring
    _≤ (8:ℝ)*((ε/8)*g^q*n) := mul_le_mul_of_nonneg_right rate (by positivity)
    _= _ := by ring

end YM.Integration.WilsonMeasuredPointStride
end
