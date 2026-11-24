import YM.Integration.WilsonOriginalMicroscopicEntrancePeerRefund
import YM.Integration.WilsonThermometerAncestralCalendar
import YM.Integration.WilsonThermometerUnitFilingChartFee

/-! At the original measured entrance the chart correction costs only a fixed
power determined by the already declared maximum physical grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePeerChart
open QuadraticLocal QuadraticLocal.Earn Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push
open Ac GridApprox.Nil MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open RG05Readout RG05Readout.Native RG05Readout.Many PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow Motion Bandage Next.Foundations Trace.Physical.GermGraph Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP QuadraticLocal.Advent
open WilsonThermometerUnitFilingFieldRange
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family
local notation "heat" => R.family.path.levels.clock.hatBeta
local notation "T₀" => |WilsonOriginalCompanionLowerPeer.tariff|
local notation "E₀" => WilsonMeasuredCompanionSoft.expense 1

def tariff (G:Gauge)(d:ℕ):ℝ:=T₀+(6+basisCost G d)*E₀

theorem original (simple:G.Simple)(d K q r:ℕ)(grade:d≤K):∀ᶠ j₀:ℕ in atTop,∀N p f (_:j₀≤f)(_:f≤N),
    ∀ m k (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G ((CF).side i p)),
    Concourse R.alloy R.kit R.T π Γ m N p k Ψ → m≤f →
    ∀V w:ℝ,0≤V → ∀F:ℂ,
    w*‖F‖≤((heat f)^(q+K))⁻¹*V*(T₀*(regulatorRun (CF) N p f)^r+
      (|cost G d ((CF).path.rep N p f).p.threshold|+1)*E₀) →
    w*‖F‖≤((heat f)^q)⁻¹*V*tariff G d:=by
  filter_upwards [WilsonThermometerAncestralCalendar.weak R simple] with j₀ date
  intro N p f start live m k π Γ Ψ path floor V w vp F bill
  let H:=heat f
  let P:=(CF).path.rep N p f
  have atH:1≤H:=((CF).path.levels.fits.delayed f).le
  have Hp:0<H:=zero_lt_one.trans_le atH
  have ep:0≤E₀:=by unfold WilsonMeasuredCompanionSoft.expense;positivity
  have bp:0≤basisCost G d:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have cp:0≤cost G d P.p.threshold:=by
    change 0≤1+basisCost G d*(max 1 P.p.threshold⁻¹)^d
    exact add_nonneg zero_le_one (mul_nonneg bp (pow_nonneg (le_max_of_le_left zero_le_one) _))
  have rep:= (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ path floor live).1
  have safe:=WilsonThermometerUnitFilingChartFee.original R π Γ Ψ path d floor live
  rw [←rep] at safe
  have shifted:|cost G d P.p.threshold|+1≤(6+basisCost G d)*H^K:=by
    rw [abs_of_nonneg cp]
    apply le_trans _ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ atH grade) (by linarith only [bp]))
    linarith only [safe]
  have g:=date N p f start live
  have paid:T₀*(regulatorRun (CF) N p f)^r ≤ T₀*H^K:=by
    exact mul_le_mul_of_nonneg_left ((pow_le_one₀ g.1.le g.2).trans (one_le_pow₀ atH)) (abs_nonneg _)
  apply bill.trans
  calc
    (H^(q+K))⁻¹*V*(T₀*(regulatorRun (CF) N p f)^r+(|cost G d P.p.threshold|+1)*E₀) ≤
        (H^(q+K))⁻¹*V*(T₀*H^K+((6+basisCost G d)*H^K)*E₀):= by
      exact mul_le_mul_of_nonneg_left (add_le_add paid (mul_le_mul_of_nonneg_right shifted ep))
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg Hp.le _)) vp)
    _ = (H^q)⁻¹*V*tariff G d:=by
      unfold tariff
      rw [pow_add]
      field_simp [Hp.ne']

end YM.Integration.WilsonOriginalMicroscopicEntrancePeerChart
end
