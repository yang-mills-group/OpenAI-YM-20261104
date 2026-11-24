import YM.Integration.WilsonCoherentMayerCaptureRent
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! The unweighted source accuracy on the original real-radius close calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseSourceCalendar
open Filter Lattice RG OPE OPE.Log Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open WilsonLimitConstruction RG05Readout Many Halls Records Chalice Address Native
open QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (hG:G.Simple)
local notation "first" => WilsonCloseCaptureCalendar.lower R
local notation "last" => WilsonCloseCaptureCalendar.reported R hG
local notation "β̂" => R.alloy.B.a.clock.hatBeta


include hG in
theorem reporter_fee {fee ε:ℝ} (hn : 0 ≤ fee) (ep : 0 < ε) :
    ∀ᶠ b:ℕ in atTop, ∀ N per, b ≤ N → fee*regulatorRun R.family N per b ≤ ε := by
  filter_upwards [(RG01.Physical.hats hG R.alloy.B.a).eventually_ge_atTop (2*((fee/ε)^2+1))]
    with b warm N per top
  let y := R.family.path.β N per b
  have base := (R.makes.wilson.represents N per b top).band.1
  change β̂ b/2 ≤ y at base
  have yp : 0 < y := by nlinarith only [warm,base,sq_nonneg (fee/ε)]
  have price : fee/ε ≤ Real.sqrt y := (Real.le_sqrt (div_nonneg hn ep.le) yp.le).mpr (by linarith only [base,warm])
  change fee*(Real.sqrt y)⁻¹ ≤ ε
  rw [←div_eq_mul_inv,div_le_iff₀ (Real.sqrt_pos.mpr yp)]
  simpa only [mul_comm] using (div_le_iff₀ ep).mp price

private theorem settle {g fee ε:ℝ} (gp:0<g) (cold:g≤1) (hp:0≤fee) (paid:fee*g≤ε)
    {q raw load : ℕ} (order:load+q+2≤raw) :
    fee*(g^(-(1/2:ℝ))*g^(-(1/2:ℝ)))*g^(raw-load) ≤ ε*g^q := by
  have inv : g^(-(1/2:ℝ))*g^(-(1/2:ℝ)) = g⁻¹ := by
    rw [←Real.rpow_add gp]
    norm_num [Real.rpow_neg_one]
  rw [inv]
  have small := pow_le_pow_of_le_one gp.le cold (show q+2 ≤ raw-load by omega)
  calc
    _ ≤ fee*g⁻¹*g^(q+2) := mul_le_mul_of_nonneg_left small (mul_nonneg hp (inv_nonneg.mpr gp.le))
    _ = fee*g*g^q := by rw [pow_add]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right paid (pow_nonneg gp.le _)

/-- All entrance floors precede both regulators. Restoring both birth radii and the entire close
calendar therefore buys every requested order on the physical reporting range. -/
theorem original (slow:WilsonWindowReportingPace.Slow R.kit) {cap:ℕ} (wide:4<cap)
    (entrance raw load q : ℕ) (order : load+q+2≤raw)
    {fee ε : ℝ} (hn : 0≤fee) (ep : 0<ε) :
    ∀ᶠ r:ℝ in trail, let m:=first r+1
      let b:=last cap r
      entrance ≤ m ∧ m < b ∧ CaptureW R.family m b r cap ∧ PaceR.Close R 1 ((cap+2:ℕ):ℝ) m b ∧
      ∀ N per, b ≤ N → let g:=regulatorRun R.family N per b
        0<g ∧ 3*g≤1 ∧ fee*(g^(-(1/2:ℝ))*g^(-(1/2:ℝ)))*g^(raw-load) ≤ ε*g^q := by
  obtain ⟨low,high,_⟩ := WilsonCloseCaptureCalendar.dates R hG slow wide
  filter_upwards [WilsonCoherentMayerCaptureRent.span R hG slow wide,
    low.grows.eventually_ge_atTop entrance,
    high.grows.eventually (WilsonReceivedClosePhysicalBirths.cool R hG),
    high.grows.eventually (reporter_fee R hG hn ep)] with r span gate cold feePaid
  refine ⟨gate.trans (Nat.le_succ _),span.1,span.2.1,span.2.2,?_⟩
  intro N per hb
  have chilled:=cold N per hb
  refine ⟨chilled.1,chilled.2,?_⟩
  apply settle chilled.1 (by linarith only [chilled.1,chilled.2]) hn _ order
  exact feePaid N per hb

end YM.Integration.WilsonReceivedCloseSourceCalendar
