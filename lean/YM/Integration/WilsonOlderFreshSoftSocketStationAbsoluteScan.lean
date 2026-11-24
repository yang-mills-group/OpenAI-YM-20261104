import YM.Integration.WilsonOlderFreshSoftSocketStationMeasuredCanvas
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationAbsoluteScan
open Finset Function Lattice RG Wilson MeasureTheory Test Extraction Spec Table
open PhysicalNext.Repeat.Legato
open WilsonCenteredPhysicalPanel
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open WilsonOlderFreshSoftSocketStationPortfolio (reading)
open WilsonPositionThermometerConnected (value)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G)(Φ:Test 3)(r:ℝ)(pos:0≤r)(z:ℕ×ℕ)
local notation "Y" => cells R Φ r z
local notation "μ" => WilsonCenteredCompactBooking.mass R Φ r z
local notation "Face" => Finset (Fin 3)

include pos in
theorem expose (p q:Y→Face→ℂ):
    r^14*‖signed R Φ r z (fun y=>value (p y)-value (q y))‖=
    ‖reading (fun o:Y=>μ o.val) ((r:ℂ)^14) p-reading (fun o:Y=>μ o.val) ((r:ℂ)^14) q‖:=by
  rw [←show ‖(r:ℂ)^14‖=r^14 by rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos],←norm_mul]
  congr 1
  unfold signed WilsonOlderFreshSoftSocketStationPortfolio.reading
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem cap: (∑o:Y,‖μ o.val‖)≤∫y:Points 3,‖Φ y‖:=by
  simpa only [mul_one] using WilsonReceivedChronologicalFixedRoseVariation.total R Φ r z (fun _=>1) (1:ℝ) zero_le_one (fun _=>le_rfl)

include pos in
theorem paid (p q:Y→Face→ℂ){fee:ℝ}(nonneg:0≤fee)
    (roof:∀y:Y,r^14*‖value (p y)-value (q y)‖≤fee):
    ‖reading (fun o:Y=>μ o.val) ((r:ℂ)^14) p-reading (fun o:Y=>μ o.val) ((r:ℂ)^14) q‖≤
      (∫y:Points 3,‖Φ y‖)*fee:=by
  unfold WilsonOlderFreshSoftSocketStationPortfolio.reading
  rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply (le_trans _ (WilsonReceivedChronologicalFixedRoseVariation.total R Φ r z
    (fun y=>r^14*‖value (p y)-value (q y)‖) fee nonneg roof))
  apply sum_le_sum
  intro i _
  rw [←mul_sub,←mul_sub,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos]

end YM.Integration.WilsonOlderFreshSoftSocketStationAbsoluteScan
end
