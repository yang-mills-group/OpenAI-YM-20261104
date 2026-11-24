import YM.Integration.WilsonOlderFreshSoftSocketStationAbsoluteScan
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationUnscaledScan
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

/-- The input already contains its engineering normalization; the original cell masses still use r. -/
theorem expose (p q:Y→Face→ℂ):
    ‖signed R Φ r z (fun y=>value (p y)-value (q y))‖=
    ‖reading (fun o:Y=>μ o.val) 1 p-reading (fun o:Y=>μ o.val) 1 q‖:=by
  apply congrArg norm
  simp only [signed,WilsonOlderFreshSoftSocketStationPortfolio.reading,one_mul,mul_sub,sum_sub_distrib]

theorem paid (p q:Y→Face→ℂ){fee:ℝ}(nonneg:0≤fee)
    (roof:∀y:Y,‖value (p y)-value (q y)‖≤fee):
    ‖reading (fun o:Y=>μ o.val) 1 p-reading (fun o:Y=>μ o.val) 1 q‖≤
      (∫y:Points 3,‖Φ y‖)*fee:=by
  rw [←expose]
  unfold signed
  exact (norm_sum_le ..).trans (by
    simp only [norm_mul]
    exact WilsonReceivedChronologicalFixedRoseVariation.total R Φ r z
      (fun y=>‖value (p y)-value (q y)‖) fee nonneg roof)

end YM.Integration.WilsonOlderFreshSoftSocketStationUnscaledScan
end
