import YM.Integration.WilsonMaxwellThermometerKineticRelease
import YM.Pert.Asymptotics.RawAxis

/-! The absolute one-loop unit of the positive physical position coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticLog
open Filter Function Spec RG Source Maxwell Extraction Table Trace.Pilot PhysMS Climb OPE OPE.Orbits
open Lattice Wilson PhysicalNext.Repeat.Legato FVA2.Register FVA2.Scale Pert.Asymptotics
open XSpace XSpace.Structure1 XSpace.Cirrus XSpace.Normalize WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G : Gauge}

def unit (G : Gauge) (r : ℝ) : ℝ := (Real.sqrt (2*b0 G*Real.log r⁻¹))⁻¹

theorem normalization : 2*(11*G.casimir/(48*Real.pi^2))=G.slopeConstant := b0_normalizes

theorem running (simple : G.Simple) {t : ℝ→ℝ} (realized : Coupling G t) :
    Tendsto (fun r=>t r/unit G r) trail (𝓝 1) := by
  have pos : 0<2*b0 G := b0_normalizes (G:=G) ▸ G.slopeConstant_pos simple
  have limit := (tendsto_const_nhds (x:=2*b0 G)).mul realized.running
  rw [← b0_normalizes (G:=G),mul_inv_cancel₀ pos.ne'] at limit
  have root := (Real.continuous_sqrt.tendsto (1:ℝ)).comp limit
  rw [Real.sqrt_one] at root
  refine root.congr' ?_
  filter_upwards [realized.positive,PhysMS.to_log_zoom.eventually_gt_atTop 0] with r here logpos
  change Real.sqrt (2*b0 G*(LogV r*(t r)^2))=t r/(Real.sqrt (2*b0 G*LogV r))⁻¹
  rw [← mul_assoc,Real.sqrt_mul (mul_nonneg pos.le logpos.le),Real.sqrt_sq here.le,
    div_inv_eq_mul,mul_comm]

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (Z : WilsonPrescription G) (F : Final R.family f S) (J : ℝ→tower S) (A : ℝ→Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    (simple : G.Simple) {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit)
    (fine index : ℝ→ℕ) (bliss : Bliss F Y arch H)
    (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index
local notation "earned" => WilsonMaxwellThermometerKineticRequest.earned (Y:=Y) Z F J A simple (B:=B) fine index

include hB pace bliss book lead in
theorem original (schedule : enrolled) (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)
    (first : earned d φ v 1) :
    (∀ᶠ r in trail,0<θ r) ∧ Tendsto
      (fun r=>θ r/(Real.sqrt (2*(11*G.casimir/(48*Real.pi^2))*Real.log r⁻¹))⁻¹) trail (𝓝 1) := by
  have receipt := (WilsonMaxwellThermometerKineticRelease.running Z F J A simple hB pace fine index
    bliss book lead schedule d φ v first).2.2
  exact ⟨receipt.positive,running simple receipt⟩

end YM.Integration.WilsonMaxwellThermometerKineticLog
