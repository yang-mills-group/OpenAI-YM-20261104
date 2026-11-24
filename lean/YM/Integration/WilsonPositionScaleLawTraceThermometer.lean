import YM.Integration.WilsonMaxwellThermometerKineticRunning

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawTraceThermometer
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(simple:G.Simple){Y:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy){arch:Trace.Terrace.Arch R.family}
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
def Every (bias:ℝ→ℝ) : Prop :=
  ∀(Z:WilsonPrescription G)(A:ℝ→Group R.family 6){B:ℕ}, 0<B → Book (f:=f) (l:=Y) (H:=H) A J →
  ∀(axis:ℝ×(ℕ×ℕ)→ℝ), (∀ᶠw in visits, 0<axis w) →
    Tendsto (fun w=>WilsonPositionRawCutoff.thermometer Z F J A w.1 w.2/axis w) visits (𝓝 1) →
    Tendsto (fun w=>axis w/WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B) w.1 w.2) visits (𝓝 1) →
    let θ:=WilsonPositionHomogeneousFrame.reading F J Z
    let rate:=fun r:ℝ=>(Real.sqrt (arch.β (WilsonMeasuredWindow.stop R.family.path.levels simple B r)))⁻¹
    Tendsto (fun r=>θ r/rate r) trail (𝓝 1) ∧ Coupling G θ ∧ (∀ᶠr in trail,0<θ r) ∧
      Tendsto (fun r=>bias r/θ r^2) trail (𝓝 (-(11*G.casimir/(48*Real.pi^2))/2))
theorem original (pace:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F Y arch H)(lead:Leading F J)
    {bias:ℝ→ℝ}(center:TendC F (fun r=>J r 4) bias):Every F J simple (Y:=Y) H (arch:=arch) bias:=by
  intro Z A B hB book axis live panel clock θ rate
  have cash:=WilsonMaxwellThermometerKineticRunning.original Z F J A simple pace hB bliss book lead axis live panel clock
  have sign:∀ᶠr in trail,0<θ r:=by
    apply (cash.1.eventually (Ioi_mem_nhds zero_lt_one)).mono
    intro r measured
    have quot:0<θ r/rate r:=measured
    exact (div_pos_iff.mp quot).elim (fun pos=>pos.1)
      (fun neg=>((not_lt_of_ge (show 0≤rate r from inv_nonneg.mpr (Real.sqrt_nonneg _))) neg.2).elim)
  exact ⟨cash.1,cash.2,sign,center.measures θ cash.2⟩

end YM.Integration.WilsonPositionScaleLawTraceThermometer
end
