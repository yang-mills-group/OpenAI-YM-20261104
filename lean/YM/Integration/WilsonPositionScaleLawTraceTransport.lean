import YM.Integration.WilsonPositionScaleLawTraceThermometer
import YM.Integration.WilsonPositionScaleLawPhysicalThermalRatio

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawTraceTransport
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
    (∀ [_window:WilsonPositionScaleLawWindow.RangeSpec],
      Tendsto (fun z:ℝ×WilsonPositionScaleLawWindow.Ratio=>θ z.1/θ (z.2.val*z.1)) WilsonPositionScaleLawWindow.sweep (𝓝 1)) ∧
      ∀ {I:Type} {l:Filter I} (r s:I→ℝ), Tendsto r l trail → Tendsto s l trail →
        Tendsto (fun i=>(bias (r i)/bias (s i))/(θ (r i)/θ (s i))^2) l (𝓝 1)

theorem original {bias:ℝ→ℝ} (booked:WilsonPositionScaleLawTraceThermometer.Every F J simple (Y:=Y) H (arch:=arch) bias):
    Every F J simple (Y:=Y) H bias := by
  intro Z A B hB book axis live panel dates θ
  obtain ⟨_,thermal,sign,paid⟩ := booked Z A hB book axis live panel dates
  refine ⟨fun {_}=>WilsonPositionScaleLawPhysicalThermalRatio.signed simple thermal sign,?_⟩
  intro I l r s near far
  have c:G.casimir≠0 := (Gauge.casimir_pos simple).ne'
  have k: -(11*G.casimir/(48*Real.pi^2))/2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) c)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)))) (by norm_num)
  exact WilsonPositionScaleLawPhysicalThermalRatio.measured k paid r s near far

end YM.Integration.WilsonPositionScaleLawTraceTransport
end
