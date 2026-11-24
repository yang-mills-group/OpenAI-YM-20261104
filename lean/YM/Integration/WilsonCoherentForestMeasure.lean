import YM.Integration.WilsonCoherentReportingForest

/-! The positive measure of the actual block chart, with the original Haar
Jacobian and the complete outer set of free group bonds. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentForestMeasure
open Function Filter Set MeasureTheory Lattice Wilson RG Tree RG16 Precision PertExtension Metric
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentReportingForest
open scoped Classical Topology ENNReal

variable {G : Gauge} {M : Type} [Fintype M] (P : ChartRatio G) (r : ℝ)

def angular (M : Type) [Fintype M] : Measure (M→G.Color) :=
  ((Chart.tangent G M).restrict (ball 0 r)).withDensity (fun x=>ENNReal.ofReal (Chart.jacobian P x))

theorem finite (hp : LocalRatio P) (pr : 0<r) (sr : r<Chart.small G P) :
    IsFiniteMeasure (angular P r M) := by
  have mp:=Chart.Ratio.combined (U:=M) hp sr pr
  have eq : angular P r M univ = ((Chart.physical G M).restrict (Chart.chamber G M r)) univ := by
    simpa only [angular,preimage_univ] using mp.measure_preimage MeasurableSet.univ.nullMeasurableSet
  exact ⟨eq ▸ measure_lt_top _ _⟩

theorem original (hp : LocalRatio P) (f : (M→G.Color)→ℝ) :
    (∫x,f x ∂angular P r M)=∫x in ball 0 r,Chart.jacobian P x * f x ∂Chart.tangent G M := by
  unfold angular
  rw [integral_withDensity_eq_integral_toReal_smul₀ (Chart.Ratio.jacobian_meas hp).ennreal_ofReal.aemeasurable (Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change (ENNReal.ofReal (Chart.jacobian P x)).toReal * f x = Chart.jacobian P x * f x
  rw [ENNReal.toReal_ofReal (Chart.jacobian_nonneg (P:=P) x)]

variable {c f : Side} {S : StepData c f} (T : Forest S.ratio) (B : Finset T.Free)
local notation "E" => moving T B
abbrev Outer := {i:T.Free|i∉E}
abbrev Sample (G:Gauge) := (Outer T B→G.El) × (↥E→G.Color)

def law : Measure (Sample T B G) :=
  (Measure.pi (fun _ : Outer T B=>G.probHaar)).prod (angular P r (↥E))

theorem funded (hp : LocalRatio P) (pr : 0<r) (sr : r<Chart.small G P) : IsFiniteMeasure (law P r T B) := by
  letI := finite P r hp pr sr (M:=↥E)
  unfold law
  infer_instance

theorem reading (hp : LocalRatio P) (pr : 0<r) (sr : r<Chart.small G P)
    (F : Sample T B G → ℝ) (hF : Integrable F (law P r T B)) :
    (∫z,F z ∂law P r T B)=∫v, (∫x in ball 0 r,
      Chart.jacobian P x * F (v,x) ∂Chart.tangent G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  letI := finite P r hp pr sr (M:=↥E)
  rw [law,integral_prod _ hF]
  apply integral_congr_ae
  exact ae_of_all _ fun v=>original P r hp fun x=>F (v,x)

end YM.Integration.WilsonCoherentForestMeasure
