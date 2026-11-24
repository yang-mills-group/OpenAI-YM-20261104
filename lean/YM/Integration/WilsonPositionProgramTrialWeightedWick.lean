import YM.Integration.WilsonPositionProgramTrialFigureWick
import YM.Integration.WilsonPositionProgramTrialMatchedGram

/-! The entire fitted source, including the thermal variations of every active
and unit coordinate, on the same finite Wilson and ghost measure. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialWeightedWick
open Function MeasureTheory MeasureTheory.Measure Lattice Gauge Wilson PhysicalNext.Repeat.Legato
open RG Precision PertExtension PertExtension.Orb PertExtension.Chart PertExtension.Series PertExtension.GaussianScore
open FVA2 FVA2.Trans FVA2.Wilson FVA2.Wilson.FP FVA2.GermLaplace
open WilsonPositionProgramCopyTop (planted normalized)
open WilsonPositionProgramTrialOrbitWick (gauge auxiliary vacuum)
open WilsonThermometerPositionTunedSlope (Columns paid finite)
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (D : ChartRatio G) (p : XSpace.Period)
    {I : Type} [Fintype I] [LinearOrder I] (d : I→ℕ) (o : I → Cover)
    (V : Measure (Cone G p.side)) [IsAddHaarMeasure V]

def word (b : Columns R d) : PowerSeries ℂ := by
  let even:=even_iff_two_dvd.mpr p.even
  let E:=gauge G p.side even
  let power:=Invoice.power V (vacuum G p.side even) (finances E (auxiliary G p.side even))
  exact PowerSeries.mk fun q=>
    (PowerSeries.coeff (q+YM.RegulatorIR.FVAAlt2.Kick.depthF Finset.univ d b)
      (power (volumeK E D (planted R p d o b)) * (power (volumeK E D 1))⁻¹) : ℝ)

theorem window (law : LocalRatio D) (T : p.Tree) :
    finite R d p o T = word R D p d o V := by
  funext b
  ext q
  simpa only [finite,word,PowerSeries.coeff_mk] using
    WilsonPositionProgramTrialFigureWick.original R D law p T d o b V q

theorem original (law : LocalRatio D) (T : p.Tree)
    (v : (i:I)→(R.family.labels.level (d i)).Index→PowerSeries ℂ) :
    paid R d v (finite R d p o T)=paid R d v (word R D p d o V) := by
  rw [window R D p d o V law T]

end YM.Integration.WilsonPositionProgramTrialWeightedWick
