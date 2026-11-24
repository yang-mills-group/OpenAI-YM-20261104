import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
/-! The entrance on each true compact node may have its own absolute cash. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseTestVariation
open Finset Lattice Wilson RG Marker Multi QuadraticLocal Org AllOrder Function MeasureTheory Analysis Table Spec Extraction
open QuadraticLocal.Affinity QuadraticLocal.Earn QuadraticLocal.Mentor PhysicalNext.Repeat.Legato Next.UVStress StressFlux.Matching Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonReceivedCanonicalVersePortfolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(φ:Test n)(r:ℝ)(z:ℕ×ℕ)


open WilsonReceivedChronologicalFixedRoseVariation (cells signed total)
theorem original (value:cells R φ r z → ℂ)(entry:cells R φ r z → ℝ)(cost:ℝ)(nonnegative:0≤cost)
    (bounded:∀p,‖value p‖≤entry p+cost):
    ‖signed R φ r z value‖≤ (∑p:cells R φ r z,‖WilsonCenteredCompactBooking.mass R φ r z p.val‖*entry p)+
      (∫y,‖φ y‖)*cost:=by
  let w:cells R φ r z → ℝ:=fun p=>‖WilsonCenteredCompactBooking.mass R φ r z p.val‖
  calc
    ‖signed R φ r z value‖ ≤ ∑p:cells R φ r z,w p*‖value p‖:=by
      unfold WilsonReceivedChronologicalFixedRoseVariation.signed
      simp only [w,←norm_mul]
      exact norm_sum_le _ _
    _ ≤ ∑p:cells R φ r z,w p*(entry p+cost):=
      sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (bounded p) (norm_nonneg _))
    _ = (∑p:cells R φ r z,w p*entry p)+(∑p:cells R φ r z,w p*cost):=by simp only [mul_add,sum_add_distrib]
    _ ≤ _:=add_le_add le_rfl (total R φ r z (fun _=>cost) cost nonnegative (fun _=>le_rfl))
end YM.Integration.WilsonReceivedChronologicalFixedRoseTestVariation
end
