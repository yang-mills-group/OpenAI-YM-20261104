import YM.Integration.WilsonReceivedChronologicalFixedBasisFare
import YM.Integration.WilsonCenteredCompactBooking
/-! Joint variation of the actual compact test across each finite family of physical socket returns. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
open Finset Lattice Wilson RG Marker Multi QuadraticLocal Org AllOrder Function MeasureTheory Analysis Table Spec Extraction
open QuadraticLocal.Affinity QuadraticLocal.Earn QuadraticLocal.Mentor PhysicalNext.Repeat.Legato Next.UVStress StressFlux.Matching Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonReceivedCanonicalVersePortfolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(φ:Test n)(r:ℝ)(z:ℕ×ℕ)

def cells:Finset (Sites R z n):=univ.filter fun p=>WilsonCenteredCompactBooking.mass R φ r z p≠0

theorem charged (p:cells R φ r z):WilsonCenteredCompactBooking.mass R φ r z p.val≠0:=
  (Finset.mem_filter.mp p.property).2

theorem total (F:cells R φ r z → ℝ)(bound:ℝ)(positive:0≤bound)(paid:∀p,F p≤bound):
    ∑p:cells R φ r z,‖WilsonCenteredCompactBooking.mass R φ r z p.val‖*F p ≤ (∫y,‖φ y‖)*bound:=by
  let S:=cells R φ r z
  let μ:=WilsonCenteredCompactBooking.mass R φ r z
  have same:(∑p:S,‖μ p.val‖)=∑p∈S,‖μ p‖:=by
    simpa only [Finset.attach_eq_univ] using (Finset.sum_attach S (fun p=>‖μ p‖))
  have cap:(∑p:S,‖μ p.val‖) ≤ ∫y,‖φ y‖:=
    same.le.trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun p _ _=>norm_nonneg (μ p))).trans (WilsonCenteredCompactBooking.variation R φ r z))
  calc
    _ ≤ ∑p:S,‖μ p.val‖*bound :=sum_le_sum fun p _=>mul_le_mul_of_nonneg_left (paid p) (norm_nonneg _)
    _ = (∑p:S,‖μ p.val‖)*bound :=(Finset.sum_mul ..).symm
    _ ≤ _ :=mul_le_mul_of_nonneg_right cap positive

def signed (value:cells R φ r z → ℂ):ℂ:=
  ∑p:cells R φ r z,WilsonCenteredCompactBooking.mass R φ r z p.val*value p

theorem original (value:cells R φ r z → ℂ)(bound:ℝ)(pos:0≤bound)(paid:∀p,‖value p‖≤bound):
    ‖signed R φ r z value‖ ≤ (∫y,‖φ y‖)*bound:=by
  unfold signed
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact total R φ r z (fun p=>‖value p‖) bound pos paid

end YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
end
