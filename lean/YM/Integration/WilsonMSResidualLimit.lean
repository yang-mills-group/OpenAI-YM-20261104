import YM.Integration.WilsonWholeLimit
import YM.Integration.PhysicalMSOPECandidate

/-! The literal finite Wilson discrepancy converges to the declared full-horizon
MS residual on the same physical construction. The candidate is the original
finite truncation in the original running frame. No signed rate or identification
of the formal prescription is supplied by this limit application. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMSResidualLimit

open Function Filter Set Spec OPE OPE.Orbits PhysMS
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open EngineeringWeightedReadout PhysicalMSOPECandidate
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (hS : Services C f S)
    (J : ℝ → PhysMS.tower S) {n i D : ℕ} (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (v : Fin n → E C.labels i)

include F hS

/-- The original normalized finite-law product-minus-candidate, with the
unchanged detector exteriors, has exactly the retained weighted MS residual
as its regulator limit. The physical configuration is not replaced by a
separately chosen stencil or a generic perturbation. -/
theorem candidate_tendsto (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (hx : ∀ a, Injective (beside x (positions S (U.listen a)).ofLp)) :
    Tendsto (fun q : ℕ × ℕ => wholeReadout U J r
      (fun a => Wilson.moment (C.beta q.1 q.2)
        (WilsonWholeLimit.detectorDiscrepancy J U v r x
          (candidate J p Z B v N t r) q.1 q.2 a)))
      f.fuse (𝓝 (weightedMSResidual J U p Z B v N t r x)) :=
  WilsonWholeLimit.wholeReadout_discrepancy_tendsto F hS J U v r x
    (candidate J p Z B v N t r) hx

/-- Any independently proved eventual finite-cutoff bound passes to that
same declared MS residual. This theorem does not assert such a bound. -/
theorem candidate_le (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (hx : ∀ a, Injective (beside x (positions S (U.listen a)).ofLp)) (b : ℝ)
    (hb : ∀ᶠ q : ℕ × ℕ in f.fuse,
      ‖wholeReadout U J r (fun a => Wilson.moment (C.beta q.1 q.2)
        (WilsonWholeLimit.detectorDiscrepancy J U v r x
          (candidate J p Z B v N t r) q.1 q.2 a))‖ ≤ b) :
    ‖weightedMSResidual J U p Z B v N t r x‖ ≤ b :=
  WilsonWholeLimit.wholeReadout_discrepancy_le F hS J U v r x
    (candidate J p Z B v N t r) hx b hb

end YM.Integration.WilsonMSResidualLimit
