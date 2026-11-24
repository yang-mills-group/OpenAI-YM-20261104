import YM.Integration.WilsonPosteriorProjectionScalarChart
import YM.Integration.FVA1Physical.Wilson.InletFVA2

/-! The actual bare stencil after the genuine Wilson input chart is
precisely the independently filed finite field bank on that same issue. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionInletClock
open Function Lattice RG YM.Wilson Source Precision Tree Exterior
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Cacao MSbar.Bakery.Film MSbar.Rolling MSbar.Bulk
open MSbar.Lis MSbar.Mosaic MSbar.CrossH Push.Uniform FVA1Physical.Wilson FVA1Physical.Round2.Curvature RGComparison.Core16.Spool
open scoped Classical
variable {G : Gauge} {I : Type} [Fintype I]

theorem taste_input (J : I → RGComparison.Core16.Spool.Lamp G) (A : Issue G) (χ : ChartRatio G)
    (p : ℕ) (o : I → Site A.f) (part : Bool) :
    (fun z => MSbar.Bakery.taste p (MSbar.Bakery.Portal.picture z (emittedRows A χ (enterRows A (stencilInlet J o part)) p)) A.fClock) =
      clue (renderedPolynomial (emittedRows A χ (jointFieldBank J A o part) p) p A.fClock) := by
  rw [inlet_FVA2]
  funext z
  exact (WilsonPosteriorProjectionScalarChart.read p _ A.fClock z).symm

end YM.Integration.WilsonPosteriorProjectionInletClock
end

