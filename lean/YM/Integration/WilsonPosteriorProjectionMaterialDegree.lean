import YM.Integration.WilsonPosteriorProjectionBooking
import YM.Integration.FVA1Physical.Wilson.BankDegree
import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.Integration.FVA1Physical.Wilson.BankOrbit

/-! The polynomial degree of the original emitted row on the actual
coarse coordinates, independent of the physical volume. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionMaterial

open Set Filter Finset MeasureTheory Lattice RG YM.Wilson Precision Tree Exterior Push.Uniform
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Cacao MSbar.Mosaic
open MSbar.Rolling MSbar.Bulk MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Measuring
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RG01.Kernel
open scoped BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}

/-- The genuine independently normalized series, transported out of the
joint variables into the actual outgoing coordinates, has the stated degree. -/
theorem degree (A : Issue G) (χ : ChartRatio G) (p m : ℕ) (hm : 1 ≤ m)
    (kind : Kind A.T) (pd : (mold A.pre A.F A.v).PosDef) (profile : Expanse A.T 1 p)
    (b : Site A.f) (s : ℕ) (y δ : ℝ) (T : Nesting G A.f) (paid : BankPaid b y s p m δ T) :
    ∀ i ≤ p, (PowerSeries.coeff i (emittedRows A χ (enterRows A T) p)).totalDegree ≤ bankDegree p m := by
  have entered (i : ℕ) (hi : i ≤ p) : (PowerSeries.coeff i (enterRows A T)).totalDegree ≤ m := by
    rw [enterRows, PowerSeries.coeff_map]
    exact (Rolling.clearD _ _).trans (paid i hi).1
  intro i hi
  rw [emittedRows, PowerSeries.coeff_map]
  exact (Rolling.clearD _ _).trans (normalized_input_degree A χ _ p m hm kind pd profile entered hi)

end YM.Integration.WilsonPosteriorProjectionMaterial
end

