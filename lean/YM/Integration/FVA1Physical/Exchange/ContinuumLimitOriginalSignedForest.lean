import YM.Integration.FVA1Physical.Exchange.ContinuumLimitOriginalMixedWilson
import YM.Comparison.RG02.Integral.Comparison
import YM.Comparison.RG02.Laplace.Fleet

/-! Actual finite-regulator push on an arbitrary incoming physical density.
The native older-input, complement, Gaussian Taylor, and excluded-mask
pieces are centered against one independently normalized formal response.
The exact weighted identity retains cancellations across those signed terms. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.OriginalMixedWilson
open Function Finset Filter MeasureTheory RG Wilson Gauge Precision Tree Lattice Exterior
open Next.SectorChange PowerSeries PertExtension.Series PertExtension.Series.Tested
open Comparison.RG02 Order Marker Multi CommonCover.JetCumulants
open Integral Actual Push.SectorMeasure
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
    {P : PathData G} {O : ChartRatio G} {I : Type} [DecidableEq I] [Fintype I]
    {R : Census I} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (ρ : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1) (r : ℕ)

def formalForecast (g : ℝ) : Poly R :=
  value (g : ℂ) (series R r (depot R (raw K F ρ W x)))

theorem forecast_nonzero : ∀ᶠ g in Laplace.along,
    (formalForecast K F ρ W x r g).part R.quiet ≠ 0 := by
  let Y := Bulk.Fk K F ρ W x r
  have hy : Laplace.Trial (Laplace.detail Y R.quiet)
      (fun g : ℝ => (value (g:ℂ) Y).part R.quiet) r := by
    unfold Laplace.Trial
    simp_rw [←Laplace.tests]
    rw [show (fun g => peval (Laplace.detail Y R.quiet) r g) =
      peval (Laplace.detail Y R.quiet) r from rfl, sub_self]
    exact Laplace.bill_zero
  have hn := Laplace.trial_sample hy
  rw [Laplace.tests_origin Y (Bulk.fk_unit ..)] at hn
  have fl := hn.eventually_ne (show (1:ℂ) ≠ 0 from one_ne_zero)
  change ∀ᶠ g : ℝ in Laplace.along, (value (g : ℂ) (series R r (depot R (raw K F ρ W x)))).part R.quiet ≠ 0
  rwa [←gaussian_table]

omit [Fintype I] in
private theorem centered {X Y E : Poly R} {z : ℂ} (h : X = z • Y + E)
    (hx : X.part R.quiet ≠ 0) (hy : Y.part R.quiet ≠ 0) :
    X.part R.quiet • (unitScale X - unitScale Y) = E - E.part R.quiet • unitScale Y := by
  rw [←scaled_reconstruct hx]
  rw [h,Poly.part_plus,Poly.part_smul,add_smul,←smul_smul z (Y.part R.quiet),
    scale_value hy]
  abel

/-- The original physical push on arbitrary gauge-invariant, leaf-integrable
incoming density. Its exact error contains the actual signed defect of all
sectors at one normalized Wilson table, measured at the original test weights. -/
theorem centered_physical_price (g c₀ : ℝ) (D : Lit R (Config G f))
    (A : S.Choices → Set (F.Slice G)) (hA : ∀ u, Trust K F u g x (A u))
    (hg : 0 < g) (hw : Bulk.Well W) (hd : Leaf.All D) (invariant : GaugeInvariant D)
    (realDen : (Actual.Push S (temperature g) D (sample g x)).part R.quiet ≠ 0)
    (formalDen : (formalForecast K F ρ W x r g).part R.quiet ≠ 0) (weights : I → ℝ) :
    let X := Actual.Push S (temperature g) D (sample g x)
    let Y := formalForecast K F ρ W x r g
    let E := leftover K F g c₀ x W D r A
    ‖X.part R.quiet‖ * Poly.price weights (unitScale X - unitScale Y) =
      Poly.price weights (E - E.part R.quiet • unitScale Y) := by
  intro X Y E
  have decomposition : X = (office K F ρ g c₀ x : ℂ) • Y + E := by
    dsimp only [X,Y,E,formalForecast]
    rw [←gaussian_table]
    exact Integral.compare K F ρ g c₀ x W D r hg hw hd A hA invariant
  have paid := congrArg (Poly.price weights) (centered decomposition realDen formalDen)
  simpa only [Poly.adapted] using paid

end YM.Integration.FVA1Physical.OriginalMixedWilson
