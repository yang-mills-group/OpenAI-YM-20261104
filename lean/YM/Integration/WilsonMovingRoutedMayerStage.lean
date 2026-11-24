import YM.Integration.WilsonLongContactMayerBooking
import YM.Integration.WilsonGaussianDeterminantTender
import YM.Integration.WilsonCoherentMayerCovarianceCalendar
import YM.RGLocalTaylor.Mayer.Calendar

/-! The particular submitted booking carries the marked cluster course,
the original covariance tariff, and the caller's prescribed analytic estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingRoutedMayerStage
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical
open RGLocalTaylor RGLocalTaylor.Laminate
open WilsonLimitConstruction WilsonLimitConstruction.FundedPredictionSupply WilsonGaussianDeterminantTender
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMarkedExistence GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared

def calendar (G : Gauge) (δ : Charity.RG12.Decal G) : Charity.RG12.Decal G :=
  (RGLocalTaylor.Mayer.decal G).paired ((WilsonCoherentMayerCovarianceCalendar.decal G).paired δ)

/-- Open the actual marked, covariance and user tariffs on one specific
booking of the original window, with its physical block and order unchanged. -/
theorem shared {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (J : Request V) (χ : Chi)
    (δ : Charity.RG12.Decal G) (ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder)
    {P : Teller G} (Q : ConnectedActivityE6.Target G P) (C : Libretto G J.outputFieldOrder)
    (b : Booking G) (D : Patch) (x γ : ℝ)
    (award : WilsonLongContactSectorProtection.Offered J ρ (joined G J χ (calendar G δ)) Q C b D x γ) :
    (RGLocalTaylor.Mayer.decal G).rub (teller J P) (target J Q) (expense J Q) D.L b.W b.μ b.order
      (teller J P).below D.J x ∧
    WilsonCoherentMayerCovarianceCalendar.deviation G D.L b.order ≤ 1 + Real.log (betaF G x D.L) ∧
    δ.rub (teller J P) (target J Q) (expense J Q) D.L b.W b.μ b.order (teller J P).below D.J x :=
  award.window.analytic.2.2

theorem at_date {G : Gauge} (R : Run G) {V : Type} [DecidableEq V] [Fintype V]
    (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder)
    (test : WilsonCoherentMayerElection.Demand G)
    (sold : WilsonLongContactMayerBooking.Sold J (joined G J χ (calendar G δ)) extra γ ρ test R.kit)
    (m : ℕ) (first : R.metals.p.first ≤ R.alloy.B.a.clock.J m) :
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let b := sold.choose j i
    let S := Clockwork.patch R.rolls (step_paid R.alloy.B.a m) first
    let x := R.alloy.B.a.clock.hatBeta m
    b.record.ε ≤ 1/4 ∧
      ρ (target J (R.kit.target j i)) S (libretto J R.metals.p R.metals.K j i) b x ∧
      test (R.kit.target j i) S b j x ∧
      WilsonCoherentMayerCovarianceCalendar.deviation G (R.rolls.L j) b.order ≤
        1 + Real.log (R.alloy.B.a.clock.hatBeta (m+1)) := by
  let j := R.alloy.B.a.clock.J (m+1)
  let i := R.alloy.B.a.clock.J m
  let x := R.alloy.B.a.clock.hatBeta m
  have W := sold.choose_spec.2 j x (R.alloy.B.valid.pays m) i (step_paid R.alloy.B.a m) first
  refine ⟨W.1.small,W.1.forecast,W.2.2.2,?_⟩
  have due := W.1.window.analytic.2.2.2.1
  change WilsonCoherentMayerCovarianceCalendar.deviation G (R.rolls.L j) (sold.choose j i).order ≤
    1 + Real.log (betaF G x (R.rolls.L j)) at due
  simpa only [j,x,← beta_eq R.alloy.B.valid m] using due

theorem measured {G : Gauge} (R : Run G) {V : Type} [DecidableEq V] [Fintype V]
    (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder)
    (test : WilsonCoherentMayerElection.Demand G)
    (sold : WilsonLongContactMayerBooking.Sold J (joined G J χ (calendar G δ)) extra γ ρ test R.kit) :
    ∀ᶠ m : ℕ in Filter.atTop,
      let j := R.alloy.B.a.clock.J (m+1)
      let b := sold.choose j (R.alloy.B.a.clock.J m)
      WilsonCoherentMayerCovarianceCalendar.deviation G (R.rolls.L j) b.order ≤
        1 + Real.log (R.alloy.B.a.clock.hatBeta (m+1)) := by
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop R.metals.p.first] with m first
  exact (at_date R J χ δ extra γ ρ test sold m first).2.2.2

end YM.Integration.WilsonMovingRoutedMayerStage
end
