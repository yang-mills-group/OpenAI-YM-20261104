import YM.Integration.WilsonReportingAbsoluteInletLiveRun
import YM.Integration.WilsonThermometerSmallPanelMoment

/-! The three filed detector apertures on the actual physical Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalPanelDates
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

variable {G : Gauge}

theorem original (R : Run G) (paid : WilsonReportingAbsoluteInletLiveRun.PanelDates R) :
    ∃ (K : Binding R.family) (O : HaarBudget G) (z : ℕ → ℝ),
      K.prices = R.metals.K ∧
      (∀ i d, i ≤ d → MergeProof.Accent.generator G i ≤ z d) ∧
      ∀ d, FiresSky K R.makes O (Next.Foundations.chart G) d (z d) := by
  obtain ⟨O,z,hz,issued⟩ := paid.panels
  have initial := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories
    R.doors R.makes R.carries R.books).1
  obtain ⟨_,_,_,_,_,K,_,rates,_⟩ := initial.reception
  exact ⟨K,O,z,rates,hz,issued R.family rfl K rates R.makes
    (Next.Rank.East.enclosing R.stories initial.freight R.makes)⟩

end YM.Integration.WilsonThermometerOriginalPanelDates
