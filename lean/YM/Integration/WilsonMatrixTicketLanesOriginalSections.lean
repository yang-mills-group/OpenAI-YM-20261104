import YM.FullVolume.Cross
import YM.UVExt.StrongProduce

/-! Recover the actual finite section bills and microscopic source room on
the named physical run before choosing its marked projection. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesOriginalSections
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open Set Function MeasureTheory Filter Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels Maxwell
open YM.MergeProof
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Dash Spec UVExt.Slots
variable {G : Gauge}

theorem purchased (R : Run G) :
    ∃ (V : ∀ d, SectionData (R.family.labels.level d)) (W : Push.Mark.Weave G),
      Chateau R.b R.Q R.T R.t R.stories R.doors ∧ Stock.Tabs R.family.path.levels ∧
      Fridge R.family (Bandage.far R.family.path.levels) (Bandage.fly R.family.path.levels) ∧
      (∀ d, Push.Mark.Portfolio R.family.params (V d) (W d)) ∧
      ∀ d, ∃ a : ℕ → ℝ, Braze (C := R.family) (V d) a := by
  obtain ⟨owned,tabs,_,fridge,_,_,⟨k,minimum,V,W,delay,sections,paper,floor⟩,_⟩ :=
    R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  exact ⟨V,W,owned,tabs,fridge,sections,
    (PhysicalNext.Repeat.Legato.duty R.T R.t R.stories R.accepts delay paper floor).1⟩

end YM.Integration.WilsonMatrixTicketLanesOriginalSections
