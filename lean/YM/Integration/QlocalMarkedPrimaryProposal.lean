import YM.Integration.LocalComparisonPackets
import YM.Integration.LocalComparisonEnvelope

/-!
PROPOSAL VOCABULARY ONLY — outside certified sources, uncompiled.
No theorem asserts that these records exist. The central full-qlocal handoff
must construct the selected formal model, its canonical reclosure, the actual
output and the common residual from genuine inputs. These definitions only
spell out the marked comparison's norm and aligned-row conclusions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QlocalMarkedPrimaryProposal
open Lattice Wilson RG Marker
open RG3.Script.Picnic
open YM.Integration.LocalComparison Comparison.RG02
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X : Type*} {P : Rep G n} {o : V → Site n}

/-- All three rows are already on a common reexpression. In the central
selection, `formal` must be the actual canonical reclosure of the selected
full formal conditional rendering. This record does not identify an arbitrary
Taste with that rendering. Forced entries are retained separately by the
central full-polynomial equality and original forced-budget conclusion. -/
structure AlignedRegularRows
    (actual formal error : Taste X o P R) : Prop where
  actual_modes : actual.menu.rays = error.menu.rays
  formal_modes : formal.menu.rays = error.menu.rays
  actual_supports : actual.menu.branch = error.menu.branch
  formal_supports : formal.menu.branch = error.menu.branch
  actual_caption_modes : actual.tag = error.tag
  formal_caption_modes : formal.tag = error.tag
  actual_caption_supports : actual.site = error.site
  formal_caption_supports : formal.site = error.site
  regular x i U : actual.menu.regular x i U =
    formal.menu.regular x i U + error.menu.regular x i U
  singleton x v : actual.menu.global x v =
    formal.menu.global x v + error.menu.global x v
  caption x i : actual.score x i = formal.score x i + error.score x i

/-- TeX 14004–14012, 14343–14356, 28838, 28854–28860.
The single majorant per row is selected before the independent test/root.
It uses the exact max-order norm, rather than silently identifying it with
Mix.grain's factorial-sum norm. Global captions and scalar coordinates remain.
Forced norms belong to a separate clause of the same central selection. -/
structure MaxConnectedBudget (p : BudgetPoint) (T : Taste X o P R)
    (radius : V → ℝ) (price : ℝ) where
  active x : (T.leaf x).Active
  radius_pos v : 0 < radius v
  white : ℕ → ℝ
  gold : ℕ → ℝ
  unitBound : V → ℝ
  white_nonnegative i : 0 ≤ white i
  regular_law x i : p.Regular (T.menu.branch i) (T.menu.regular x i)
  regular x i v : v ∈ (T.menu.rays i).val →
    p.supBounds (o v) (T.menu.branch i) (T.menu.regular x i) (white i)
  gold_nonnegative i : 0 ≤ gold i
  caption x i : ‖T.score x i‖ ≤ gold i
  unit_nonnegative v : 0 ≤ unitBound v
  singleton x v : ‖T.menu.global x v‖ ≤ unitBound v
  hit v : ∃ B D : ℝ,
    SumBudget (fun i => if v ∈ (T.menu.rays i).val then
      Poly.toll radius (T.menu.rays i) * p.mass (T.menu.branch i) (white i)
      else 0) B ∧
    SumBudget (fun i => if v ∈ (T.tag i).val then
      Poly.toll radius (T.tag i) * p.mass (T.site i) (gold i)
      else 0) D ∧
    radius v * unitBound v + B + D ≤ price

/-- Only the norm coefficients are divided by the envelope. The physical
polynomial, its output vacuum and its conditional denominator are unchanged.
For disjoint analytic input blocks, `envelope` is their actual product; a slot
product is appropriate only when the original inputs are singleton blocks. -/
structure RelativeConnectedBudget (p : BudgetPoint) (T : Taste X o P R)
    (radius : V → ℝ) (envelope : R.Mode → ℝ) (price : ℝ) where
  positive mode : 0 < envelope mode
  quiet : envelope R.quiet = 1
  budget : MaxConnectedBudget p (priceNormalized envelope T) radius price

/-- The independent-test supremum is inside every common row majorant.
The representation itself was fixed on the full ambient product TestSpace. -/
def IndependentConnectedClause
    (tests : V → ComparisonDensity.Address.Orbit) (p : BudgetPoint)
    (error : Taste (TestSpace tests) o P R)
    (radius : V → ℝ) (envelope : R.Mode → ℝ) (price : ℝ) : Prop :=
  Nonempty (RelativeConnectedBudget p
    (pullback (testInclusion tests) error) radius envelope price)

variable {C : Family G} [Fintype V]

/-- Output-side existence of the literal rendering and its complete formal
coefficient identification. The central target fixes this record before all
later delta/forced-order/test requests. It must also supply the rendering's
address/path envelopes and its same-density canonical reclosure. -/
structure FormalConditionalSelection
    (tests : V → ComparisonDensity.Address.Orbit)
    (Y : Bulk.Chain C.path) (datum : LocalFormal.Datum C R)
    (inputColors : TestSpace tests →
      Bulk.Colors R G (C.side (datum.level + 1) datum.period)) (order : ℕ) where
  model : MarkedPackets tests G (C.side datum.level datum.period) R
  formal : PrescribedPackets Y datum inputColors model order

end YM.Integration.QlocalMarkedPrimaryProposal
end
