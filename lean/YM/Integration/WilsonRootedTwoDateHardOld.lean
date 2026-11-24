import YM.Integration.WilsonRootedTwoDateHardSource
import YM.Integration.WilsonRetainedRequestedBudget
import YM.Integration.WilsonOriginalPointTaste

/-! The original compulsory rows are paid at once on both independent test spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardOld
open Function Finset Lattice RG Wilson Marker Overlay RG3.Script.Picnic
open Extra.Iteration.Comparison LocalComparison LocalComparison.Global WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
  (oldD newD : V → ComparisonDensity.Address.Orbit) {Q : Rep G n}
  (a : Bands (Stock.census V) Q)

local notation "incl" => WilsonRootedTwoDateHardSource.inclusion (D:=newD) oldD
local notation "T" => pullback (@Prod.fst (TestSpace oldD) (TestSpace newD)) (WilsonOriginalPointTaste.representation oldD a)

theorem original {p : BudgetPoint} (fit : HasBudget Q.p p) {w : V → ℝ} {c d κ : ℝ}
    (pos : 0<κ) (live : a.Active) (radial : a.Radial w 0 c d κ) :
    Nonempty (ForcedBudget p (pullback (incl) (T)) w κ d) := by
  obtain ⟨paid⟩ := WilsonRetainedPointBudget.divided oldD a pos live radial
  let h := WilsonRetainedRequestedBudget.restrict fit paid
  refine ⟨⟨h.black,h.black_nonnegative,?_,?_⟩⟩
  · intro z i j U
    exact h.forced z.1 i j U
  · exact h.forcedTotal

end YM.Integration.WilsonRootedTwoDateHardOld
