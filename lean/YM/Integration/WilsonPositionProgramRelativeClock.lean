import YM.Integration.MSFixedRatioClockComposition
import YM.Comparison.RG02.Adjacent.Warp

noncomputable section
namespace YM.Integration.WilsonPositionProgramRelativeClock
open Function Filter Finset
open YM.Comparison.RG02 YM.Comparison.RG02.Adjacent
open YM.Comparison.RG02.Moving YM.Comparison.RG02.Moving.Path
open YM.Comparison.RG02.Valence YM.Comparison.RG02.Symmetry
open scoped BigOperators Classical Topology

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Convert a field filed at the receiving clock to that same field in the chronological clock. -/
def relative (K T : UnitCost) : UnitCost :=
  MSFixedRatioClockComposition.compose K.inverseCurve T

theorem same_rows {U V : Display X} (d : ℤ) (r : ℕ) (T : UnitCost)
    (same : ∀i ≤ r, U i=V i) (k : ℕ) : born U T d r k = born V T d r k := by
  funext x
  unfold born
  apply congrArg (fun f : ℝ→ℂ => motion f k)
  funext t
  unfold ages cover
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [same i (mem_range_succ_iff.mp hi)]

theorem restored (r : ℕ) (U : Display X) (p : ℕ→ℤ)
    (bought : Charge r p U) (increasing : Monotone p) (K T : UnitCost)
    (k : ℕ) (hk : k ≤ r) :
    born (born U K 0 r) (relative K T) 0 r k=born U T 0 r k := by
  rw [relative, ←MSFixedRatioClockComposition.measured K.inverseCurve T _
    (affordable 0 r bought K increasing) hk]
  exact same_rows 0 r T (fun i hi=>reverse 0 r bought K.rightInverse i hi) k

end YM.Integration.WilsonPositionProgramRelativeClock
end
