import YM.Integration.RunFormalChain
import YM.RGComparison.Core16.Trajectory
import YM.FVA2.FundingOffer

/-! Coefficients of the actual finite Wilson descent at its flat boundary.  The
outer solenoid receives the full older ticket under its own inherited data. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentTraversal
open Function Lattice Wilson RG Tree Precision PertExtension Chart PowerSeries
open PhysicalNext.Repeat.Legato
open PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router
open RGComparison.Core16 Descent FVA2 FVA2.CityHistory
open scoped ContDiff

variable {G : Gauge} (R : Run G) {per N : ℕ}
variable (Z : Slices R.family.path.levels per)

theorem room {i : ℕ} (hi : i ≤ N) :
    (∀ t, i ≤ t → t < N → Bid.Larger (G:=G) (R.family.path.levels.clock.op t per)) →
    (traversal Z hi).Room G := by
  induction hi using Nat.decreasingInduction with
  | self => intro _; rw [traversal_self]; trivial
  | of_succ t ht ih =>
    intro larger
    rw [traversal_push Z ht]
    exact ⟨larger t le_rfl ht, ih (fun j h hj => larger j (Nat.le_trans (Nat.le_succ t) h) hj)⟩

variable {i : ℕ} (hi : i < N)
local notation "S" => R.family.path.levels.clock.op i per
local notation "D" => traversal Z hi
local notation "B" => Descent.push S (Z i) D

/-- A coefficient identity before an estimate or a change of kinetic clock.
The offset schedule is fixed in the same beta units on both sides. -/
theorem coefficient (larger : Bid.Larger (G:=G) S) (previous : (D).Room G)
    (tag : (S).Choices) (tags : (D).Tags) (offsets : ℕ → ℝ)
    (O : Config G (R.family.path.levels.S.side N per) → ℝ)
    (smooth : ContDiffAt ℝ ∞ (O ∘ expLinks G _) 0) (e : ℕ) :
    Descent.ranking R.metals.O B offsets O e =
      coeff e (Stack.read 0 (solenoid S (Z i) D tags tag R.metals.O (Delay.stones offsets)
        larger previous (boost (gate G S (Z i))
          (skyread R.metals.O D tags previous (parentZ (Delay.stones offsets)) (exPay O))))) := by
  have paid := accrued R.metals.O R.alloy.B.ratio B ⟨larger, previous⟩
    (tag,tags) offsets smooth
  rw [atop S (Z i) D tags tag R.metals.O (Delay.stones offsets)
    R.alloy.B.ratio larger previous (exPay O)] at paid
  simpa only [coeff_mk] using congrArg (coeff e) paid

/-- The source on the left is a compact Wilson conditional normalized by its
whole original vacuum, at the genuine flat boundary and each fixed regulator. -/
theorem observed (larger : Bid.Larger (G:=G) S) (previous : (D).Room G)
    (tag : (S).Choices) (tags : (D).Tags) (offsets : ℕ → ℝ)
    (O : Config G (R.family.path.levels.S.side N per) → ℝ)
    (tested : (B).Testable O) (smooth : ContDiffAt ℝ ∞ (O ∘ expLinks G _) 0) :
    Aspiration (fun g => (B).conditioned (Descent.offset offsets g) O 1)
      (fun e => coeff e (Stack.read 0 (solenoid S (Z i) D tags tag R.metals.O
        (Delay.stones offsets) larger previous (boost (gate G S (Z i))
          (skyread R.metals.O D tags previous (parentZ (Delay.stones offsets)) (exPay O)))))) := by
  have read := Descent.coefficient_formula R.metals.O R.alloy.B.ratio offsets
    (h := (show (B).Room G from ⟨larger, previous⟩)) tested
  have coeffs := funext (coefficient R Z hi larger previous tag tags offsets O smooth)
  rwa [← coeffs]

end YM.Integration.WilsonCoherentTraversal
end
