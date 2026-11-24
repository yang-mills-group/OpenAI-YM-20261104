import YM.Integration.WilsonCoherentTraversal

/-! The positive physical map at every boundary and the complete independently
computed flat formal return on any number of original consecutive steps. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentInheritedRenderer
open Function Lattice Wilson RG Tree Precision PertExtension Chart PowerSeries
open PhysicalNext.Repeat.Legato
open PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router
open RGComparison.Core16 Descent FVA2 FVA2.CityHistory
open scoped ContDiff

open RGComparison.Core16.Descent

variable {G : Gauge} (R : Run G) {per N : ℕ}
variable (F F' : Slices R.family.path.levels per) {i : ℕ} (hi : i ≤ N)
local notation "D" => traversal F hi
local notation "D'" => traversal F' hi
local notation "n" => R.family.side N per

theorem output {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (β : ℕ → ℝ)
    (f : Config G n → X) : (D).output β f=(D').output β f := by
  induction hi using Nat.decreasingInduction generalizing β with
  | self => simp only [traversal_self]
  | of_succ i live ih =>
    rw [traversal_push F live,traversal_push F' live,output_push,output_push,
      ih (upβ β)]

/-- All earlier excluded partners in the authentic vacuum remain under the
same integral, at the original regulator and on all group configurations. -/
theorem conditional {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (β : ℕ → ℝ)
    (f : Config G n → X) : (D).conditioned β f=(D').conditioned β f := by
  unfold Descent.conditioned Descent.vacuum Descent.weighted
  rw [traversal_depth F hi,traversal_depth F' hi,output R F F' hi,output R F F' hi]

/-- This is a genuine nonbare assertion if i+1<N. It keeps the entire
finite original joint input and the full previous partition in both
solvers. The held boundary is the identity. -/
theorem flat (Z Z' : ChartRatio G) (hz : LocalRatio Z) (hz' : LocalRatio Z')
    (room : (D).Room G) (room' : (D').Room G) (offsets : ℕ → ℝ) (O : Config G n → ℝ)
    (test : (D).Testable O) (other : (D').Testable O) (b : (D).Tags) (b' : (D').Tags)
    (smooth : ContDiffAt ℝ ∞ (O ∘ expLinks G _) 0) :
    Stack.read 0 (skyread Z D b room (Delay.stones offsets) (exPay O)) =
      Stack.read 0 (skyread Z' D' b' room' (Delay.stones offsets) (exPay O)) := by
  rw [←accrued Z hz D room b offsets smooth,←accrued Z' hz' D' room' b' offsets smooth]
  have first := Descent.coefficient_formula Z hz offsets (h:=room) test
  have second := Descent.coefficient_formula Z' hz' offsets (h:=room') other
  have common : (fun g : ℝ => (D).conditioned (Descent.offset offsets g) O 1) =
      (fun g : ℝ => (D').conditioned (Descent.offset offsets g) O 1) := by
    funext g
    exact congrFun (conditional R F F' hi (Descent.offset offsets g) O) 1
  rw [← common] at second
  rw [first.unique second]

end YM.Integration.WilsonCoherentInheritedRenderer
end
