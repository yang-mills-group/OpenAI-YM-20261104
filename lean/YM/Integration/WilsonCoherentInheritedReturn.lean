import YM.Integration.WilsonCoherentInheritedLamps

/-! The finite inherited positive Wilson ratio and the independent normalized
FVA2 recursion have the same complete graded expansion at the held identity.
A different forest history computes the very same coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentInheritedReturn
open Function PowerSeries Lattice Wilson RG Tree Precision
open PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Chart PertExtension.Series.Tested
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool
open FVA2 FVA2.CityHistory
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router

variable {G : Gauge} (R : Run G) {N per i : ℕ}
variable {I : Type} [Fintype I] (J : I → Lamp G) (o : I → Site (R.family.side N per))
variable (part : Bool) (hi : i ≤ N) (F : Slices R.family.path.levels per)
local notation "D" => traversal F hi
local notation "O" => look part ∘ tally J o

theorem original (room : (D).Room G) (tags : (D).Tags) (offsets : ℕ → ℝ) :
    Aspiration (fun g : ℝ => g⁻¹ ^ power J * (D).conditioned (Descent.offset offsets g) O 1)
      (fun e => coeff (power J+e) (Stack.read 0
        (skyread R.metals.O (D) tags room (Delay.stones offsets) (exPay O)))) := by
  have paid := WilsonCoherentInheritedLamps.registered J o part (D)
  have ledger := accrued R.metals.O R.alloy.B.ratio (D) room tags offsets
    ((WilsonCoherentInheritedLamps.smooth J o part).of_le le_top)
  rw [← ledger]
  simp only [coeff_mk]
  exact Descent.rescaled_formula R.metals.O R.alloy.B.ratio offsets (h:=room) paid.1 paid.2

theorem alternate (Z : ChartRatio G) (hz : LocalRatio Z)
    (F' : Slices R.family.path.levels per) (room : (D).Room G)
    (room' : (traversal F' hi).Room G)
    (tags : (D).Tags) (tags' : (traversal F' hi).Tags) (offsets : ℕ → ℝ) :
    Stack.read 0 (skyread R.metals.O (D) tags room (Delay.stones offsets) (exPay O)) =
      Stack.read 0 (skyread Z (traversal F' hi) tags' room' (Delay.stones offsets) (exPay O)) :=
  WilsonCoherentInheritedRenderer.flat R F F' hi R.metals.O Z R.alloy.B.ratio hz
    room room' offsets O (WilsonCoherentInheritedLamps.registered J o part (D)).1
    (WilsonCoherentInheritedLamps.registered J o part (traversal F' hi)).1 tags tags'
    ((WilsonCoherentInheritedLamps.smooth J o part).of_le le_top)

end YM.Integration.WilsonCoherentInheritedReturn
end
