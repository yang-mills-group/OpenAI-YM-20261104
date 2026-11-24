import YM.Integration.WilsonConditionalTaylorWheelVacuumHistory

/-! Periodization of the authentic upper vacuum supplies the varying finite
input in the original marked period-to-cover comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelFoldedYields
open Function Filter Lattice RG Precision Laurent Wilson Next.Free FormalBulk08
open PhysicalNext.Repeat.Legato Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "O" => R.metals.O

theorem scalar (N j:ℕ) (live:j≤N) (e:ℕ):actionW A O N j e 0=0:=by
  rcases eq_or_lt_of_le live with rfl|proper
  · rw [actionW,story_top]
    rfl
  · rw [conduct A O proper]
    simp [Blue.mix,lop]

theorem original (simple:G.Simple) (N j:ℕ) (live:j≤N) (e r:ℕ):
    Yields (fun n=>Winding.emera (actionW A O N j) n e r) (actionW A O N j e r):=by
  cases r with
  | zero=>
    rw [scalar R N j live e]
    exact Yields.zero
  | succ r=>
    have inherited:=(old A O simple R.alloy.B.ratio N j live).patch e (r+1)
    obtain ⟨s,C,positive,spatial⟩:=inherited.cover
    exact lagoon_yields spatial positive inherited.road
end YM.Integration.WilsonConditionalTaylorWheelFoldedYields
end
