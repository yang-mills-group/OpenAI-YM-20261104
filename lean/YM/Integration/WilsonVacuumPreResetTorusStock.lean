import YM.Integration.WilsonMovingMentorConcourseRows
import YM.AllOrder.Till.Glace

/-! The regular rows selected at an intervening date on the original torus.
A single pair of signed packet series per age accounts for the full cutoff
from the independent uncut action to the physical finite-window renderer. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusStock
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP AllOrder.Till Extra.Iteration
open AnalyticBridge VerifiedReset
open ConnectedActivityE6
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G)
local notation "V" => R.alloy.B.a

theorem window {n : Side} {B : BudgetPoint} {H : Rep G n}
    {π : Layout G} {β : ℝ} {k : ℕ}
    (C : Burn.Seed H (M0 k 0 B π β)) (positive : 0 < β)
    (room : 4*(Burn.horizon k+4) ≤ B.B) (U : Config G n) :
    ∑ x, H.activities.E (C.model x) U =
      β*∑ i ∈ Age.scope (Burn.horizon k+2),
        (Coat.gStep β)^i.stamp*action (legible (π i) B.B) U := by
  let t := Coat.gStep β
  have hot : 0 < t := inv_pos.mpr (Real.sqrt_pos.2 positive)
  have scale : t^2*β=1 := by
    change (Real.sqrt β)⁻¹^2*β=1
    rw [inv_pow,Real.sq_sqrt positive.le,inv_mul_cancel₀ positive.ne']
  have fits : ∀ i∈Age.scope (Burn.horizon k+2),4*i.r≤B.B := by
    intro i hi
    have h := Age.in_scope.mp hi
    have p := i.pricey
    omega
  calc
    _ = ∑ x, M0 k 0 B π β n x U :=
      Finset.sum_congr rfl fun x _ => congrFun (C.value x) U
    _ = _ := (Tilt.sunset π _ B.B fits t hot β scale U).symm

theorem history {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin} {m N j h : ℕ}
    (route : PlanV.Path r R.alloy Q h N m π Γ) (before : m≤j) (after : j≤N)
    (i : Age) (active : i∈Age.scope (h+2)) :
    ∃ X Y : ℕ → RG.Atom G i.r,
      (∀ (n : Side) (U : Config G n), action (π j i) U -
        action (legible (π j i) ((V).budget j).B) U = action X U - action Y U) ∧
      Charged X (r.pre h ((V).clock.J j) i/2)
        (Real.exp (-(r.pre h ((V).clock.J j) i/2)*((V).budget j).B)*PlanV.capprice R.alloy h j i) ∧
      Charged Y (r.pre h ((V).clock.J j) i/2)
        (Real.exp (-(r.pre h ((V).clock.J j) i/2)*((V).budget j).B)*PlanV.capprice R.alloy h j i) := by
  exact action_slips (π j i) ((route.1 j before after i active).pay)
    ((r.shape h).pos ((V).clock.J j) i) ((V).budget j).B

end YM.Integration.WilsonVacuumPreResetTorusStock

