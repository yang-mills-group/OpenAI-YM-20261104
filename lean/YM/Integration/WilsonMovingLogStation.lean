import YM.Integration.WilsonVacuumPreResetColdInput
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Link
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Thrills

/-! The classical response and its finite determinant and coupling bills on the
same physical step and same critical chart as the moving upper Wilson action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogStation
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Gauge
open Push Push.Uniform Push.PriceCompiler ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Roost Pane Sienna Lapis
open Further.PhysicalPeriodLimitF933.Mural
open Planned.JetPort AnalyticBridge VerifiedReset Collection Quotes RG.Shoot
open scoped Topology Classical
variable {G : Gauge} (R : Run G) {m N per : ℕ}
local notation "J" => R.alloy.B.a.clock.J (m+1)
local notation "L" => R.rolls.L J
local notation "T" => WilsonVacuumPreResetColdInput.tube R N per m
local notation "P" => (Lattice.Ratio.exact_size (R.alloy.B.a.S.oneStep m per))
local notation "S" => Pane.panel R.alloy m (Lattice.Ratio.exact_size (R.alloy.B.a.S.oneStep m per))
local notation "Bf" => (R.family.path.levels.budget (m+1))

/-- Keep the old regular rows at their original invoice, including at the bare date. -/
theorem incoming (live : m<N) :
    (WilsonVacuumPreResetColdInput.rows (R.family.path.rep N per (m+1)).activities).Valid
      Bf (incomingE G L (R.alloy.B.a.clock.hatBeta m)) 0 := by
  have paid := (WilsonVacuumPreResetColdInput.original R (per:=per) live).1
  have height : incomingE G L (R.alloy.B.a.clock.hatBeta m) = R.alloy.B.a.clock.allowance (m+1) := by
    unfold incomingE
    rw [← PriceCompiler.beta_eq R.alloy.B.valid m]
    rfl
  rw [height]
  exact paid

/-- A submitted genuine sensor forest with an original perturbative service
chart receives the physical classical comparison and original determinant bill. -/
theorem classical (live : m<N) (F : Forest (S).ratio) {a δ C : ℝ} {k : ℕ}
    (held : Quilt T F a) (M : Push.Uniform.Before G δ C (S).patch.J (S).kernel k)
    (ρ : Bid.Dir G (R.family.side m per) → AxisChart G F)
    (chart : M.Service F (T).high (T).up ρ) :
    ClassicalMatch F (T).high (T).low (T).up (T).down ρ ∧
    FiniteBound F (T).up (T).down (T).high (T).low (R.alloy.B.kin.alpha N m) R.metals.O ρ
      (pref R.rolls J + R.alloy.post.Γ J) (min (knot R.rolls J) (R.alloy.post.c J))
      (R.alloy.B.a.clock.loopCap (m+1)) := by
  obtain ⟨t,critical,matchT,paid⟩ :=
    Pane.presents R.rolls R.alloy R.kit.floor live P F (Y:=fun _ _ _ => a) held
  exact Pane.payouts (R:=T) (Push.Uniform.Before.Service.is_extension chart critical) matchT paid

end YM.Integration.WilsonMovingLogStation
