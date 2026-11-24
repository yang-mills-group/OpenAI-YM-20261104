import YM.Integration.WilsonThermometerPositionFirstTable
import YM.Integration.WilsonOriginalCopiedHistory

/-! The original first return uses the connected log of each finite ordinary
position table and the page factor of that same periodic copy. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFirstReturn
open FVA1Physical.TwoReset
open Function Filter Finset RG Lattice Wilson Marker Multi
open PhysicalNext PhysicalNext.Repeat Legato Next.Scheduling Next.Scheduling.Clock
open Push Input Org Precision Tree Exterior Next.SectorChange AnalyticBridge VerifiedReset ConnectedActivityE6
open Comparison.RG02 Comparison.RG02.Cumulants AllOrder AllOrder.Transit WheelP AllOrder.Floe
open AllOrder.Floe.Step PlanV QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker Extra.Trajectories PertExtension.Series
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick WilsonOriginalCopiedHistory
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (i per : ℕ) {V T : Type} [Fintype V] [LinearOrder V]
    (d : V → ℕ) (o : V → Site (R.family.side (i+1) per))
    (g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t:V → T → ℂ) (x:T) (p : ℕ)

def submitted : Values G (Stock.census V) (R.family.side i per) :=
  fun grid tiles k z => limUnder (coverFilter R.family.path.levels.S i grid) fun b =>
    let A := Stationary.arm G (R.family.side i b.val) 1 (convey (coverWin b.prop) z)
    (((Pages grid (R.family.side i b.val):ℕ):ℝ)⁻¹ : ℝ) •
      Order.observe (Stock.census V) p (connected (Order.series (Stock.census V) p
        (WilsonThermometerPositionFirstTable.filed R i b.val d o (tiled R tiles b) g τ v t x
          (forest R i grid b) (tag R i grid b) A p))) k

variable {m h : ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q : D.Tab R.rolls) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (enrolled : PlanV.Path D R.alloy Q h (i+1) m π Γ)

include enrolled in
/-- The first received coefficient on every reporting side and at every real
link field, with exactly the same shared forest, tags and cover filter. -/
theorem original (archive : Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (σ : ℝ) (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0 < σ) (D₀ : BudgetPoint) (inside : p ≤ h + 2) :
    block R (per:=per) (Nat.lt_succ_self i) p (fun _ mult =>
      WilsonThermometerNumericalBank.bank R d o g τ v t mult x (π (i+1)) (tape (h+2))) =
      submitted R i per d o g τ v t x p := by
  funext grid tiles k z
  unfold block WilsonOriginalCoverCoefficient.read submitted
  apply congrArg (limUnder (coverFilter R.family.path.levels.S i grid))
  funext b
  let A := Stationary.arm G (R.family.side i b.val) 1 (convey (coverWin b.prop) z)
  have H := (WilsonThermometerPositionFirstTable.original R i b.val d o (tiled R tiles b)
    g τ v t x (forest R i grid b) (tag R i grid b) A p D Q π Γ enrolled
    archive active σ positive w fleet rate D₀ inside).2
  exact congrArg (fun a => (((Pages grid (R.family.side i b.val):ℕ):ℝ)⁻¹ : ℝ) •
    Order.observe (Stock.census V) p a k) H

end YM.Integration.WilsonThermometerPositionFirstReturn
