import YM.Integration.WilsonCoherentMayerWindingClubPrice
import YM.Integration.WilsonOriginalReceivedFiniteChain

/-! Fixed polynomial weights on the true finite side are covered by the original occupied tuition. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramMarkedTuition
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
open Filter ConnectedActivityE6
variable {G:Gauge}(R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q:D.Tab R.rolls) {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)
local notation "clock₁" i:max => R.alloy.B.a.clock.J (i+1)
local notation "clock₀" i:max => R.alloy.B.a.clock.J i
local notation "d₀" i:max => Wharf.title R.rolls D (clock₁ i) (clock₀ i) Q φ books
local notation "a₀" i:max => Wharf.upper R.rolls D (clock₁ i) (clock₀ i) Q φ books
local notation "s₀" i:max k:max => Poetry.Agenda.poll D (Burn.horizon k) (clock₁ i)
local notation "p₀" i:max => loopBill G (R.rolls.L (clock₁ i)) (R.alloy.B.a.clock.hatBeta i)
local notation "width₀" i:max => ((R.family.S.block i).val:ℝ)^4


theorem original (i k q slots exponent : ℕ) (ε : ℝ) (he : 0 < ε) :
    ∃ first:ℕ,∀m N per (hi:m ≤ i)(_cut:i<N)(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(lesson:Lesson (N:=N) R hk D Q π Γ hi)
      (op:Mentor.Opportunity (clock₁ i) (clock₀ i)), op.count ≤ slots →
      ∀cost:ℝ, 0 ≤ cost → cost ≤ 1 → first ≤ (R.family.side i per).val →
      ∀A:Stationary.Link G (R.family.side i per),
        ((R.family.side i per).val:ℝ)^exponent * |Oak.Tutoring.bill R hk D Q π Γ books hi op lesson A cost| ≤
        (ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^q)*(2+‖A‖)^(Burn.horizon k+4) := by
  have upper : 0 < a₀ i := (Wharf.ready R.rolls D (clock₁ i) (clock₀ i) Q φ books).choose_spec.choose_spec.1
  have slope : 0 < s₀ i k := AllOrder.Ink.Money.soprano _
    (Poetry.Agenda.receives D (Burn.horizon k) (clock₁ i)).choose_spec.1 _
  let c := (a₀ i)*(1+|p₀ i|)^(d₀ i)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have floor := (WilsonCoherentMayerWindingGeometry.lower R (i+1) 0 (i+1) le_rfl).1
  obtain ⟨first,early⟩ := eventually_atTop.mp (WilsonCoherentMayerWindingSide.purchased
    (exponent+d₀ i) slots c (width₀ i) (s₀ i k) hc (by positivity) slope
    (ε*(WilsonCoherentMayerWindingGeometry.floor R (i+1))^q) (mul_pos he (pow_pos floor _)))
  refine ⟨first,?_⟩
  intro m N per hi cut hk π Γ lesson op load cost nonnegative small large A
  let n := R.family.side i per
  have dims := WilsonCoherentMayerWindingGeometry.count R i per
  have card : lesson.entry.self.paid=p₀ i := lesson.studied.books.fisc
  have tariff : 0 ≤ Wharf.rate (d₀ i) (a₀ i) (p₀ i) n := by unfold Wharf.rate; positivity
  have tail : 0 ≤ AllOrder.Ink.Money.dearth (s₀ i k) n := (Real.exp_pos _).le
  have area : 0 ≤ Breeze.areaBudget n.val op.count (width₀ i) := by unfold Breeze.areaBudget; positivity
  have clean : 0 ≤ Oak.Tutoring.bill R hk D Q π Γ books hi op lesson A cost := by
    unfold Oak.Tutoring.bill Oak.Tutoring.duty Air.united Wharf.rate AllOrder.Ink.Money.dearth Breeze.areaBudget
    positivity
  rw [abs_of_nonneg clean]
  change (n.val:ℝ)^exponent *
    (Wharf.rate (d₀ i) (a₀ i) lesson.entry.self.paid n * AllOrder.Ink.Money.dearth (s₀ i k) n *
      (2+‖A‖)^(Burn.horizon k+4) * ((n.val:ℝ)^4*(cost*Breeze.areaBudget n.val op.count
        (((R.family.path.levels.clock.op i per).ratio.count.val:ℝ)^4)))) ≤ _
  rw [dims,card]
  calc
    _ ≤ (n.val:ℝ)^exponent * (Wharf.rate (d₀ i) (a₀ i) (p₀ i) n * AllOrder.Ink.Money.dearth (s₀ i k) n *
        (2+‖A‖)^(Burn.horizon k+4) * ((n.val:ℝ)^4*(1*Breeze.areaBudget n.val op.count (width₀ i)))) := by
        gcongr
    _ = WilsonCoherentMayerWindingSide.fee n.val (exponent+d₀ i) op.count c (width₀ i) (s₀ i k) *
        (2+‖A‖)^(Burn.horizon k+4) := by
        simp [WilsonCoherentMayerWindingSide.fee,c,Wharf.rate,AllOrder.Ink.Money.dearth,
          Breeze.areaBudget,Push.AbsoluteSums.Animals.ballCost,pow_add];ring
    _ ≤ (ε*(WilsonCoherentMayerWindingGeometry.floor R (i+1))^q)*(2+‖A‖)^(Burn.horizon k+4) := by
        exact mul_le_mul_of_nonneg_right (early n.val large op.count load _ (by positivity) le_rfl) (by positivity)
    _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ floor.le (WilsonCoherentMayerWindingGeometry.lower R N per (i+1) cut).2 _) he.le)
          (by positivity)

end YM.Integration.WilsonPositionProgramMarkedTuition
end
