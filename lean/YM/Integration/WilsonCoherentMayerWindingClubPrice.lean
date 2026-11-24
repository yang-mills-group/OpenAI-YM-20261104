import YM.Integration.WilsonOriginalProjectedCurvatureSignedPublication
import YM.QuadraticLocal.Fk.Station
import YM.QuadraticLocal.Union.Commit
import YM.Integration.WilsonCoherentMayerWindingSide
import YM.Integration.WilsonCoherentMayerWindingGeometry

/-! The numerical full-roster winding invoice of the actual enrolled card, before both regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingClubPrice
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

theorem purchased (i k q slots:ℕ)(B:ℝ)(hB:0 ≤ B)(ε:ℝ)(hε:0 < ε):
    ∃ first:ℕ,∀ m N per (hi:m ≤ i)(_cut:i < N)(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(lesson:Lesson (N:=N) R hk D Q π Γ hi)
      (j:ℕ),j ≤ slots → ∀cost:ℝ,cost ≤ 1 → ∀A:Stationary.Link G (R.family.side i per),
      ‖A‖ ≤ B → first ≤ (R.family.side i per).val →
      let n:=R.family.side i per
      let ratio:=((R.family.path.levels.clock.op i per).ratio.count.val:ℝ)^4
      let duty:=Wharf.rate (d₀ i) (a₀ i) lesson.entry.self.paid n *
        AllOrder.Ink.Money.dearth (s₀ i k) n * (2+‖A‖)^(Burn.horizon k+4)
      2*(duty*((n.val:ℝ)^4*(cost*Breeze.areaBudget n.val j ratio))) ≤ 
        ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^q:=by
  have upper:0 < a₀ i:=(Wharf.ready R.rolls D (clock₁ i) (clock₀ i) Q φ books).choose_spec.choose_spec.1
  have slope:0 < s₀ i k:=AllOrder.Ink.Money.soprano _ (Poetry.Agenda.receives D (Burn.horizon k) (clock₁ i)).choose_spec.1 _
  let c:=2*((a₀ i)*(1+|p₀ i|)^(d₀ i))*(2+B)^(Burn.horizon k+4)
  have hc:0 ≤ c:=by dsimp [c]; positivity
  have light:= (WilsonCoherentMayerWindingGeometry.lower R (i+1) 0 (i+1) le_rfl).1
  obtain ⟨first,early⟩:= eventually_atTop.mp (WilsonCoherentMayerWindingSide.purchased
    (d₀ i) slots c (width₀ i) (s₀ i k) hc (by positivity) slope
    (ε*(WilsonCoherentMayerWindingGeometry.floor R (i+1))^q) (mul_pos hε (pow_pos light _)))
  refine ⟨first,fun m N per hi cut hk π Γ lesson j hj cost hcost A hA hn=>?_⟩
  let n:=R.family.side i per
  have dims:=WilsonCoherentMayerWindingGeometry.count R i per
  have amt:0 ≤ Breeze.areaBudget n.val j (width₀ i):=by unfold Breeze.areaBudget; positivity
  have card:lesson.entry.self.paid=p₀ i:=lesson.studied.books.fisc
  dsimp only
  rw [dims,card]
  change 2*(Wharf.rate (d₀ i) (a₀ i) (p₀ i) n * AllOrder.Ink.Money.dearth (s₀ i k) n *
    (2+‖A‖)^(Burn.horizon k+4)*((n.val:ℝ)^4*(cost*Breeze.areaBudget n.val j (width₀ i)))) ≤ _
  have hr:0 ≤ Wharf.rate (d₀ i) (a₀ i) (p₀ i) n:=by unfold Wharf.rate; positivity
  have he:0 ≤ AllOrder.Ink.Money.dearth (s₀ i k) n:=(Real.exp_pos _).le
  calc
    _ ≤ 2*(Wharf.rate (d₀ i) (a₀ i) (p₀ i) n * AllOrder.Ink.Money.dearth (s₀ i k) n *
      (2+B)^(Burn.horizon k+4)*((n.val:ℝ)^4*(1*Breeze.areaBudget n.val j (width₀ i)))):=by
        by_cases h0:0 ≤ cost
        · gcongr
        · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos
              (by positivity) (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h0) amt)))) (by positivity)
    _=WilsonCoherentMayerWindingSide.fee n.val (d₀ i) j c (width₀ i) (s₀ i k):=by
      simp [WilsonCoherentMayerWindingSide.fee,c,Wharf.rate,AllOrder.Ink.Money.dearth,
        Breeze.areaBudget,Push.AbsoluteSums.Animals.ballCost];ring
    _ ≤ ε*(WilsonCoherentMayerWindingGeometry.floor R (i+1))^q:=early n.val hn j hj _ (by positivity) le_rfl
    _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ light.le (WilsonCoherentMayerWindingGeometry.lower R N per (i+1) cut).2 _) hε.le

end YM.Integration.WilsonCoherentMayerWindingClubPrice
