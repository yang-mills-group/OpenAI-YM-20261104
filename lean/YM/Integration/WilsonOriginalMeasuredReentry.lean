import YM.QuadraticLocal.Rebirth.Actual

/-! The measured coupling reversion and outgoing regular invoice on the original elected course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMeasuredReentry
open Finset Lattice Wilson RG RG.Supply Pressure Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor
open RemainderComparison QuadraticLocal.Rebirth AllOrder.Wheel.Ride
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) {m i N n k : ℕ}
  (hk : Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (pass : Pass D Q R.alloy R.kit)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (course : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  (hi : m ≤ i) (cut : i < N) (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  {φ : ℕ → ℕ} (books : Offices.Books D R.rolls Q φ)
  (op : Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (ahead : Forecast D R.rolls Q φ books)

local notation "fine" => R.alloy.B.a.clock.J (i+1)
local notation "coarse" => R.alloy.B.a.clock.J i
local notation "fineStage" => R.alloy.B.a.budget (i+1)
local notation "coarseStage" => R.alloy.B.a.budget i
local notation "calibration" => R.alloy.B.a.clock.hatBeta i
local notation "fineCalibration" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "blockSize" => R.rolls.L fine
local notation "admission" => R.alloy.B.a.clock.adm (i+1)
local notation "level" => (show Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J i from
  hk.trans (R.alloy.B.a.fits.mono hi))
local notation "lit" => litP D R.alloy Q level lesson.entry
local notation "fineCoupling" => Coat.gStep ((Ψ (i+1)).beta)
local notation "coarseCoupling" => Coat.gStep ((Ψ i).beta)
local notation "payment" => Oak.payroll R hk D Q π Γ hi lesson
local notation "rebate" => Oak.rebate R hk D Q π Γ hi op lesson
local notation "era" => Oak.era R hk D Q π Γ hi op lesson

include pass course cut in
private def prediction : Predicted R.rolls D fine coarse admission lit calibration := by
  let coarseRow := later R π Γ Ψ course hi cut.le
  let fineRow := later R π Γ Ψ course (Nat.le_succ_of_le hi) cut
  have actual := PriceCompiler.beta_eq R.alloy.B.valid i
  have band : (Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1) :=
    fineRow.beta.symm ▸ (R.T.sticks N n |>.prices _ (Nat.zero_le _) cut).2
  refine ⟨⟨lesson.entry, lesson.studied.books.fisc, (Ψ (i+1)).beta,
    (show fineCalibration = _ from actual) ▸
      (show (Ψ (i+1)).beta ∈ Set.Icc (fineCalibration/2) (2*fineCalibration) from band)⟩,
    (Ψ i).beta, coarseRow.beta.symm ▸ (R.T.sticks N n |>.prices _ (Nat.zero_le _) cut.le).2, ?_⟩
  obtain ⟨_, _, _, threshold, _⟩ := WheelP.zones D Q R.alloy R.kit (m:=i) pass
  change Pressure.temp calibration ^ 2 *
    |(Ψ i).beta - Wheel.now ((lit).issue lesson.entry) (Burn.horizon k+2) (Ψ (i+1)).beta| ≤ _
  rw [← lesson.eats, coarseRow.beta, fineRow.beta, ← threshold]
  exact course.1.pace _ hi cut

variable (month : Scholar.Month R.rolls D Q R.alloy.delay) (order width : ℕ)
local notation "figures" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order width
local notation "radius" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order width

include pass course cut month in
theorem credited (fits : order ≤ Burn.horizon k+1) (narrow : width ≤ coarse) :
    Recharged (Γ i) (Oak.grade0 R hk D Q π Γ hi lesson) fineCoupling coarseCoupling
      (Burn.horizon k+2) order width payment (figures).fidelity rebate ∧ rebate ≤ budgetR R i := by
  let predicted := prediction (R:=R) (hk:=hk) (D:=D) (Q:=Q) (pass:=pass) (π:=π) (Γ:=Γ)
    (Ψ:=Ψ) (course:=course) (hi:=hi) (cut:=cut) (lesson:=lesson)
  have priced : Scholar.Priced R.rolls D fine coarse admission lit calibration :=
    month.coupons _ _ op era calibration (R.alloy.B.valid.pays i)
  have allowed (p : Sunrise.Loan) (he : p.e ≤ order) (hw : p.toll ≤ width) :
      p.lag ∈ House.grammar (coarse+1) := by
    have crest := p.crest
    have height : order ≤ coarse := fits.trans (le_trans (by omega) level)
    unfold Sunrise.Loan.lag
    rw [House.grammar, mem_Icc]
    omega
  have unit : 1 ≤ payment := House.serene R.rolls D fine coarse admission lit (coarse+1) calibration
  refine ⟨⟨fits.trans (by omega), unit, ?_, fun p he hw j hj => ?_, fun p he hw => ?_⟩, ?_⟩
  · change _ ≤ ((Burn.horizon k+2 : ℕ) : ℝ)*payment
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (zero_le_one.trans unit)
  · have upper : j ≤ Burn.horizon k+2 := by omega
    rw [Chart.parallel (Γ i) (Oak.grade0 R hk D Q π Γ hi lesson) _ _ _
      (((lit).sustenance.due lesson.entry).1) _ _ upper upper
      (show ∀ m : ℕ, m ≤ j → Γ i m = (lit).issue lesson.entry m from fun m _ => congr_fun lesson.eats m)]
    exact House.settles R.rolls D fine coarse admission lit calibration predicted
      _ (coarse+1) j upper (allowed p he hw)
  · have bound := priced.earns predicted order p.e p.lag (allowed p he hw) fits he
    change |fineCoupling^p.e * Balance.balance ((lit).issue lesson.entry) _ (Burn.horizon k+2)
      p.lag fineCoupling coarseCoupling (order-p.e)| ≤ _ at bound
    rw [Recharged.value_shift (Γ i) (Oak.grade0 R hk D Q π Γ hi lesson) fineCoupling
      coarseCoupling _ _ _ _ lesson.eats]
    exact bound
  · change _ ≤ MintClock.Page.reward fineCalibration _
    rw [PriceCompiler.beta_eq R.alloy.B.valid]
    exact priced.quota

include pass course cut month in
theorem connected
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (stage : order+1 ≤ op.stage) (narrow : width ≤ coarse) (load : op.count ≤ Burn.horizon k+2) :
    Earn.Earnings.Cashier figures G
      (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i n).exact_size).ratio.count
      (Ψ (i+1)).p (Ψ i).p radius (Willow.haloSlack (coarseStage).B) coarseCoupling := by
  obtain ⟨calendar⟩ := Oak.agrees R hk D Q π Γ Ψ course hi cut lesson
  have fineTerms := (later R π Γ Ψ course (Nat.le_succ_of_le hi) cut).truep.point
  have coarseTerms := (later R π Γ Ψ course hi cut.le).truep.point
  have size : (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i n).exact_size).ratio.count = blockSize :=
    calendar.clock.laws.data.funds.length_eq
  obtain ⟨box, same, fineSame, threshold, fineThreshold, fineBox, _, _⟩ :=
    WheelP.zones D Q R.alloy R.kit (m:=i) pass
  have temperatures : Pressure.temp calibration ≤ 2 * Pressure.fiery G calibration blockSize :=
    calendar.clock.laws.data.funds.length_eq ▸ calendar.clock.laws.data.room.temperatures
  let predicted := prediction (R:=R) (hk:=hk) (D:=D) (Q:=Q) (pass:=pass) (π:=π) (Γ:=Γ)
    (Ψ:=Ψ) (course:=course) (hi:=hi) (cut:=cut) (lesson:=lesson)
  have priced := hospital.price _ _ order width op era narrow stage load calibration (R.alloy.B.valid.pays i)
  have band : inBand (betaF G calibration blockSize) (Ψ i).beta :=
    (month.coupons _ _ op era calibration (R.alloy.B.valid.pays i)).postBand predicted.post predicted.band
  have cost := priced.cost (Ψ i).beta band fineStage coarseStage
    ⟨fineSame, fineBox, fineThreshold.trans_le (by
      change Pressure.fiery G calibration blockSize ≤ _
      have positive : 0 < Pressure.fiery G calibration blockSize := (fineStage).threshold_pos.trans_eq fineThreshold
      linarith only [positive])⟩ ⟨same, box, threshold.trans_le temperatures⟩
  rw [fineTerms, coarseTerms, size, box]
  exact (MintClock.Page.drops G blockSize _ _ _ _ _ fineSame same fineBox box cost).2

end YM.Integration.WilsonOriginalMeasuredReentry
end

