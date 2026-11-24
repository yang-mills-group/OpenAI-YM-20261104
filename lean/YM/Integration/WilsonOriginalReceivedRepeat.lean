import YM.Integration.WilsonOriginalReceivedMeasuredCarry
import YM.Integration.WilsonOriginalReceivedCarryPrice
import YM.Integration.WilsonOriginalTwoDateQHistory
import YM.QuadraticLocal.Rebirth.Team
import YM.QuadraticLocal.Union.Return

/-! Re-inscription of the complete returned marked source between its birth dates.
The affine reset acts on the same reported Wilson density and its hard gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedRepeat
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
  (floor:m ≤ j) (cut : j+1 < N)
local notation "hi" => (floor.trans (Nat.le_succ j))
variable
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson : Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j)))
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Countable ι] [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side ((j+1)+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport (Stock.census V) G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J (j+1)))
variable (cost rent:ℝ) {oldIndex outIndex:Type}
variable [outCount : Countable outIndex]
variable (pieces:∀ v,Submodule ℝ (X v))
variable (Z:Tint.Incoming passport (Ψ ((j+1)+1)) (Affinity.Wallet actors) oldIndex (Stock.census V))
variable (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio)
      (Ψ (j+1)) (Affinity.Wallet actors) outIndex (Stock.census V))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "upper" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G
  (R.family.path.levels.clock.op (j+1) per).ratio.count (Ψ ((j+1)+1)).p (Ψ (j+1)).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young upper k) (Coat.gStep (Ψ ((j+1)+1)).beta)
local notation "received" => Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
  actors pieces M Z w grades order shelf voter rent cost Y

local notation "h₀" => (Burn.horizon k+2)
local notation "H" => (Ψ (j+1))
local notation "fine" => (Ψ ((j+1)+1))
local notation "income" => R.alloy.B.a.clock.J (j+1)
local notation "agenda" => Poetry.Agenda.seed D φ (Burn.horizon k) income
local notation "ratio" => (R.family.path.levels.clock.op (j+1) per).ratio
local notation "siz" => (R.alloy.B.a.S.oneStep (j+1) per).exact_size
local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ hi lesson
local notation "gf" => Coat.gStep (fine).beta
local notation "gc" => Coat.gStep (H).beta
local notation "posted" => Mutation.stamp M₁ (Γ (j+1)) ζ h₀ order
local notation "carried" => Mutation.grow M₁ (Γ (j+1)) ζ h₀ order gf gc H Y
local notation "width" => ((H).p.supportExponent+1+1)
local notation "stampFee" => Invoice.price (H).p (fig).mist (order+shelf+1) op.count width (fig).limitC G
local notation "stamped" => Oak.rebate R hk D Q π Γ hi op lesson
local notation "published" => ((fig).produce (ratio).count*cost)
local notation "salary" => (stamped*(Ω⁻¹*published))
local notation "paid" => ((fig).fidelity*stampFee*(Ω⁻¹*published)+oldFee)
local notation "hardFee" => Time.quoteHard R.alloy.B.a (j+1) R.kit.book (fine).beta
local notation "w₁" => Stoop.radius w Ω
local notation "w₂" => Stoop.radius w (Ω^6)

local notation "gu" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "divisor" => LocalComparison.forcedDivisor R.family (j+1)

local notation "nextCut" => Nat.lt_trans (Nat.lt_succ_self j) cut
local notation "stockCost" => ((Ω^5)⁻¹*salary)
local notation "stockError" => ((Ω^5)⁻¹*paid)
local notation "fitClock" => hk.trans (R.alloy.B.a.fits.mono floor)

include course cut path outCount in
/-- On the same elected Wilson history, repeat the exported step with all previously
filed marks. The admitted radius and independent voter are fixed before the
requested tolerance at the receiving date. -/
theorem purchased (pass:Pass D Q R.alloy R.kit) (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ R.alloy.B.a.clock.J j) (load:op.count ≤ h₀)
    (packed:order+shelf ≤ h₀) (result:received) (simple:G.Simple)
    (q:ℕ) (deep:2*q+8 ≤ order) (aged:q+3 ≤ 3*k+2) {ε:ℝ} (ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ (j+1))
    (c₀:0 ≤ cost) (cheap:cost ≤ Ω⁻¹) (r₀:0 ≤ rent) (test:Wallet actors) :
    let plan:Syl.School k:=⟨order,op.count,shelf,load,fits,packed⟩
    let nx:=plan.room (step_paid R.alloy.B.a j) fitClock
    ∃ (lesson₂:Lesson (N:=N) R hk D Q π Γ floor)
      (vote:Cruise.Voter posted agenda order nx.count nx.stage k (R.alloy.B.a.clock.J j)),
      let Δ:=Oak.expenseReal R hk D Q π Γ books floor nx lesson₂ ahead order shelf
      let h:=max 1 (max (Δ*stockCost) stockError)
      let w':=Stoop.radius w₂ h
      let c':=h⁻¹*stockCost
      let e':=h⁻¹*stockError
      1 ≤ h ∧ 0 ≤ c' ∧ c' ≤ Δ⁻¹ ∧ e' ≤ 1 ∧ stockError ≤ rent+ε*gu^q ∧ stockCost ≤ budgetR R (j+1) ∧
      Countable (Mutation.Names M₁ order) ∧
      (∀v,w' v=w v/(Ω^6*h)) ∧
      Scene.Armada posted w' grades agenda c' order nx.count shelf ∧ Tableau pieces actors posted ∧
      Taut (passport.coarser (ratio)).support actors pieces (carried).old ∧
      Crown (passport.coarser (ratio)).support actors pieces (carried).hard ∧
      (carried).old.Paid w' (H).p.B width e' ∧ (carried).hard.Paid w' (H).p.B (H).p.supportExponent divisor ∧
      (carried).hard=Y.hard ∧ (∀x,LocalComparison.actualPush R.family N per (j+1) ((Tint.Patrol.picture M Z).density x)=
        (Tint.Patrol.picture posted carried).density x) ∧
      ∀τ:ℝ,0<τ → τ ≤ 1 → ∃ (c:Type),Countable c ∧ ∃ out:Tint.Incoming
        ((passport.coarser (ratio)).coarser (R.family.path.levels.clock.op j per).ratio)
        (Ψ j) (Wallet actors) c (Stock.census V),
        let student₂:=Oak.student (n:=per) R hk D Q π Γ books floor nx lesson₂ ahead actors posted order vote
        Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books floor nx lesson₂ ahead actors pieces posted carried w' grades order shelf vote
          (max e' τ) c' out ∧
        h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) (rent+ε*gu^q)) ∧
        ∀x,LocalComparison.actualPush R.family N per j
          (LocalComparison.actualPush R.family N per (j+1) ((Tint.Patrol.picture M Z).density x))=
          (Tint.Patrol.report student₂ out gc).density x := by
  intro plan nx
  have wide:shelf ≤ income:=narrow.trans (R.alloy.B.a.fits.mono (Nat.le_succ j))
  obtain ⟨funds,school,taut,crown,regular,forced,retained,field⟩:=WilsonOriginalReceivedMeasuredCarry.measured R hk D Q π Γ Ψ course
    books hi cut op lesson ahead actors M w grades order shelf voter cost pieces Z rent Y pass month hospital fits wide load result
  obtain ⟨fee,cap,flag,tiny⟩:=WilsonOriginalReceivedCarryPrice.charged R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M w grades order shelf voter cost pieces Z rent Y pass (chamber.ready scroll) month hospital fits wide load result simple q deep aged ep late c₀ cheap r₀
  obtain ⟨lesson₂⟩:=Oak.tale R hk D Q π Γ floor nextCut path
  obtain ⟨cal₂⟩:=Oak.agrees R hk D Q π Γ Ψ course floor nextCut lesson₂
  have vote:=plan.future (step_paid R.alloy.B.a j) fitClock grades posted funds
  have nextCash:=WilsonOriginalMeasuredReentry.connected R hk D Q pass π Γ Ψ course floor nextCut lesson₂ books nx ahead
    month order shelf hospital vote.height narrow load
  refine ⟨lesson₂,vote,?_⟩
  intro Δ h w' c' e'
  have hu:1 ≤ h:=le_max_left _ _
  have hp:=zero_lt_one.trans_le hu
  have Δ₀:0<Δ:=zero_lt_one.trans_le nextCash.cool
  have ce:c' ≤ Δ⁻¹:=by
    apply (inv_mul_le_iff₀ hp).2
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ Δ₀).2
    simpa only [mul_comm (stockCost) Δ] using ((le_max_left _ _).trans (le_max_right 1 _):Δ*stockCost ≤ h)
  have ee:e' ≤ 1:=by
    apply (inv_mul_le_iff₀ hp).2
    rw [mul_one]
    exact (le_max_right _ _).trans (le_max_right 1 _)
  haveI students:Countable (Scene.Texts M (Pane.panel R.alloy (j+1) siz).ratio (Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)):=Scene.crewC M _
      (Cruise.publish D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)
      (Cruise.funded D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry lesson.studied ahead)
  haveI onFile:Countable (Mutation.Names M₁ order):=@Mutation.instCountable _ _ _ _ _ _ _ _ M₁ order students
  haveI combined : Countable ((Scene.Texts M (Pane.panel R.alloy (j+1) siz).ratio (Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)) ⊕ outIndex) := by infer_instance
  have accepted:=funds.stored hu
  have paidOld:=Stoop.tighten w₂ (carried).old funds.positive hu regular
  have paidHard:=Stoop.leaves w₂ (carried).hard funds.positive hu forced
  refine ⟨hu,Push.AbsoluteSums.budget_nonneg (accepted.suggests 0),ce,ee,fee,cap,onFile,fun v=>div_div _ _ _,accepted,school,taut,crown,paidOld,Hard.mono _ paidHard flag,retained,field,?_⟩
  intro τ posτ topτ
  have native:(carried).old.Paid w' (H).p.B (H).p.supportExponent (max e' τ):=by
    apply (carried).old.loan_monotone _ (le_max_left _ _)
    obtain ⟨f,hn,terms,sums⟩:=paidOld.budget
    refine ⟨f,hn,terms,fun v=>Push.AbsoluteSums.budget_mono (sums v) ?_ ?_⟩
    · intro a
      split
      · exact mul_nonneg (mul_nonneg (Poly.worth accepted.positive _).le (hn a)) (Real.exp_nonneg _)
      · exact le_rfl
    · intro a
      split
      · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (mul_nonneg (Poly.worth accepted.positive _).le (hn a))
        exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      · exact le_rfl
  obtain ⟨c,cc,out,story⟩:=Oak.Buffered.arrive (ιw:=(Scene.Texts M (Pane.panel R.alloy (j+1) siz).ratio (Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) siz M order voter lesson.entry)) ⊕ outIndex) R simple hk D Q π Γ Ψ course scroll books chamber floor nextCut nx lesson₂ cal₂ ahead
    hospital actors pieces posted carried w' grades order shelf vote (max e' τ) c' load narrow accepted school test taut crown native
    (Hard.mono _ paidHard (flag.trans tiny)) (ce.trans (inv_le_one_of_one_le₀ nextCash.cool)) (posτ.trans_le (le_max_right _ _)) (max_le ee topτ)
  have hi₀:0 ≤ budgetR R (j+1):=zero_le_one.trans (result.Waffle.cool.trans result.Beamwork)
  have geometry:Δ*stockCost ≤ budgetR R j*budgetR R (j+1):=(mul_le_mul_of_nonneg_left cap Δ₀.le).trans (mul_le_mul_of_nonneg_right story.Beamwork hi₀)
  refine ⟨c,cc,out,story,max_le_max le_rfl (max_le_max geometry fee),fun x=>?_⟩
  exact (congrArg (LocalComparison.actualPush R.family N per j) (field x)).trans (story.reads x)

end YM.Integration.WilsonOriginalReceivedRepeat
