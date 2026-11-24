import YM.Integration.WilsonOriginalReceivedMeasuredCarry
import YM.Integration.WilsonReceivedMeasuredStampPrice
import YM.QuadraticLocal.Rebirth.Team
import YM.QuadraticLocal.Union.Return

/-! Re-inscription of the complete returned marked source between its birth dates.
The affine reset acts on the same reported Wilson density and its hard gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedCarryPrice
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Countable ι] [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport (Stock.census V) G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
variable (cost:ℝ) {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old (Stock.census V))
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next (Stock.census V))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "upper" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G
  (R.family.path.levels.clock.op i per).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young upper k) (Coat.gStep (Ψ (i+1)).beta)
local notation "received" => Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
  actors pieces M Z w grades order shelf voter rent cost Y

local notation "h₀" => (Burn.horizon k+2)
local notation "H" => (Ψ i)
local notation "fine" => (Ψ (i+1))
local notation "income" => R.alloy.B.a.clock.J i
local notation "agenda" => Poetry.Agenda.seed D φ (Burn.horizon k) income
local notation "ratio" => (R.family.path.levels.clock.op i per).ratio
local notation "siz" => (R.alloy.B.a.S.oneStep i per).exact_size
local notation "M₁" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ hi lesson
local notation "gf" => Coat.gStep (fine).beta
local notation "gc" => Coat.gStep (H).beta
local notation "posted" => Mutation.stamp M₁ (Γ i) ζ h₀ order
local notation "carried" => Mutation.grow M₁ (Γ i) ζ h₀ order gf gc H Y
local notation "width" => ((H).p.supportExponent+1+1)
local notation "stampFee" => Invoice.price (H).p (fig).mist (order+shelf+1) op.count width (fig).limitC G
local notation "stamped" => Oak.rebate R hk D Q π Γ hi op lesson
local notation "published" => ((fig).produce (ratio).count*cost)
local notation "salary" => (stamped*(Ω⁻¹*published))
local notation "paid" => ((fig).fidelity*stampFee*(Ω⁻¹*published)+oldFee)
local notation "hardFee" => Time.quoteHard R.alloy.B.a i R.kit.book (fine).beta
local notation "w₁" => Stoop.radius w Ω
local notation "w₂" => Stoop.radius w (Ω^6)

local notation "gu" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "divisor" => LocalComparison.forcedDivisor R.family i

include course cut in
/-- At the native hard radius the regular reset costs the inherited error plus the
booked power, and the next analytic salary is bounded by the stage budget. -/
theorem charged (pass:Pass D Q R.alloy R.kit) (way:WayStation R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ income) (load:op.count ≤ h₀)
    (result:received) (simple:G.Simple) (q:ℕ) (deep:2*q+8 ≤ order) (aged:q+3 ≤ 3*k+2)
    {ε:ℝ} (ep:0<ε) (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ i)
    (c₀:0 ≤ cost) (cheap:cost ≤ Ω⁻¹) (r₀:0 ≤ rent) :
    (Ω^5)⁻¹*paid ≤ rent+ε*gu^q ∧ (Ω^5)⁻¹*salary ≤ budgetR R i ∧
    hardFee ≤ divisor ∧ divisor ≤ 1 := by
  have one:=result.Waffle.cool
  have op₀:=zero_lt_one.trans_le one
  have five₀:=pow_pos op₀ 5
  have five₁:=one_le_pow₀ (n:=5) one
  have eight:8 ≤ Ω^2:=by nlinarith only [result.Waffle.strong,sq_nonneg ((Ω)-4)]
  have big:8 ≤ Ω^5:=eight.trans (pow_le_pow_right₀ one (show 2 ≤ 5 by decide))
  have bsmall:=cheap.trans (inv_le_one_of_one_le₀ one)
  have bp:Ω⁻¹*cost ≤ Ω⁻¹:=mul_le_of_le_one_right (inv_nonneg.mpr op₀.le) bsmall
  have priced:=WilsonReceivedMeasuredStampPrice.original R hk D Q π Γ Ψ course books hi cut op lesson ahead actors M order shelf voter
    pass hospital narrow load simple q deep aged ep late (mul_nonneg (inv_nonneg.mpr op₀.le) c₀) bp (mul_nonneg (inv_nonneg.mpr op₀.le) r₀)
  have salaryEq:Ω⁻¹*published=(fig).produce (ratio).count*(Ω⁻¹*cost):=by ring
  have rentEq:8*Ω*(Ω⁻¹*rent)=8*rent:=by
    calc 8*Ω*(Ω⁻¹*rent)=8*(Ω*Ω⁻¹)*rent:=by ring
         _=8*rent:=by rw [mul_inv_cancel₀ op₀.ne',mul_one]
  have bill:paid ≤ 8*rent+ε*gu^q:=by
    change (fig).fidelity*stampFee*((fig).produce (ratio).count*(Ω⁻¹*cost))+oldFee ≤
      8*Ω*(Ω⁻¹*rent)+ε*gu^q at priced
    rw [salaryEq,←rentEq]
    exact priced
  have tail:0 ≤ ε*gu^q:=mul_nonneg ep.le (pow_nonneg (by unfold Coat.gStep; positivity) _)
  have last:(Ω^5)⁻¹*paid ≤ rent+ε*gu^q:=by
    apply (mul_le_mul_of_nonneg_left bill (inv_nonneg.mpr five₀.le)).trans
    rw [inv_mul_le_iff₀ five₀]
    linarith only [mul_le_mul_of_nonneg_right big r₀,mul_le_mul_of_nonneg_right five₁ tail]
  have low:published ≤ 1:=calc
    _ ≤ Ω*cost:=mul_le_mul_of_nonneg_right result.Waffle.earns c₀
    _ ≤ Ω*Ω⁻¹:=mul_le_mul_of_nonneg_left cheap op₀.le
    _ =1:=mul_inv_cancel₀ op₀.ne'
  have stage:=WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson books op ahead month order shelf fits narrow
  have first:Ω⁻¹*published ≤ 1:=(mul_le_mul_of_nonneg_left low (inv_nonneg.mpr op₀.le)).trans (by simpa only [mul_one] using inv_le_one_of_one_le₀ one)
  have rebate₀:0 ≤ stamped:=(mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans stage.1.quota)).trans stage.1.attendance
  have low₁:salary ≤ stamped:=mul_le_of_le_one_right rebate₀ first
  have spc:(Ω^5)⁻¹*salary ≤ budgetR R i:=(mul_le_mul_of_nonneg_left low₁ (inv_nonneg.mpr five₀.le)).trans
    ((mul_le_of_le_one_left rebate₀ (inv_le_one_of_one_le₀ five₁)).trans stage.2)
  have flag:=QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut (Nat.zero_le _)
  simp only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] at flag
  exact ⟨last,spc,flag,(Graces.glyphBound R.alloy.B.a i).2⟩

end YM.Integration.WilsonOriginalReceivedCarryPrice
