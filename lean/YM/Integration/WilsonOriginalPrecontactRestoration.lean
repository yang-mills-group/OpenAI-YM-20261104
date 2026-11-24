import YM.Integration.WilsonOriginalPrecontactReturn
import YM.Integration.WilsonMovingMentorStartingHard

/-! Restore elementary mark radii on the separated part of the original history.
The forced return is divided by its actual Wilson allowance once, independently
of the cutoff and period, for every elected finite accuracy. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrecontactRestoration
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
  {V ι : Type} [Fintype V] [DecidableEq V] {marks : Census V} {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
variable (cost:ℝ) {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next marks)
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


local notation "L₀" => (H).p.supportExponent
local notation "T₀" => MintClock.Page.temperature G 1 (R.alloy.B.a.clock.hatBeta i)
local notation "debit" => (Invoice.price (H).p T₀ (order+shelf+1) op.count (L₀+1) (agenda/4) G*((Ω^5)⁻¹*salary))
local notation "roll" => WilsonOriginalPrecontactRefile.shifted H posted carried
local notation "singleRows" => WilsonOriginalPrecontactRefile.singles posted
local notation "apartFee" => Real.exp (-((H).p.B/8:ℕ):ℝ)
local notation "home" => passport.coarser (ratio)


open Integration.LocalComparison
include course cut in
theorem original (pass:Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (raffle:Spill.Raffle.Warm G D R.alloy.delay φ)
    (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit D Q)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ income) (load:op.count ≤ h₀)
    (result:received) (hB:5≤ (H).p.B)
    (apart:∀ v v':V,v≠v' → (H).p.B^2+1 ≤ separation ((home).origin v) ((home).origin v'))
    (q:ℕ) (active:q+6*op.count ≤ income) :
    let L:=WilsonPrecontactSeparatedLamps.portion (roll).old (WilsonPrecontactSeparatedLamps.mixed (roll).old)
    L.Paid w (H).p.B L₀ ((Ω^6)^op.count*(apartFee*(debit+(Ω^5)⁻¹*paid))) ∧
    (roll).hard.Paid w (H).p.B L₀ (upper^(-(q:ℝ))*forcedDivisor R.family i) := by
  obtain ⟨_,stock,_,_,_,_,mixed,hard,_⟩:=
    WilsonOriginalPrecontactReturn.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
      actors M w grades order shelf voter cost pieces Z rent Y pass month hospital raffle fits narrow load result hB apart
  have one:1≤Ω:=result.Waffle.cool
  have six:1≤Ω^6:=one_le_pow₀ one
  have pos:0<Ω^6:=zero_lt_one.trans_le six
  have wage(v):0<w v := (div_pos_iff_of_pos_right pos).mp (stock.positive v)
  have complete:=Stoop.budget w stock.quota (roll).hard wage six hard
  obtain ⟨_,bill⟩:=WilsonMovingMentorStartingHard.original R way D Q π Γ Ψ course ticket hi cut (q+6*op.count) active
  have initial:=R.alloy.B.a.fits.delayed (i+1)
  have capped:Ω ≤ upper:=by
    apply result.Beamwork.trans
    apply (min_le_right _ _ : budgetR R i ≤ _).trans
    apply (Real.rpow_le_rpow_of_exponent_le initial.le ?_).trans_eq (Real.rpow_one _)
    unfold Beaming.grain
    exact (div_le_one (by positivity)).mpr (by linarith only [Nat.cast_nonneg (R.alloy.B.a.clock.J i) (α:=ℝ)])
  have powCap:(Ω^6)^op.count ≤ upper^(6*op.count):=by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans one) _) (pow_le_pow_left₀ (zero_le_one.trans one) capped _) _
  have hpos : 0<upper:=zero_lt_one.trans_le initial.le
  refine ⟨Stoop.retake w _ stock.quota wage six mixed, Hard.mono _ complete ?_⟩
  calc
    (Ω^6)^op.count*hardFee ≤ upper^(6*op.count)*hardFee := mul_le_mul_of_nonneg_right powCap (Real.exp_nonneg _)
    _ ≤ upper^(6*op.count)*(upper^(-((q+6*op.count:ℕ):ℝ))*forcedDivisor R.family i) :=
      mul_le_mul_of_nonneg_left bill (pow_nonneg hpos.le _)
    _ = upper^(-(q:ℝ))*forcedDivisor R.family i := by
      rw [Real.rpow_neg hpos.le,Real.rpow_neg hpos.le,Real.rpow_natCast,Real.rpow_natCast,pow_add]
      field_simp

end YM.Integration.WilsonOriginalPrecontactRestoration
end
