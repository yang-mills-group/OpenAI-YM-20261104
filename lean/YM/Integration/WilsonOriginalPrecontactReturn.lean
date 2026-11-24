import YM.Integration.WilsonOriginalPrecontactRefile
import YM.Integration.WilsonOriginalReceivedMeasuredCarry
import YM.Integration.WilsonMovingMentorRaffleCourse

/-! Run the original no-birth block and measured reset before keeping just the
singleton analytic inputs above contact. Every inherited proper face and its
joint exterior remains in the same original next-date density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrecontactReturn
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

include course cut in
theorem original (pass:Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (raffle:Spill.Raffle.Warm G D R.alloy.delay φ)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ income) (load:op.count ≤ h₀)
    (result:received) (hB:5≤ (H).p.B)
    (apart:∀ v v':V,v≠v' → (H).p.B^2+1 ≤ separation ((home).origin v) ((home).origin v')) :
    (∀ x, LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x) =
      (Tint.Patrol.picture singleRows roll).density x) ∧
    Scene.Armada singleRows w₂ grades agenda ((Ω^5)⁻¹*salary) order op.count shelf ∧
    Tableau pieces actors singleRows ∧ Taut (home).support actors pieces (roll).old ∧
    Crown (home).support actors pieces (roll).hard ∧
    (roll).old.Paid w₂ (H).p.B L₀ (apartFee*debit+(Ω^5)⁻¹*paid) ∧
    (WilsonPrecontactSeparatedLamps.portion (roll).old (WilsonPrecontactSeparatedLamps.mixed (roll).old)).Paid
      w₂ (H).p.B L₀ (apartFee*(debit+(Ω^5)⁻¹*paid)) ∧
    (roll).hard.Paid w₂ (H).p.B L₀ hardFee ∧ (roll).hard=Y.hard := by
  obtain ⟨fund,table,physical,flags,old,hard,held,act⟩:=
    WilsonOriginalReceivedMeasuredCarry.measured R hk D Q π Γ Ψ course books hi cut op lesson ahead
      actors M w grades order shelf voter cost pieces Z rent Y pass month hospital fits narrow load result
  have lvl:h₀ ≤ income:=hk.trans (R.alloy.B.a.fits.mono hi)
  have rank:order ≤ income:=fits.trans (by omega)
  have inv:Invoice.Supports (H).p T₀ (L₀+1) gc agenda (agenda/4) :=
    (WilsonMovingMentorRaffleCourse.measured R raffle course hi (by omega : Burn.horizon k ≤ income)
      rank narrow (load.trans lvl) cut.le).1
  have base:=WilsonPrecontactSeparatedLamps.lower (carried).old (show L₀≤width by linarith) fund.positive old
  have extra:=WilsonPrecontactSeparatedLamps.lower (carried).old (show L₀+1≤width by linarith) fund.positive old
  have legal:=WilsonOriginalPrecontactRefile.compatible H actors pieces posted carried table physical
  have pos : 0≤L₀ := (H).p.exponent_pos.le
  refine ⟨?_,WilsonOriginalPrecontactRefile.enrolled posted fund,legal.1,legal.2,flags,
    WilsonOriginalPrecontactRefile.priced H posted carried fund inv base hB apart,
    WilsonOriginalPrecontactRefile.full_mixed H posted carried fund inv hB apart extra,hard,held⟩
  intro x
  apply (act x).trans
  funext U
  exact WilsonOriginalPrecontactRefile.density H posted carried fund inv base pos x U

end YM.Integration.WilsonOriginalPrecontactReturn
end
