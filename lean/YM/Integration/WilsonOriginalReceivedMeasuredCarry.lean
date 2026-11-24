import YM.Integration.WilsonOriginalSignedQFiled
import YM.QuadraticLocal.Rebirth.Team
import YM.QuadraticLocal.Union.Return

/-! Re-inscription of the complete returned marked source between its birth dates.
The affine reset acts on the same reported Wilson density and its hard gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedMeasuredCarry
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

include course cut in
/-- Reset the independent rows at the actual lower beta. Every marked configuration
keeps the returned hard field and all prior markings under the original push. -/
theorem measured (pass:Pass D Q R.alloy R.kit)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (narrow:shelf ≤ income) (load:op.count ≤ h₀)
    (result:received) :
    Scene.Armada posted w₂ grades agenda ((Ω^5)⁻¹*salary) order op.count shelf ∧
    Tableau pieces actors posted ∧ Taut (passport.coarser (ratio)).support actors pieces (carried).old ∧
    Crown (passport.coarser (ratio)).support actors pieces (carried).hard ∧
    (carried).old.Paid w₂ (H).p.B width ((Ω^5)⁻¹*paid) ∧
    (carried).hard.Paid w₂ (H).p.B (H).p.supportExponent hardFee ∧
    (carried).hard=Y.hard ∧
    (∀ x,LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x)=
      (Tint.Patrol.picture posted carried).density x) := by
  have calibrated:=(WilsonOriginalMeasuredReentry.credited R hk D Q pass π Γ Ψ course hi cut lesson books op ahead
    month order shelf fits narrow).1
  have lower:=WilsonOriginalMeasuredReentry.connected R hk D Q pass π Γ Ψ course hi cut lesson books op ahead
    month order shelf hospital voter.height narrow load
  have warm:=result.Waffle
  have one:1 ≤ Ω:=warm.cool
  have pos:0<Ω:=zero_lt_one.trans_le one
  have widthPos:0 ≤ (width):=by
    linarith [(Ψ i).p.exponent_pos]
  have stock:=result.earning.stored one
  have issued:=Mutation.allocate M₁ (Γ i) ζ h₀ order w₁ grades calibrated stock
  have rental:=(Mutation.leases M₁ (Γ i) ζ h₀ order gf gc w₁ grades calibrated stock
      lower.bloom.le H Y warm.soon lower.soon result.local_).1
  have eq:=Mutation.reads M₁ (Γ i) ζ h₀ order gf gc w₁ grades calibrated stock lower.bloom.le widthPos
      H Y warm.soon lower.soon result.local_
  have homes:=Mutation.pencil (Γ i) ζ h₀ order gf gc H X actors pieces M₁ Y result.school result.repair result.force
  have swap:Stoop.radius w₁ (Ω^5)=w₂:=by
    funext v
    unfold Stoop.radius
    rw [div_div]
    congr 1
    ring
  have good:=one_le_pow₀ (n:=5) one
  refine ⟨swap ▸ issued.stored good,Mutation.fidelity (Γ i) ζ h₀ order actors pieces M₁ result.school,homes.2,
    result.force,swap ▸ Stoop.tighten w₁ (carried).old stock.positive good rental,result.kept,rfl,?_⟩
  intro x
  exact (result.reads x).trans (congrFun eq x)

end YM.Integration.WilsonOriginalReceivedMeasuredCarry
