import YM.Integration.WilsonThermometerMixedProgram
import YM.QuadraticLocal.Relative.Tandem

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedOutlet
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
  {ι : Type} {marks : Census (Fin 3)} {X : (Fin 3) → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side (i+1) per) (Fin 3)}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : (Fin 3) → ℝ) (grades : (Fin 3) → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
variable (cost:ℝ) {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next marks)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf

local notation "fine" => Ψ (i+1)
local notation "coarse" => Ψ i
local notation "width" => (fine).p.supportExponent
local notation "level" => (fine).p.B
variable [Countable ι] [Countable old]
open WilsonThermometerMixedProgram WilsonThermometerMixedShoulder

include course cut in
theorem original (simple : G.Simple) (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (limit:op.count ≤ Burn.horizon k+2) (slips:shelf ≤ R.alloy.B.a.clock.J i)
    (clock:order ≤ Burn.horizon k+1)
    (stock:Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) cost order op.count shelf)
    (legal:Tableau pieces actors M)(sample:Wallet actors)
    (rows:Taut passport.support actors pieces Z.old)(flags:Crown passport.support actors pieces Z.hard)
    (affordable:cost ≤ 1)(salt:0 < rent)(room:rent ≤ 1)
    (reg : old → marks.Mode → Prop)(owners : ℕ → marks.Mode → Prop)
    {e δ K:ℝ}(common:Z.old.Paid w (level) (width) e)
    (mixed:(WilsonPrecontactSeparatedLamps.portion Z.old (picked Z.old reg)).Paid w (level) (width) δ)
    (forced:Z.hard.Paid w (level) (width) K)
    (c:ℂ)(er:e+‖c‖*δ ≤ rent)(hr:max 1 ‖c‖*K ≤ 1) :
    ∃ (J:Type),Countable J ∧ ∃ out,
       Oak.Buffered.Tandem R hk D Q π Γ Ψ books hi op lesson ahead actors pieces M
         (intake c reg owners Z) w grades order shelf voter rent cost Set.univ (J:=J) out:=by
  have A:=WilsonThermometerMixedProgram.admissible actors pieces Z reg owners c rows flags
  have L: (intake c reg owners Z).old.Paid w (level) (width) rent:=
    Lamps.loan_monotone _ (WilsonThermometerMixedShoulder.regular Z.old reg c stock.positive common mixed) er
  have force : (intake c reg owners Z).hard.Paid w (level) (width) 1:=
    Hard.mono _ (WilsonThermometerMixedShoulder.forced Z.hard owners c forced) hr
  let cal:=Classical.choice (Oak.agrees R hk D Q π Γ Ψ course hi cut lesson)
  exact Oak.Buffered.pares R simple hk D Q π Γ Ψ course scroll books chamber hi cut op lesson cal ahead
    hospital actors pieces M (intake c reg owners Z) w grades order shelf voter rent cost limit slips stock
    legal sample A.1 A.2 force affordable salt room Set.univ month clock
    (Deletion.owed Set.univ _ L) (Lamps.loan_monotone _ L room)

end YM.Integration.WilsonThermometerMixedOutlet
end
