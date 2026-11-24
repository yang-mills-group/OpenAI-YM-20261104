import YM.Integration.WilsonOriginalThermometerTopPost
import YM.Integration.WilsonReceivedForcedUnit

/-! A marked hard source is booked on the incoming measured representation with the
same opportunity and lesson. Its analytic painter has no rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerArrival
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Progress.DirectedRecipe QuadraticLocal.Tint

variable {I : Type} [Fintype I] [DecidableEq I] {F : I → Type}
  [∀v, AddCommGroup (F v)] [∀v,Module ℝ (F v)]
  (families : ∀v, Set (F v)) (subspaces : ∀v, Submodule ℝ (F v)) (degrees : I→ℕ)
  (wallet : Scene.Ministry (Stock.census I) degrees P.op.count shelf)
local notation "upper" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable (o : I → Site (R.family.side (i+1) per))
local notation "births" => Earn.Passport.point o
local notation "bareModel" => (Empty.elim : Empty → Row (births) (Stock.census I) G (Wallet families))
include wallet in
private theorem subjects (w : I → ℝ) (hw : ∀v,0<w v) :
    Scene.Armada (bareModel) w degrees (σ₀) 0 order P.op.count shelf ∧
    Cruise.Voter (bareModel) (σ₀) order P.op.count P.op.stage k (R.alloy.B.a.clock.J i) ∧
    Tableau subspaces families (bareModel) := by
  refine ⟨⟨wallet,hw,fun x=>?_,⟨fun j=>j.elim,fun j=>j.elim⟩,fun j=>j.elim⟩,
    ⟨fun j=>j.elim,wallet.quota,P.voter.height,fun C=>?_⟩,⟨fun j=>j.elim⟩⟩
  · exact ⟨fun j=>j.elim,Summable.of_finite,by simp⟩
  · obtain ⟨j,-⟩:=C.property.1
    exact j.elim

include wallet in
/-- The source and its real paid incoming hard gallery are carried through the actual
measured block together. The hard allowance is spent once on the whole marked gallery. -/
theorem original (live : i<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats ≤ Burn.horizon k+2) (shelfFit : shelf ≤ R.alloy.B.a.clock.J i)
    (sample : Wallet families) (w : I → ℝ) (hw : ∀v,0<w v)
    (Z : Tint.Incoming (births) (upper) (Wallet families) Empty (Stock.census I))
    (row : Z.old.Paid w (upper).p.B ((upper).p.supportExponent+1+1) 0)
    (base : Z.old.Paid w (upper).p.B (upper).p.supportExponent 0)
    (full : Z.hard.Paid w (upper).p.B (upper).p.supportExponent (LocalComparison.forcedDivisor R.family (i+1)))
    (letters : Taut (births).support families subspaces Z.old)
    (fonds : Crown (births).support families subspaces Z.hard)
    {τ : ℝ} (positive : 0<τ) (bounded : τ≤1) :
    ∃ L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead families subspaces degrees
        order shelf seats i floor ((Tint.Patrol.picture (bareModel) Z).density),
      L.op=P.op ∧ L.lesson=P.lesson ∧ L.passport=(births) ∧ L.w=w ∧ L.cost=0 ∧ L.rent=τ ∧
      L.inputIndex=Empty ∧ HEq L.input Z ∧ Countable L.inputIndex := by
  obtain ⟨salary,voter,test⟩:=subjects R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P families subspaces degrees wallet o w hw
  have actual := P.salary.suggests (0:Site (R.family.side (i+1) per))
  have cost : 0≤P.cost := (tsum_nonneg actual.1).trans actual.2.2
  have allowance := (Graces.glyphBound R.alloy.B.a (i+1)).2
  let cal := Classical.choice (Oak.agrees R hk D Q π Γ Ψ course floor live P.lesson)
  obtain ⟨J,countable,out,post⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber floor live
    P.op P.lesson cal ahead hospital families subspaces (bareModel) Z w degrees order shelf voter τ 0
    (P.capacity.trans_le load) shelfFit salary test sample letters fonds (Z.old.loan_monotone base positive.le)
    (Hard.mono _ full allowance) zero_le_one positive bounded
  let L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead families subspaces degrees
      order shelf seats i floor ((Tint.Patrol.picture (bareModel) Z).density) := {
    op := P.op
    capacity := P.capacity
    lesson := P.lesson
    passport := Earn.Passport.point o
    modelIndex := Empty
    inputIndex := Empty
    outputIndex := J
    modelCount := inferInstance
    outputCount := countable
    model := Empty.elim
    input := Z
    output := out
    w := w
    cost := 0
    rent := τ
    affordable := cost.trans P.affordable
    active := positive
    small := bounded
    voter := voter
    salary := salary
    tests := test
    oldTests := letters
    hardTests := fonds
    regular := Z.old.loan_monotone row positive.le
    forced := full
    represented := fun _=>rfl
    issued := post }
  exact ⟨L,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,inferInstanceAs (Countable Empty)⟩

end YM.Integration.WilsonMeasuredOwnerArrival
end
