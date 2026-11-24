import YM.Integration.WilsonMeasuredOwnerArrival
import YM.Integration.WilsonReceivedForcedExit
import YM.Integration.WilsonMeasuredOwnerReserve

/-! The actual singleton forced source on the dated Wilson vacuum has a counted,
filed marked successor, with all of its original compulsory partners. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerReturn
open YM.Integration.WilsonMeasuredOwnerReserve
open Labels Source WilsonPhysicalMarkedDefect.RegularProjection
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

local notation "incoming" => Ψ (i+1)
local notation "κ₁" => LocalComparison.forcedDivisor R.family (i+1)
local notation "κ₀" => LocalComparison.forcedDivisor R.family i
local notation "cash" => R.family.path.levels.clock.forcedAllowance (i+1)
local notation "labels₁" => Stock.census (Fin 1)
local notation "temperature" => R.alloy.B.a.clock.hatBeta (i+1)
variable (y : Site (R.family.side (i+1) per))
local notation "E₁" => Earn.Passport.point (fun _:Fin 1=>y)
local notation "model₁" => (Empty.elim : Empty → Row (E₁) (labels₁) G (Wallet disk))
local notation "canonical" => R.family.path.rep N per (i+1)

/-- Full marked return on the same opportunity as an original physical post. The new
hard income is restored to its original test radii. The reference field in the signed
source uses the canonical measured representation at that very mesh. -/
theorem original (v : V) (live : i<N) (simple : G.Simple)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load : seats ≤ Burn.horizon k+2) (shelfFit : shelf ≤ R.alloy.B.a.clock.J i)
    (way : WayStation R.kit) (small : cash≤κ₁/2)
    {d : ℕ} {F : Frame G d} (S : SectionData F) (A : Hol G)
    (q : Coefficient F (R.family.side (i+1) per)) (law : q.Format y A (incoming))
    (M w : ℝ) (bill : q.remBound y (incoming) (κ₁) M) (rad : 0<w) (fit : w*M≤1/2)
    {τ : ℝ} (positive : 0<τ) (bounded : τ≤1) :
    ∃ (Z : Tint.Incoming (E₁) (incoming) (Wallet disk) Empty (labels₁))
      (L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disk kernel
          (fun _ => 0) order shelf seats i floor ((Tint.Patrol.picture (model₁) Z).density)),
      L.op=P.op ∧ L.lesson=P.lesson ∧ L.passport=(E₁) ∧ L.w=(fun _=>w) ∧
      L.cost=0 ∧ L.rent=τ ∧ L.inputIndex=Empty ∧ HEq L.input Z ∧ Countable L.inputIndex ∧
      (∀ (x:Wallet disk) U,
        ((Tint.Patrol.picture (model₁) Z).density x U).part (labels₁).quiet=(incoming).eval U ∧
        ((Tint.Patrol.picture (model₁) Z).density x U).part ((labels₁).fire 0)=
          test x*(q.density y S (incoming) U-(soft q).density y S (canonical) U)) ∧
      ∀ s : ℕ,s+6*seats≤R.alloy.B.a.clock.J i →
        L.output.hard.Paid L.w (Ψ i).p.B (Ψ i).p.supportExponent ((temperature)^(-(s:ℝ))*(κ₀)) := by
  have one : 1≤P.op.count := by simpa [Census.fire] using P.voter.room ((Stock.census V).fire v)
  have paid : Scene.Ministry (labels₁) (fun _=>0) P.op.count shelf := by
    refine ⟨fun m=>?_,fun m=>?_⟩
    · exact (show m.val.card ≤ 1 by simpa using m.val.card_le_univ).trans one
    · simp
  obtain ⟨Z,letters,hard,row,forced,actual⟩:=WilsonMeasuredOwnerReserve.original R π Γ Ψ course
    (floor.trans i.le_succ) live small S A y q law M bill w rad fit
  let sample : Wallet disk := fun _=>⟨1,by simp [disk]⟩
  obtain ⟨L,op,lesson,stamp,radius,cost,rent,old,identical,countable⟩:=
    WilsonMeasuredOwnerArrival.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor
      physical P disk kernel (fun _=>0) paid (fun _:Fin 1=>y) live simple course scroll chamber hospital
      load shelfFit sample (fun _=>w) (fun _=>rad) Z row (Spill.Foundry.empty_lit (incoming) Z _ _)
      forced letters hard positive bounded
  refine ⟨Z,L,op,lesson,stamp,radius,cost,rent,old,identical,countable,actual,fun s active=>?_⟩
  exact WilsonReceivedForcedExit.original R hk D Q π Γ Ψ books ahead disk kernel (fun _=>0) order shelf seats floor
    ((Tint.Patrol.picture (model₁) Z).density) L live way course s active

end YM.Integration.WilsonMeasuredOwnerReturn
end
