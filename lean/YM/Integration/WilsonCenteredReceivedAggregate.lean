import YM.Integration.WilsonCenteredGalleryCapture
import YM.Integration.WilsonCenteredCountertermSlate
import YM.Integration.WilsonCenteredCourseKeeper
import YM.Integration.WilsonCenteredReceivedWages
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonCenteredDetectorUnit

/-! On the one dated physical Wilson post, file any complete marked subset
and actual finite counterterm. The raw numerator and the measured identity
scalar both retain the full original push.-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCenteredReceivedAggregate
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

private abbrev rowsOf {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {o : V→Site n} {P : Rep G n}
    {R : Census V} (_ : Gallery X ι o P R) := ι

private theorem unionCount {A B : Type} (a : Countable A) (b : Countable B) : Countable (A⊕B) :=by
  letI :=a
  letI :=b
  infer_instance

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple) (late : WilsonCenteredCaptureClock.first R simple ≤ i)
    (x : Wallet actors) (s : (Stock.census V).Mode) (counter : Finset V) (c : V→ℂ)
    (Z : Support (R.family.side i per)) (y : Site (R.family.side i per)) (center : y∈Z)
    (home : ∀j∈s.val,homes j∈Z) (zc : ∀j∈counter,homes j∈Z) (rad : ℕ)
    (near : ∀j∈s.val,separation (homes j) y≤rad) (nc : ∀j∈counter,separation (homes j) y≤rad)
    {d : ℕ} {F : Labels.Frame G d} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (Ψ i).p (R.family.side i per) μ) :
    ∃ A : Coefficient F (R.family.side i per), A.Format y Y (Ψ i) ∧
      A.remBound y (Ψ i) κ
        (WilsonCenteredGalleryCapture.fare (Ψ i).p S Y weights s counter c Z rad account κ (R.alloy.B.a.clock.forcedAllowance i) μ) ∧
      (∀ U,A.density y S (Ψ i) U=((value) (physical x) U).part s-∑j∈counter,c j*((value) (physical x) U).part ((Stock.census V).fire j)) ∧
      ∀ probe : Probe G d, probe.2.val=0 →
        runProbe F probe A.x=((Ψ i).eval (1:configuration):ℂ)⁻¹ *
          (((value) (physical x) 1).part s-∑j∈counter,c j*((value) (physical x) 1).part ((Stock.census V).fire j)) := by
  obtain ⟨hp,regular,hard⟩:=WilsonCenteredReceivedWages.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P way
  obtain ⟨K⟩:=WilsonCenteredCourseKeeper.original R course i hi cut
  have actual:=(course.1.walk i hi cut.le).truep
  obtain ⟨div,pos,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec i late
  rw [←actual.point] at room
  letI : Countable P.modelIndex :=P.modelCount
  letI : Countable (rowsOf (gauge)) :=by
    apply unionCount _ P.outputCount
    exact Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
      (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
      order P.voter P.lesson.entry P.lesson.studied ahead)
  obtain ⟨A,form,paid,receipt⟩:=WilsonCenteredGalleryCapture.original (ι:=rowsOf (gauge)) (gauge) x s counter c weights hp
    regular hard div pos room actual.valid K Z y center home zc rad near nc S Y reader
  have realSource U : A.density y S (Ψ i) U=((value) (physical x) U).part s-∑j∈counter,c j*((value) (physical x) U).part ((Stock.census V).fire j) := by
    have push:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
      seats i hi physical P x) U
    exact (receipt U).trans (congrArg (fun t : Poly (Stock.census V)=>t.part s-∑j∈counter,c j*t.part ((Stock.census V).fire j)) push.symm)
  refine ⟨A,form,paid,realSource,fun probe flat=>?_⟩
  exact (WilsonCenteredDetectorUnit.flatProbe A form reader.sound probe flat).trans
    (congrArg (fun z : ℂ=>((Ψ i).eval (1:configuration):ℂ)⁻¹*z) (realSource 1))

end YM.Integration.WilsonCenteredReceivedAggregate
