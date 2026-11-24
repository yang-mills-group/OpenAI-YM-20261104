import YM.Integration.FVA1Physical.MixedResets.LessonVac
import YM.QuadraticLocal.Rebirth.Pipe

/-!
# Local model identification on the Run

given the CP5 painter (`pupil` publisher following Lesson program), its
incoming stencil receipt and arity budgets, it can now be used at an EXACT rather than seam
projection. At both pre/post coordinates. Still need separate geometry purchases
ahead and application to the actual running representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ}
variable (pay : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : pay.Tab R.rolls)
  (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (hi : m ≤ i) (L : Oak.Lesson (N:=N) R J pay Q π Γ hi)
  {Ψ : ∀ i, RG.Rep G (R.family.side i n)}
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ) (cut : i < N)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "xStage" => R.alloy.B.a.clock.J (i+1)
local notation "yStage" => R.alloy.B.a.clock.J i
local notation "Y" => (RunFormalChain.fromRun R)
local notation "C" => Route.step R i n
local notation "p₀" => (Burn.horizon k+2)
local notation "T" => Step.tape p₀
local notation "cWorking" => R.family.side i n

variable {φ : ℕ → ℕ}
variable (clock : QuadraticLocal.Mentor.Offices.Books pay R.rolls Q φ)
  (capacity : QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  {V ι : Type} [Fintype V] [DecidableEq V] {I : Marker.Census V}
  {A : Passport (R.family.side (i+1) n) V}
  {W : V → Type} (allowed : ∀ i, Set (W i))
  (rows : ι → Earn.Row A I G (Affinity.Wallet allowed)) {p : ℕ}
  (voter : Cruise.Voter rows
    (Poetry.Agenda.seed pay φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p capacity.count capacity.stage k (R.alloy.B.a.clock.J i))
  (forecast : Mentor.Forecast pay R.rolls Q φ clock)
  {w w' : V → ℝ} (grades : V → ℕ)
local notation "out" => Oak.student (n:=n) R J pay Q π Γ clock hi capacity L forecast allowed rows p voter
local notation "new" => Oak.Buffered.born (n:=n) R J pay Q π Γ clock hi capacity L forecast allowed rows p voter
local notation "prints" => Cruise.publish pay R.rolls Q R.alloy φ clock capacity
    (Oak.era R J pay Q π Γ hi capacity L) ((σ).S.oneStep i n).exact_size rows p voter L.entry
local notation "g" => (Route.action R N (i+1) n)
local notation "a" => (Route.clip R N (i+1) n)
local notation "O" => R.metals.O
local notation "lo" => (π (i+1))
local notation "bill" => Route.wilson R N p₀ (π (i+1)) rows p
local notation "Cal" => Route.calibrator R pay Q J π Γ hi L
local notation "newBill" => (Route.reexpress R N p₀ (π (i+1)) rows p Cal)

set_option maxHeartbeats 740000

include conc cut
lemma born_renders {pieces k' : ℕ} {funds funds' : ℝ}
    (paid : Earn.Scene.Armada out w grades (Poetry.Agenda.seed pay φ (Burn.horizon k) yStage) funds p pieces k')
    (refund : Earn.Scene.Armada new w' grades (Poetry.Agenda.seed pay φ (Burn.horizon k) yStage) funds' p pieces k')
    (reset : ∀ t z, Tutoring.Rollback R J pay Q π Γ clock hi capacity L forecast allowed rows grades p voter t z) :
    Renderer out (π i) T grades p bill ∧
    Renderer new (π i) T grades p newBill := by
  let ready := (student_renders R pay Q J π Γ hi L conc cut clock capacity allowed rows voter forecast paid).1
  exact ⟨ready, reset_renderer Cal p₀ p refund (Poetry.Agenda.stem pay φ (Burn.horizon k) yStage) ready
    (fun r order t z t' => (reset t z).2 r order t')⟩

section seam
local notation "yLink" => rule (Coarse G) (R.family.side i n)
local notation "Wcns" => Affinity.Wallet allowed
local notation "δ" v:max t:max y:max z:max => Route.datum R N p₀ lo rows grades v t cut y z

/-- Exact link to the *other* convention (raw finite-volume `Datum` on this very R with
true path orientation). Cover recursion pays this additional conditional alias when comparing
to that valuation. This identity is *not* the estimate on represented inputs: in particular the
norm here is on the seam at each field; use the estimates on `out`/`new` instead. -/
structure PinnedSeam (weights : V → ℝ) (F : Tree.Forest (C).ratio) (tag : (C).Choices)
    (q : ℝ) (z : rule (Coarse G) cWorking) (t : Affinity.Wallet allowed) : Prop where
  alias_bill (r : ℕ) (order : r ≤ p) :
    let seen := (Order.observe I p ((Route.datum R N p₀ lo rows grades F tag cut t z).markedLog (RunFormalChain.fromRun R) p) r)
    let E := Route.winding R N p₀ lo rows F tag cut t z p r
    HasSum E (seen - (bill r t z)) ∧ Poly.price weights (seen - (bill r t z)) ≤
      Tutoring.bill R J pay Q π Γ clock hi capacity L z q ∧ SumBudget (fun i => Poly.price weights (E i))
        (Tutoring.bill R J pay Q π Γ clock hi capacity L z q)
  shape : ‖z‖ ≤ ((σ).clock.hatBeta (i+1))^ (R.alloy.B.a.clock.J (i+1)) →
    Tutoring.bill R J pay Q π Γ clock hi capacity L z q ≤ ((σ).clock.hatBeta (i+1))^(-(R.alloy.B.a.clock.J (i+1) : ℝ))

lemma also_seam (F : Tree.Forest (C).ratio) (tag : (C).Choices)
    (weights : V → ℝ) {q funds : ℝ} {pieces k' : ℕ} (z : rule (Coarse G) cWorking) (t : Affinity.Wallet allowed)
    (seam : Tutoring.Unearthed R J pay Q π Γ clock hi cut capacity L forecast allowed rows weights grades p voter q t F tag z)
    (paid : Earn.Scene.Armada out w grades (Poetry.Agenda.seed pay φ (Burn.horizon k) yStage) funds p pieces k') :
    PinnedSeam R pay Q J π Γ hi L cut clock capacity allowed rows (p:=p) grades weights F tag q z t := by
  let boolOK := issued_writes R pay Q J π Γ hi L conc cut clock capacity rows voter
  refine ⟨fun r order => ?_, fun h => seam.numbers h⟩
  intro seen E
  obtain ⟨e,he,hp,hE,hq⟩ := seam.current r order
  have renderer := (student_renders R pay Q J π Γ hi L conc cut clock capacity allowed rows voter forecast paid).1
  let Ystep := (RunFormalChain.fromRun R).step N i n cut
  -- expose defeq with Datum only by forcing the expected Poly type;
  -- no switching the marker/symbol choices.
  have heq := (renderer.coefficients r order t z)
  have sees : seen = bill r t z + e := he.trans (congr_arg (· + e) heq)
  let M := Alliance.miss rows (fun j => (rows j).paint t) (Route.step R i n|>.ratio) Ystep F tag z (π (i+1)) T prints r
  have aligned : M = E := seam_diff rows t prints boolOK order (tag:=tag) (F:=F) («g»:=Ystep) (z:=z)
  have hm : HasSum M e := hE
  have eq : seen - bill r t z = e := by rw [sees]; abel
  rw [eq, ← aligned]
  exact ⟨hm,hp,hq⟩
end seam
end YM.Integration.FVA1Physical.MixedResets
