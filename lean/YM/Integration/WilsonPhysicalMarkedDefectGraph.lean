import YM.Integration.WilsonPhysicalMarkedDefect
import YM.Integration.FVA1Physical.MixedResets.LessonPaid

/-! A prescribed successive graph is computed from the incoming graph, the
physical vacuum parameters and the previously purchased formal change of
coupling. It can be named before any output error register is constructed.
This version keeps the declared index and address, not only Taylor coefficients. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice Kinetic.Port
open Progress.ClassicalKin Progress.ClassicalKin.Tent Pressure Next.Scheduling Next.Scheduling.Clock
open AnalyticBridge VerifiedReset Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open QuadraticLocal.Syl Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree Oak FVA1Physical.MixedResets
open scoped Topology BigOperators Classical

/-- The supported analytic representative; the physical marked residual has a
different index and is deliberately not an argument. -/
structure MarkedGraph (G : Gauge) (n : Side) {V : Type} [DecidableEq V]
    (marks : Census V) (X : Type) : Type 1 where
  address : Passport n V
  index : Type
  rows : index → Row address marks G X

def reportedGraph {G : Gauge} {n : Side} {V X : Type} [DecidableEq V]
    {marks : Census V} {P : Rep G n} (packet : Pupil P marks X) : MarkedGraph G n marks X :=
  ⟨packet.address, packet.index, packet.painter⟩

/-- The vacuum order is bought before the range, fields, test or outgoing
packet. Extra changes of scheme do not have to consume marked orders. -/
theorem orders (p depth count : ℕ) :
    ∃ k : ℕ, ∃ s : School k, s.order = p ∧ depth ≤ s.horizon ∧ s.pieces = count ∧
      s.order + 4 ≤ Burn.horizon k + 2 := by
  let k := p + depth + count + 4
  let s : School k := ⟨p, count, max depth 4, by unfold Burn.horizon k; omega,
    by unfold Burn.horizon k; omega, by unfold Burn.horizon k; omega⟩
  exact ⟨k, s, rfl, le_max_left _ _, rfl, by change p + 4 ≤ 3*k + 2; omega⟩

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
    {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
    (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
    {V : Type} [Fintype V] [DecidableEq V] {marks : Census V}
    {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
    (allow : ∀ v, Set (X v)) (kills : ∀ v, Submodule ℝ (X v)) (w : V → ℝ)
    (grades : V → ℕ) (school : School k) (old η : ℝ) (hardOrder : ℕ)
    (f : Pupil (Ψ (i+1)) marks (Affinity.Wallet allow)) (aperture : ℝ)
    (e : Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ (Stoop.radius w aperture) old f)

local notation "stage" => (School.room school (PriceCompiler.step_paid R.alloy.B.a i)
  (J.trans (R.alloy.B.a.fits.mono hi)))
local notation "approved" => (voters R J D Ψ (φ:=φ) hi allow kills (Stoop.radius w aperture)
  grades school 1 1 f (Ribbon.seed e))

/-- Source prescription for this particular step: all nonlinear curvature
completions, local addresses and actual reset powers precede the output packet. -/
def nextGraph : MarkedGraph G (R.family.side i n) marks (Affinity.Wallet allow) :=
  ⟨f.address.coarser (R.family.path.levels.clock.op i n).ratio, _,
    Oak.Buffered.born (n:=n) R J D Q π Γ clock hi stage L ahead allow f.painter school.order approved⟩

local notation "prescribed" => (nextGraph R J D Q π Γ Ψ clock ahead hi L allow kills w grades school old f aperture e)
local notation "forecast" => (Route.reexpress R N (Burn.horizon k+2) (π (i+1)) f.painter school.order
  (Route.calibrator R D Q J π Γ hi L))

variable (forest : Tree.Forest (Route.step R i n).ratio)
    (out : Pupil (Ψ i) marks (Affinity.Wallet allow))
    (step : InvoiceHistory R J D Q π Γ Ψ clock ahead hi cut L allow kills w grades school
      old η hardOrder f aperture e forest out)

include step

/-- Every actual output (not just a freely chosen model with the same Taylor
series) has exactly these prescribed signed rows and exactly these supports. -/
theorem prescribed_graph : reportedGraph out = prescribed := by
  obtain ⟨j, count, entered, actual, _, _⟩ := step.certificate
  subst out
  rfl

/-- On this *prior* graph the formal coefficients through the appointed order
are the independently computed rebased Wilson cover step evaluated on the
previous graph. `Renderer.realizes` also asserts the actual signed HasSum for
each coefficient and every independently prescribed Lie field. -/
theorem prescribed_cover : Renderer (prescribed).rows (π i) (Step.tape (Burn.horizon k+2)) grades
    school.order forecast := by
  obtain ⟨j, count, entered, actual, _, _⟩ := step.certificate
  subst out
  exact step.wilson

/-- Once the true prior is known, the full measured source includes the old
charged ordinary and forced insertions. This is the normalized physical field,
not the Taylor series or a replacement bare seed placed at an interior scale. -/
theorem measured_short (x : Affinity.Wallet allow) (v : V) (U : Config G (R.family.side i n))
    (healthy : Healthy (Ψ i).p.threshold (halo (2*(Ψ i).p.B+10) {(prescribed).address.origin v}) U) :
    (((Route.step R i n).push (Ψ (i+1)).beta ((Tint.Patrol.picture f.painter f.packet).density x)) U).part
        (marks.fire v) / ((Ψ i).eval U : ℂ) -
      shortCoefficient (prescribed).rows (Ψ i).p (Coat.gStep (Ψ i).beta) (marks.fire v) x U =
      longRead (prescribed).rows (Ψ i).p (Coat.gStep (Ψ i).beta) (marks.fire v) x U +
        ((remainderGallery (Ψ i) out.packet).density x U).part (marks.fire v) / ((Ψ i).eval U : ℂ) := by
  have entrance := step.at_work x
  obtain ⟨field, positive, vacuum, _, _⟩ := entrance
  obtain ⟨j, count, entered, actual, _, _⟩ := step.certificate
  subst out
  rw [← field]
  apply healthy_singleton _ step.currency (by norm_num)
    (Lamps.tenure _ _ step.currency.positive step.whole (by linarith)) x v U _ healthy
  rw [vacuum]
  exact positive U

end YM.Integration.WilsonPhysicalMarkedDefect

