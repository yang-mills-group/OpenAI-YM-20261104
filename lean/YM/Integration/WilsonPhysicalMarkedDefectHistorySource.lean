import YM.Integration.FVA1Physical.MixedResets.SchoolTerm
import YM.MergeProof.South.Window

/-! The measured polynomial along a licensed trajectory is determined by its
complete original upper signed field. Every step uses the same true stored
vacuum beta, including the full signed correction from the preceding station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect
open FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k b N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (below : i<b) (birth : b ≤ N) (L : ∀ j, ∀ h:m ≤ j, j<b → Lesson (N:=N) R J D Q π Γ h)

set_option quotPrecheck false
open QuadraticLocal.Syl
open RG3 RG3.Annuncia
variable {Θ V : Type} [Fintype Θ] [DecidableEq Θ] [Fintype V] [DecidableEq V] {R₀ : Marker.Census V}
    (f₀ : Θ → V) {X : V → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
    (atV : ∀ i, Set (X i)) (killV : ∀ i, Submodule ℝ (X i))
    (wV : V → ℝ) (hw : ∀ i, 0 < wV i) (η : V → ℕ) (school : School k)
    (uP : ∀ i:ℕ,i ≤ b → Earn.Passport (R.family.side i n) V) (ε ηz : ℝ) (s : ℕ)
    (H : ∀ i:ℕ, m ≤ i → i≤b→ Pupil (Ψ i) (Replica f₀ R₀) (Affinity.Wallet (fun i=>atV (f₀ i))))
local notation "allow" => (fun i => atV (f₀ i))
local notation "kills" => (fun i => killV (f₀ i))
local notation "grades" => (η ∘ f₀)
local notation "w₀" => (wV ∘ f₀)
local notation "Lh" => (L i hi below)
variable (sx : ℕ) (eta : ℝ)
  (initial : Pupil (Ψ b) (Replica f₀ R₀) (Affinity.Wallet (fun i=>atV (f₀ i))))
  (Xb : Earn.Passport (R.family.side b n) V) (hXb : initial.address=Tariff.clone f₀ Xb)
  (hP : Academy.physicalCourse R Xb uP) (motive : m≤b)
  [Nonempty (Affinity.Wallet (fun i=> atV (f₀ i)))]

local notation "grad" => (Graduate R J D Q π Γ Ψ clock ahead birth L f₀ atV killV wV η school
  uP ε ηz s H sx eta initial Xb hXb hP motive)
local notation "pic" X:max => (Tint.Patrol.picture (Pupil.painter X) (Pupil.packet X))
include conc

/-- No pointwise comparison of independently selected interior representations is
required. The actual `Graduate.paid` fixes the upper datum and each full signed
one-step transfer is the native `InvoiceHistory.at_work` on this same trajectory. -/
theorem history_source (track : grad) (span : i ≤ b) (x : Affinity.Wallet allow) :
    (pic (H i hi span)).density x =
    MergeProof.Accent.gust R.family.path N n b ((pic initial).density x) i span := by
  induction span using Nat.decreasingInduction with
  | self =>
    rw [track.paid hi le_rfl, MergeProof.Accent.gust_base]
  | of_succ j hj ih =>
    let op := Route.step R j n
    let F : Tree.Forest op.ratio := Classical.choice (Tree.select _ op.patch.odd_side)
    obtain ⟨e,invoice⟩ := ((track.budgets j hi hj).witness F).instructor
    have charged := (invoice.at_work x).1
    rw [MergeProof.Accent.gust_step R.family.path N n b _ hj]
    rw [charged, ih (Nat.le_succ_of_le hi)]
    rw [(later R π Γ Ψ conc (Nat.le_succ_of_le hi) (le_trans hj birth)).beta]
    rfl

end YM.Integration.WilsonPhysicalMarkedDefect
