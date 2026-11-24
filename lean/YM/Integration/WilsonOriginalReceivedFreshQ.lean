import YM.Integration.WilsonOriginalRightBirthLamp
import YM.Integration.WilsonOriginalMixedTestTableau
import YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada

/-! The charged, independently placed fresh curvature source in the mixed
wallet. Its unmasked value is the source at its actual coupling on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFreshQ
open Function Filter Finset Lattice Wilson RG Marker Source Labels Push
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureLamps
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p ℓ n : ℕ} {hn : n ≤ ℓ} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p ℓ n hn V)
  (labels : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (σ : ℝ) (extra : V → ℕ)
  {E : V → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
  (A : ∀ i, Set (E i)) (K : ∀ i, Submodule ℝ (E i))
  (P : Passport (R.family.side ℓ p) V) (old fresh : Finset V) (apart : Disjoint old fresh)
local notation "G₁" => WilsonOriginalProjectedCurvatureTableau.actors D
local notation "L₁" => (fun i => (WilsonOriginalProjectedCurvatureTableau.nulls D i).restrictScalars ℝ)
local notation "T₁" => WilsonMixedTestTableau.actors A G₁
local notation "t₁" => WilsonMixedTestTableau.right A G₁ fresh (WilsonOriginalMixedTestTableau.zero D)
local notation "J₀" => WilsonMixedPassportRows.passport (WilsonMixedPassportRows.owner P (paper D labels) old)
local notation "Y" => cohort Q D labels μ orders N σ extra
local notation "X" => WilsonOriginalRightBirthLamp.rows A G₁ Y P old fresh apart (WilsonOriginalMixedTestTableau.zero D)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p ℓ
local notation "r₀" => ActualOriginalQLayout.rankCap R labels
local notation "toll" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) labels
local notation "v₀" => Fintype.card V*toll
local notation "head" => r₀+v₀+1

def birth (point : BudgetPoint) := rendered X point g₀
local notation "𝓑" => birth Q D labels μ orders N σ extra A P old fresh apart

structure Posted (point : BudgetPoint) (w : V → ℝ) (regular gross : ℝ) : Prop where
  salary : (𝓑 point).Paid w point.B (point.supportExponent+1+1) regular
  full : WilsonRootedKioskOccupiedSlip.Gross (𝓑 point) w point.B (point.supportExponent+1) gross
  affine : Taut (J₀).support T₁ (WilsonMixedTestTableau.pieces K L₁) (𝓑 point)
  source (x : Wallet T₁) (U : Config G (R.family.side ℓ p)) :
    WilsonRootedKioskOccupiedSlip.bare (𝓑 point) x U = Mach (Stock.census V) (fun i =>
      ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) (t₁ x) i) *
      ActualOriginalCalibratedColumns.weightedObservable R B Q (labels i) μ (R.family.side ℓ p)
        (ActualRunQlocalNativeTuple.root D i) U (orders i))

theorem original (point : BudgetPoint) (atDate : ℓ ≤ N) {w u : V → ℝ} {x θ c : ℝ}
    (book : Scene.Armada Y w (fun _ => toll) σ c r₀ (Fintype.card V) v₀)
    (positive : ∀ i, 0 < u i) (fits : ∀ i ∈ fresh, u i ≤ w i)
    (invoice : Invoice.Supports point x (point.supportExponent+1+1) g₀ σ θ) :
    let regular := Invoice.price point x (head) (Fintype.card V) (point.supportExponent+1+1) θ G * c
    Posted Q D labels μ orders N σ extra A K P old fresh apart point u regular (Spill.allOver point ^ (head) * regular) := by
  intro regular
  have funded := WilsonOriginalRightBirthLamp.tariff A G₁ Y P old fresh apart
    (WilsonOriginalMixedTestTableau.zero D) book positive fits
  have test := WilsonOriginalProjectedCurvatureTableau.real D Q labels μ orders N σ extra
  refine ⟨Scene.Armada.paid X u _ funded point invoice,?_,?_,?_⟩
  · exact WilsonOriginalRightBirthLamp.gross X point funded invoice (by linarith)
  · exact (WilsonOriginalRightBirthLamp.tested A G₁ K L₁ Y P old fresh apart
      (WilsonOriginalMixedTestTableau.zero D) test).line point g₀
  · intro t U
    have ungated := WilsonOriginalRightBirthLamp.unmasked A G₁ L₁ Y P old fresh apart
      (WilsonOriginalMixedTestTableau.zero D) test point g₀ t U
    exact ungated.trans (WilsonOriginalProjectedCurvatureLamps.original Q D labels μ orders N σ extra point (t₁ t) U atDate)

end YM.Integration.WilsonOriginalReceivedFreshQ
