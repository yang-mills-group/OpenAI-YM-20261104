import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.Integration.WilsonMovingMentorCurvatureWord

/-! The actually issued complete marked density in the old course has the
ordinary physical conditional for the registered curvature insertion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorFoundryTransport
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof MergeProof.Accent MergeProof.Replicums FVA1 QuadraticLocal QuadraticLocal.Earn
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open WilsonOriginalProjectedCurvaturePassport AllOrder AllOrder.Floe AllOrder.Transit.WheelP
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {m N per k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
  {H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per)} {L n j : ℕ} {hn : n ≤ L}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R per L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (σ : ℝ) (extra : V → ℕ)

local notation "X₀" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "q₀" x:max U:max => Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader D v (testInclusion (ActualRunQlocalNativeTuple.orbit D) x v) *
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u v) μ (R.family.side L per)
      (ActualRunQlocalNativeTuple.root D v) U (orders v))

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k H)
    (within : m ≤ j) (below : j ≤ L) (live : L ≤ N) (simple : G.Simple)
    (ready : ∀ a : Slot u, R.family.ref a.2.size ≤ L)
    (incoming : Tint.Incoming (paper D u) (H L) (tastes D) Empty (Stock.census V))
    (issued : ∀ (x : tastes D) (U : Config G (R.family.side L per)),
      (Tint.Patrol.picture X₀ incoming).density x U =
        ((ActualOriginalQInput.input Q D u μ orders simple N live).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U)
    (x : tastes D) (exterior : Config G (R.family.side L per) → ℂ)
    (read : Poly (Stock.census V) →ₗ[ℂ] ℂ) (W : Config G (R.family.side j per)) :
    ((H j).eval W)⁻¹ • gust R.family.path N per L
      (fun U => exterior U * read ((Tint.Patrol.picture X₀ incoming).density x U)) j below W =
      actualTransport R.family (N:=N) (fun U => exterior U * read (Poly.pass (q₀ x U))) below W := by
  simp only [issued]
  exact WilsonMovingMentorCurvatureWord.original R Q D u μ orders course within below live simple ready x exterior read W

local notation "P₀" => H L
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per L

theorem purchased (course : Concourse R.alloy R.kit R.T π Γ m N per k H) (opened : m ≤ L)
    (live : L ≤ N) (simple : G.Simple) (ready : ∀ a : Slot u, R.family.ref a.2.size ≤ L)
    {w : V → ℝ} {t : V → ℕ} {f b z c θ d : ℝ} {q h v : ℕ}
    (existing : Hard.Install (P₀).activities (P₀).p f b)
    (salary : Scene.Armada X₀ w t σ c q h v)
    (invoice : Invoice.Supports (P₀).p z ((P₀).p.supportExponent+1) g₀ σ θ) (unit : 1 ≤ d)
    (financed : Spill.allOver (P₀).p^(q+v+1) *
      (Invoice.price (P₀).p z (q+v+1) h ((P₀).p.supportExponent+1) θ G*c) ≤ b*d) :
    ∃ incoming : Tint.Incoming (paper D u) (P₀) (tastes D) Empty (Stock.census V),
      incoming.hard.Paid w (P₀).p.B (P₀).p.supportExponent (d^h*f) ∧
      (∀ (x : tastes D) (U : Config G (R.family.side L per)),
        (Tint.Patrol.picture X₀ incoming).density x U =
          ((ActualOriginalQInput.input Q D u μ orders simple N live).leaf
            (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U) ∧
      ∀ a : ℕ, m ≤ a → ∀ lower : a ≤ L, ∀ (x : tastes D)
        (exterior : Config G (R.family.side L per) → ℂ)
        (read : Poly (Stock.census V) →ₗ[ℂ] ℂ) (W : Config G (R.family.side a per)),
        ((H a).eval W)⁻¹ • gust R.family.path N per L
          (fun U => exterior U * read ((Tint.Patrol.picture X₀ incoming).density x U)) a lower W =
          actualTransport R.family (N:=N) (fun U => exterior U * read (Poly.pass (q₀ x U))) lower W := by
  have entry := course.1.walk L opened live
  have measured : g₀ = ConnectedActivityE6.Coat.gStep (P₀).beta := by rw [entry.beta]; rfl
  obtain ⟨incoming,paid,data⟩ := WilsonOriginalProjectedCurvatureFoundry.original Q D u μ orders N σ extra
    (P₀) existing salary invoice unit financed measured entry.view simple live ready
  exact ⟨incoming,paid,data,fun a ha lower x ext read W =>
    original R Q D u μ orders σ extra course ha lower live simple ready incoming data x ext read W⟩

end YM.Integration.WilsonMovingMentorFoundryTransport
end
