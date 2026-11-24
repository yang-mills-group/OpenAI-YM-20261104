import YM.Integration.WilsonMovingMentorMarkedPicture
import YM.Integration.WilsonOriginalProjectedCurvatureStartingField

/-! Positive transfer of the complete exponentiated original Wilson curvature input,
with a single actual incoming vacuum and an arbitrary signed exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorCurvatureWord
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 QuadraticLocal
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open WilsonOriginalProjectedCurvaturePassport AllOrder AllOrder.Floe AllOrder.Transit.WheelP
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {m N per k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
  {H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per)} {L n j : ℕ} {hn : n ≤ L}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R per L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

local notation "q₀" x:max U:max => Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader D v (testInclusion (ActualRunQlocalNativeTuple.orbit D) x v) *
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u v) μ (R.family.side L per)
      (ActualRunQlocalNativeTuple.root D v) U (orders v))

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k H)
    (within : m ≤ j) (below : j ≤ L) (live : L ≤ N) (simple : G.Simple)
    (ready : ∀ a : Slot u, R.family.ref a.2.size ≤ L)
    (x : tastes D) (exterior : Config G (R.family.side L per) → ℂ)
    (read : Poly (Stock.census V) →ₗ[ℂ] ℂ) (W : Config G (R.family.side j per)) :
    ((H j).eval W)⁻¹ • gust R.family.path N per L
      (fun U => exterior U * read (((ActualOriginalQInput.input Q D u μ orders simple N live).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U)) j below W =
      actualTransport R.family (N:=N) (fun U => exterior U * read (Poly.pass (q₀ x U))) below W := by
  have lower : (H j).eval = (R.family.path.rep N per j).eval :=
    (course.1.walk j within (below.trans live)).view
  rw [lower]
  unfold actualTransport
  apply congrArg (fun z : ℂ => ((R.family.path.rep N per j).eval W)⁻¹ • z)
  apply congrArg (fun F : Config G (R.family.side L per) → ℂ => gust R.family.path N per L F j below W)
  funext U
  have density := ActualOriginalQInput.density_full Q D u μ orders simple N live ready
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U
  change ((ActualOriginalQInput.input Q D u μ orders simple N live).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U =
    ((R.family.path.rep N per L).eval U : ℂ) • Poly.pass (q₀ x U) at density
  rw [density,map_smul]
  simp only [Complex.real_smul,smul_eq_mul]
  ring

end YM.Integration.WilsonMovingMentorCurvatureWord
end
