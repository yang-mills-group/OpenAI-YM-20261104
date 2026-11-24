import YM.Integration.WilsonMovingMentorConcourse
import YM.Integration.WilsonOriginalProjectedCurvatureEnrollment
import YM.Integration.WilsonCoherentEarlier

/-! The complete registered signed source is evaluated in the physical
representative on its own history and transported to one earlier held field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorMarkedPicture
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open AllOrder AllOrder.Floe AllOrder.Transit.WheelP
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m N per k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
variable {H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per)}
    (course : Concourse R.alloy R.kit R.T π Γ m N per k H)

include course in
theorem kernel {i : ℕ} (past : m ≤ i) (live : i < N)
    (V : Config G (R.family.side i per)) (U : Config G (R.family.side (i+1) per)) :
    actualConditionalDensity R.family N per i V U =
      (R.family.path.levels.clock.op i per).density (H (i+1)).beta U V *
        (H (i+1)).eval U / (H i).eval V := by
  have upper := course.1.walk (i+1) (by omega) (by omega)
  have lower := course.1.walk i past live.le
  rw [upper.beta,upper.view,lower.view]
  rfl

include course in
theorem original {L n j : ℕ} (within : m≤j) (below : j≤L) (live : L≤N)
    {hn : n≤L} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R per L n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (σ : ℝ) (extra : V → ℕ) (x : tastes D)
    (read : Poly (Stock.census V) → ℂ) (exterior : Config G (R.family.side L per) → ℂ)
    (W : Config G (R.family.side j per)) :
    actualTransport R.family (N:=N) (fun U => exterior U * read
      (WilsonOriginalProjectedCurvatureEnrollment.filed Q D u μ orders N σ extra
        (Pert.Asymptotics.regulatorRun R.family N per L) x U)) below W =
    ((H j).eval W)⁻¹ • gust R.family.path N per L
      (fun U => (H L).eval U • (exterior U * read
        (Mach (Stock.census V) (fun i =>
          ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
            ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
              (R.family.side L per) (ActualRunQlocalNativeTuple.root D i) U (orders i))))) j below W := by
  have lower := (course.1.walk j within (below.trans live)).view
  have upper := (course.1.walk L (within.trans below) live).view
  rw [upper,lower]
  simp only [actualTransport, fun U => WilsonOriginalProjectedCurvatureEnrollment.original Q D u μ orders N σ extra x U live]
  rfl

end YM.Integration.WilsonMovingMentorMarkedPicture
end
