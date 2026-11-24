import YM.Integration.ActualRunQlocalTupleReaders
import YM.Integration.ActualRunKernelPackets

/-! The actual rooted tuple supplies the test fields of every original
curvature token. All Haar, regulator, threshold and monomial coefficients
remain literal. This supplies structural packet obligations only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalNativeTuple
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open RG05Readout RG05Readout.Native RG05Readout.Address
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {p L n : ℕ} {hn : n ≤ L}
  {V : Type} [DecidableEq V] (D : Datum R p L n hn V)

def packetLabels (i : V) (x : TestSpace (orbit D)) : R.family.label (grade D i) :=
  reader D i (x i) • label D i

def coefficientBudget (i : V)
    (j : (R.family.labels.level (grade D i)).Index) : ℝ :=
  (‖constant D i‖ *
    ((((R.family.S.toDepth hn p).count.val : ℝ)⁻¹) ^ depth (D.choice i).2.1 *
      (NativeCalibrationMoodReadout.coordinateCost (depth (D.choice i).2.1) *
        (orbit D i).height (ActualRunCalibrationTests.coordinates.symm
          (RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice i).1))))) *
    ‖label D i j‖

abbrev packetToken (N : ℕ) (s : ActualRunKernelPackets.Index R (grade D)) :=
  ActualRunKernelPackets.term R (orbit D) (grade D) N p L (root D)
    (packetLabels D) (coefficientBudget D) s

omit [DecidableEq V] in
/-- Every token reads only its original slot through the full original stub. -/
theorem token_reads (N : ℕ) (s : ActualRunKernelPackets.Index R (grade D))
    (j : Fin (ActualRunKernelPackets.tokenRank R (grade D) s) → G.ColorIndex) :
    Comparison.Density.Testing.Reads (readerRegion D) (packetToken D N s).plot
      {s.1} ((packetToken D N s).gem j) := by
  intro x y h
  have hr := coefficient_reads D s.1 s.2.1 (packetToken D N s).plot
    (by exact le_rfl) x y h
  let a : ℂ := NativeCurvatureTensor.coefficient (G := G)
    (fun k => (NativeCurvatureTensor.word s.2.2.val k).2) j
  let b : ℂ := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
    ActualRunKernelPackets.fieldRank R (grade D) s *
      ActualRunKernelPackets.weight R (grade D) N p L s
  change a * (b * labelCoefficient D s.1 s.2.1 x) =
    a * (b * labelCoefficient D s.1 s.2.1 y)
  exact congrArg (fun z : ℂ => a * (b * z)) hr

/-- Fixed tensor coefficients preserve the exact singleton complex letter. -/
theorem token_letter (N : ℕ) (s : ActualRunKernelPackets.Index R (grade D))
    (j : Fin (ActualRunKernelPackets.tokenRank R (grade D) s) → G.ColorIndex) :
    RG3.Held.Letter ℂ (fun i => (orbit D i).Mood) {s.1}
      ((packetToken D N s).gem j) := by
  let a : ℂ := NativeCurvatureTensor.coefficient (G := G)
    (fun k => (NativeCurvatureTensor.word s.2.2.val k).2) j
  let b : ℂ := (Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
    ActualRunKernelPackets.fieldRank R (grade D) s *
      ActualRunKernelPackets.weight R (grade D) N p L s
  change RG3.Held.Letter ℂ (fun i => (orbit D i).Mood) {s.1}
    (fun x => a * (b * labelCoefficient D s.1 s.2.1 x))
  exact ((coefficient_letter D s.1 s.2.1).cmul b).cmul a

omit [DecidableEq V] in
/-- The whole color-tensor sum is paid at each actual independent unit test. -/
theorem token_bound (N : ℕ) (s : ActualRunKernelPackets.Index R (grade D))
    (x : IndependentTests (orbit D)) :
    (∑ j, ‖(packetToken D N s).gem j (testInclusion (orbit D) x)‖) ≤
      (packetToken D N s).coin := by
  apply ActualRunKernelPackets.term_bound
  change ‖labelCoefficient D s.1 s.2.1 (testInclusion (orbit D) x)‖ ≤
    coefficientBudget D s.1 s.2.1
  exact coefficient_bound D s.1 s.2.1 x

end YM.Integration.ActualRunQlocalNativeTuple
end
