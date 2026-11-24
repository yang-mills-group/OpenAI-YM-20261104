import YM.Integration.WilsonPositionProgramTrialPublicJointPivotEvidence

/-! Finite coefficients for each independent connected test and every allowed grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotCompact
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS PowerSeries
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPositionProgramTrialPublicJointPivotRose (Fields Face)
open WilsonPositionProgramTrialPublicJointPivotSeries (whole signed cash cooked)
open private Regular regular_add regular_sub regular_mul regular_smul from YM.Integration.WilsonPositionIndependentIntegral
open scoped Classical Topology BigOperators Polynomial
variable {G : Gauge} {d : ℕ}

open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionProgramTrialPublicJointPivotEvidence (independent regular)
open private test_linear from YM.Integration.WilsonPositionIndependentIntegral

def coefficient (φ : Test 3) (p : Fields G d) (k : ℕ) : ℂ :=
  φ.applyTo (fun x => coeff k (signed (fxt (Measure.start Z.scheme Z.criterion d) x) p))

theorem paid (φ : Test 3) (p : Fields G d) (q : ℕ) (g : ℂ) :
    independent Z M H ν d φ q g p = ∑ k ∈ range (q+1), g^k * coefficient Z φ p k := by
  let A (x : Points 3) := fxt (Measure.start Z.scheme Z.criterion d) x
  have a (S : Face) : Regular (fun x => whole (A x) (Rose.missing p S)) := by
    intro k
    simpa only [WilsonPositionProgramTrialPublicJointPivotSeries.whole,PowerSeries.coeff_mk]
      using regular Z M H ν d 3 k (Rose.missing p S)
  have all : Regular (fun x => signed (A x) p) :=
    regular_add (regular_sub (a univ) (regular_add (regular_add
      (regular_mul (a {0,1}) (a {2})) (regular_mul (a {0,2}) (a {1})))
      (regular_mul (a {1,2}) (a {0}))))
      (regular_smul (regular_mul (regular_mul (a {0}) (a {1})) (a {2})) 2)
  change φ.applyTo (fun x => cash q g (signed (A x) p)) = _
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.printed,
    WilsonPositionScaleLawThermometerSmeared.paper]
  simpa only [coefficient,A,mul_comm] using test_linear φ (q+1)
    (fun k x => coeff k (signed (A x) p)) (fun k => g^k) all

def fee (d : ℕ) (φ : Test 3) (q : ℕ) : ℝ :=
  ∑ b : Fin 3 → Pin G d, ∑ k ∈ range (q+1),
    ‖coefficient Z φ (fun j => Module.finBasis ℝ (Sec G d) (b j)) k‖

theorem original (d : ℕ) (φ : Test 3) (q : ℕ) (g : ℂ) (hg : ‖g‖ ≤ 1) :
    ‖rows (independent Z M H ν d φ q g)‖ ≤ fee Z d φ q := by
  have nn (r : Fin 3 → Pin G d) : 0 ≤ ∑ k ∈ range (q+1),
      ‖coefficient Z φ (fun j => Module.finBasis ℝ (Sec G d) (r j)) k‖ :=
    sum_nonneg (fun _ _ => norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (sum_nonneg (fun b _ => nn b))).2
  intro b
  let v (j : Fin 3) := Module.finBasis ℝ (Sec G d) (b j)
  change ‖independent Z M H ν d φ q g v‖ ≤ _
  rw [paid]
  calc
    ‖∑ k ∈ range (q+1), g^k * coefficient Z φ v k‖ ≤
        ∑ k ∈ range (q+1), ‖g^k * coefficient Z φ v k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (q+1), ‖coefficient Z φ v k‖ := by
      apply sum_le_sum
      intro k _
      rw [norm_mul,norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hg)
    _ ≤ fee Z d φ q := single_le_sum (fun r _ => nn r) (mem_univ b)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotCompact
