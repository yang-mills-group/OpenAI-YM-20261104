import YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget

/-! Uniform finite-order cost of the genuine independent compact diagnostic on its full field basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotBudget
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
open WilsonPositionProgramTrialPublicJointPivotTarget (row regular)
open private test_linear from YM.Integration.WilsonPositionIndependentIntegral

def coefficient (s : ℝ) (p : Fields G 6) (k : ℕ) : ℂ :=
  (Rose.test Z.criterion).applyTo (fun x => coeff k (signed (fxt (response Z M ν s) x) p))

theorem paid (s : ℝ) (p : Fields G 6) (q : ℕ) (g : ℂ) :
    row Z M H ν s q g p = ∑ k ∈ range (q+1), g^k * coefficient Z M ν s p k := by
  let A (x : Points 3) := fxt (response Z M ν s) x
  let φ := Rose.test Z.criterion
  have a (S : Face) : Regular (fun x => whole (A x) (Rose.missing p S)) := by
    intro k
    simpa only [WilsonPositionProgramTrialPublicJointPivotSeries.whole,PowerSeries.coeff_mk]
      using regular Z M H ν s 3 k (Rose.missing p S)
  have all : Regular (fun x => signed (A x) p) :=
    regular_add (regular_sub (a univ) (regular_add (regular_add
      (regular_mul (a {0,1}) (a {2})) (regular_mul (a {0,2}) (a {1})))
      (regular_mul (a {1,2}) (a {0}))))
      (regular_smul (regular_mul (regular_mul (a {0}) (a {1})) (a {2})) 2)
  change φ.applyTo (fun x => cash q g (signed (A x) p)) = _
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.printed,
    WilsonPositionScaleLawThermometerSmeared.paper]
  simpa only [coefficient,A,φ,mul_comm] using test_linear φ (q+1)
    (fun k x => coeff k (signed (A x) p)) (fun k => g^k) all

def fee (s : ℝ) (q : ℕ) : ℝ :=
  ∑ b : Fin 3 → Pin G 6, ∑ k ∈ range (q+1),
    ‖coefficient Z M ν s (fun j => Module.finBasis ℝ (Sec G 6) (b j)) k‖

theorem original (s : ℝ) (q : ℕ) (g : ℂ) (hg : ‖g‖ ≤ 1) :
    ‖rows (row Z M H ν s q g)‖ ≤ fee Z M ν s q := by
  have nn (r : Fin 3 → Pin G 6) : 0 ≤ ∑ k ∈ range (q+1),
      ‖coefficient Z M ν s (fun j => Module.finBasis ℝ (Sec G 6) (r j)) k‖ :=
    sum_nonneg (fun _ _ => norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg (sum_nonneg (fun b _ => nn b))).2
  intro b
  let v (j : Fin 3) := Module.finBasis ℝ (Sec G 6) (b j)
  change ‖row Z M H ν s q g v‖ ≤ _
  rw [paid]
  calc
    ‖∑ k ∈ range (q+1), g^k * coefficient Z M ν s v k‖ ≤
        ∑ k ∈ range (q+1), ‖g^k * coefficient Z M ν s v k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (q+1), ‖coefficient Z M ν s v k‖ := by
      apply sum_le_sum
      intro k _
      rw [norm_mul,norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hg)
    _ ≤ fee Z M ν s q := single_le_sum (fun r _ => nn r) (mem_univ b)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotBudget
