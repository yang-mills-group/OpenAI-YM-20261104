import YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredRows
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

open scoped ContDiff
theorem coefficients (A : Points 3 → ℕ → Row G d 3) (h : ∀ k p, ContinuousOn (fun x=>A x k p) (conf 3)) (p : Fields G d) :
    Regular (fun x=>signed (A x) p) := by
  have a (s : Face) : Regular (fun x => whole (A x) (Rose.missing p s)) := by
    intro k
    simpa only [WilsonPositionProgramTrialPublicJointPivotSeries.whole,PowerSeries.coeff_mk] using h k (Rose.missing p s)
  exact
    regular_add (regular_sub (a univ) (regular_add (regular_add
      (regular_mul (a {0,1}) (a {2})) (regular_mul (a {0,2}) (a {1})))
      (regular_mul (a {1,2}) (a {0}))))
      (regular_smul (regular_mul (regular_mul (a {0}) (a {1})) (a {2})) 2)

def leaf (φ : Test 3) (A : Points 3 → ℕ → Row G d 3) (p : Fields G d) (k : ℕ) : ℂ :=
  φ.applyTo (fun x=>(coeff k) (signed (A x) p))
theorem expansion (φ : Test 3) (A : Points 3 → ℕ → Row G d 3) (h : ∀ k p, ContinuousOn (fun x=>A x k p) (conf 3)) (p : Fields G d) (q : ℕ) (u : ℂ) :
    φ.applyTo (fun x=>cooked (A x) q u p) = ∑k∈range (q+1), leaf φ A p k*u^k := by
  change φ.applyTo (fun x=>cash q u (signed (A x) p))=_
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.printed,WilsonPositionScaleLawThermometerSmeared.paper]
  unfold Test.applyTo leaf
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [integral_finsetSum _ (fun k _=>(φ.smearing (coefficients A h p k)).mul_const (u^k))]
  simp_rw [integral_mul_const]
  rfl
variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

theorem thermal (s : ℝ) (q : ℕ) (p : Fields G 6) :
    ContDiff ℝ ω (fun u:ℝ=>WilsonPositionProgramTrialPublicJointPivotTarget.row Z M H ν s q (u:ℂ) p) := by
  let A : Points 3 → ℕ → Row G 6 3 := fun x=>fxt (response Z M ν s) x
  have h:=fun k v=>WilsonPositionProgramTrialPublicJointPivotTarget.regular Z M H ν s 3 k v
  change ContDiff ℝ ω (fun u:ℝ=>(Rose.test Z.criterion).applyTo (fun x=>cooked (A x) q (u:ℂ) p))
  simp_rw [expansion (Rose.test Z.criterion) A h p q]
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.pow k)
end YM.Integration.WilsonPositionScaleLawMeasuredRows
