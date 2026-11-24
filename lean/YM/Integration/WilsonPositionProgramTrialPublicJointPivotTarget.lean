import YM.Integration.WilsonPositionProgramTrialPublicJointPivotSeries
import YM.Integration.WilsonPositionIndependentIntegral
import YM.Integration.WilsonPositionScaleLawThermometerSmeared

/-! The prescribed thermal polynomial on the entire finite determining and diagnostic field stock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget
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

def contracts (φ : Test 3) (M : Points 3 → Row G d 3)
    (h : ∀ p, Integrable (fun x => φ x * M x p)) : Row G d 3 :=
  MultilinearMap.mk' (fun p => φ.applyTo fun x => M x p)
    (fun p i a b => by
      simp_rw [Test.applyTo,MultilinearMap.map_update_add,mul_add]
      exact integral_add (h _) (h _))
    (fun p i z a => by
      unfold Test.applyTo
      simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,mul_left_comm (φ _) z]
      exact integral_const_mul z _)

theorem smooth (A : Points 3 → ℕ → Row G d 3)
    (h : ∀ k p, ContinuousOn (fun x => A x k p) (conf 3)) (p : Fields G d) (q : ℕ) (g : ℂ) :
    ContinuousOn (fun x => cooked (A x) q g p) (conf 3) := by
  have a (s : Face) : Regular (fun x => whole (A x) (Rose.missing p s)) := by
    intro k
    simpa only [WilsonPositionProgramTrialPublicJointPivotSeries.whole,PowerSeries.coeff_mk] using h k (Rose.missing p s)
  have all : Regular (fun x => signed (A x) p) :=
    regular_add (regular_sub (a univ) (regular_add (regular_add
      (regular_mul (a {0,1}) (a {2})) (regular_mul (a {0,2}) (a {1})))
      (regular_mul (a {1,2}) (a {0}))))
      (regular_smul (regular_mul (regular_mul (a {0}) (a {1})) (a {2})) 2)
  change ContinuousOn (fun x => cash q g (signed (A x) p)) (conf 3)
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.printed,
    WilsonPositionScaleLawThermometerSmeared.paper]
  exact continuousOn_finsetSum _ (fun k _ => (all k).mul_const _)
variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

include H in
theorem regular (s : ℝ) : Thin (response Z M ν s) := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base := Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=6)
  exact (base.glance (ψ Z M ν s)).light

def row (s : ℝ) (q : ℕ) (g : ℂ) : Row G 6 3 :=
  contracts (Rose.test Z.criterion) (fun x => cooked (fxt (response Z M ν s) x) q g)
    (fun p => (Rose.test Z.criterion).smearing
      (smooth _ (fun k v => regular Z M H ν s 3 k v) p q g))

theorem original (s : ℝ) (q : ℕ) (g : ℂ) :
    row Z M H ν s q g (Rose.tag G) =
      (Rose.cT Z.criterion.cut G Z.criterion.image:ℂ)*(trunc (q+1) (ψ Z M ν s)).eval g := by
  change (Rose.test Z.criterion).applyTo (fun x => cooked (fxt (response Z M ν s) x) q g (Rose.tag G)) = _
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.original]
  exact WilsonPositionScaleLawThermometerSmeared.original Z M H ν s q g

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotTarget
