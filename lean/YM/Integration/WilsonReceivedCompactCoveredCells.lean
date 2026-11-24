import YM.Integration.WilsonReceivedGeometricCellReadout
import YM.Integration.WilsonReceivedCompactPriorIntegral

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompactCoveredCells
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
open MeasureTheory WilsonLimitConstruction OPE.Therm WilsonJointAxialRoster WilsonReportingForestAngularFare
open WilsonMeasuredCoefficientTransport ConnectedActivityE6.SliceRows
open Filter Finset MeasureTheory Lattice Wilson RG Source FVA1
open OPE OPE.Orbits OPE.Therm Climb Trace.Pilot PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Push.GridApprox
open scoped BigOperators Topology Classical

open FVA1 MeasureTheory OPE RG16.Literal RG Lattice Wilson Push Push.Local 
open AllOrder PhysicalNext Extra.Histories Source Labels Next.Foundations XSpace XSpace.Rose
open WilsonMeasuredCoefficientTransport WilsonReceivedGeometricCellReadout
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {i N per:ℕ} (live:i ≤ N)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "Ω" => Config G ((C).side i per)
variable {A:Type} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (test:Test 3) (χ:Points 3→A) (measured:Measurable χ)
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ

def Integrated (W:Rep G ((C).side i per)) (v:A→Values Ω) (prices:Fares) (y:A→Site ((C).side i per))
    (store:∀o:A,w o≠0 → Coefficient (F) ((C).side i per))
: Prop :=
    let stored:=fun o U=>if h:w o≠0 then (store o h).density (y o) (S₀) W U else 0
    let forced:=fun o U=>if h:w o≠0 then account (store o h) W U else 0
    (∀U,test.applyTo (fun x=>stored (χ x) U)=
      test.applyTo (fun x=>(v (χ x)).withdrawn U)-(W.eval U:ℂ)*test.applyTo (fun x=>(v (χ x)).filed U)) ∧
    let loss:=fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U)/(W.eval U:ℂ)-
      test.applyTo (fun x=>(v (χ x)).covered U)-test.applyTo (fun x=>forced (χ x) U)/(W.eval U:ℂ)
    RG.Envelope loss ∧ ∀j (age:j ≤ i),
      (∫U,‖actualTransport R.family (N:=N) loss age U‖ ∂scene R.family.path N per j) ≤
       (∫x:Points 3,‖test x‖)*|prices.earlier|

include live measured in
/-- At an occupied placement the stored coefficient and its compulsory term are read on the original vacuum.
    The same nominal and the same independent field are used in the compact signed hearing. -/
theorem original (W:Rep G ((C).side i per)) (v:A→Values Ω) (prices:Fares) (y:A→Site ((C).side i per))
    (store:∀o:A,w o≠0 → Coefficient (F) ((C).side i per))
    (bought:∀o h,Paid (N:=N) R W prices (y o) (v o) (store o h)) :
 Integrated (N:=N) R test χ W v prices y store := by
  let stored:=fun o U=>if h:w o≠0 then (store o h).density (y o) (S₀) W U else 0
  let forced:=fun o U=>if h:w o≠0 then account (store o h) W U else 0
  let Z:=fun (o:A) (U:Ω)=>(v o).withdrawn U/(W.eval U:ℂ)-(v o).covered U-forced o U/(W.eval U:ℂ)
  let loss:=fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U)/(W.eval U:ℂ)-
      test.applyTo (fun x=>(v (χ x)).covered U)-test.applyTo (fun x=>forced (χ x) U)/(W.eval U:ℂ)
  constructor
  · intro U
    change test.applyTo (fun x=>stored (χ x) U)=_
    rw [WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>stored o U),
      WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).withdrawn U),
      WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).filed U),
      Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    change w o * stored o U = w o * (v o).withdrawn U-(W.eval U:ℂ)*(w o*(v o).filed U)
    by_cases h:w o≠0
    · simp only [stored,dif_pos h,(bought o h).2.2.2.1 U]
      ring
    · simp [not_ne_iff.mp h]
  · have localError (o:A) (h:w o≠0): Z o=error R W (v o) (store o h):=by
      funext U
      simp only [Z,error,forced,dif_pos h]
    have envelope (o:A) (h:w o≠0):RG.Envelope (Z o):=by
      rw [localError o h]
      exact (bought o h).2.2.2.2.1
    have charge (o:A) (h:w o≠0):(∫U,‖Z o U‖ ∂scene R.family.path N per i) ≤ |prices.earlier|:=by
      rw [localError o h]
      apply le_trans _ (le_abs_self _)
      simpa only [actualTransport_base R.family R.makes live] using (bought o h).2.2.2.2.2 i le_rfl
    have same:(fun U=>test.applyTo (fun x=>Z (χ x) U))=loss:=by
      funext U
      dsimp only [loss]
      rw [WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>Z o U),
        WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).withdrawn U),
        WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).covered U),
        WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>forced o U)]
      simp only [Z,mul_sub,←mul_div_assoc,Finset.sum_sub_distrib,Finset.sum_div]
    change RG.Envelope loss ∧ ∀j (age:j ≤ i),
      (∫U,‖actualTransport R.family (N:=N) loss age U‖ ∂scene R.family.path N per j) ≤ (∫x:Points 3,‖test x‖)*|prices.earlier|
    rw [←same]
    exact WilsonReceivedCompactPriorIntegral.occupied R live test χ measured Z _ (abs_nonneg _) envelope charge
end YM.Integration.WilsonReceivedCompactCoveredCells
