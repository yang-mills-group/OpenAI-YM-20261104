import YM.Integration.WilsonThermometerUnitFilingRegistered
import YM.Integration.WilsonThermometerUnitFilingPaidBlend
import YM.Integration.WilsonCapturedPrimaryShiftedCylinder

/-! All eight filed terms use one admissible anchor in a cell. Translation of the joint physical integral identifies its original value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPaidSites
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato OPE OPE.Cards
open Bid RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof MergeProof.Accent FVA1 Marker
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingCylinder Primitives.GCC.Anchor
open WilsonThermometerUnitFilingReflectedShape (Key)
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) (z:UVIndex)
variable (r:ℝ) (φ:Test 3) (Q:Sites R z→Poly (Stock.census (Fin 3))) (axis:Sites R z→Option (Fin 3))
local notation "J!" => Stock.census (Fin 3)
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ
  (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
local notation "P!" => fun y:Sites R z=>WilsonCapturedPrimaryPhysicalArray.registered y (axis y)
local notation "Y!" => WilsonThermometerUnitFilingRegistered.submitted R A z r φ Q (P!)
local notation "c!" => WilsonThermometerUnitFilingReflectedShape.tariff R z r φ Q
local notation "F!" => WilsonThermometerUnitFilingRegistered.operand R A z (P!)

open private smooth from YM.Integration.WilsonThermometerUnitFilingRegistered
include simple in
theorem original (ready:∀v,R.family.ref (WilsonPositionThermometerGradedSource.grade v).val≤z.1) {u b j:ℕ} (ju:j≤u) (ub:u≤b) (bN:b≤z.1) (door:Opened R.family 0 u z.2)
    (cost:Key R z→ℝ)
    (returned:∀a,c! a≠0 → Booked R.family z.1 z.2 0 ((F!) a) u (ub.trans bN) ∧
      PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) (cost a)
        ((F!) a-report R ((F!) a) u • (1:Cut R.family z.1 z.2))) :
    Booked R.family z.1 z.2 0 (Y!) u (ub.trans bN) ∧
    PaidAt R.family.S z.1 z.2 j (R.family.beta z.1 z.2) (∑a,‖c! a‖*cost a)
      ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) ∧
    ‖tested R A z r φ Q-report R (Y!) u‖≤∑a,‖c! a‖*cost a:=by
  let T:=center R.family.S z.2 (ju.trans (ub.trans bN)) 0
  letI : Nonempty (Key R z) := ⟨(fun _=>0,⟨∅,Finset.mem_univ _⟩)⟩
  obtain ⟨bk,root⟩:=WilsonThermometerUnitFilingPaidBlend.original R simple (c!) (F!) ju ub bN door
    (smooth R A z (P!)) cost returned
  have change_field:=WilsonThermometerUnitFilingRegistered.expansion R A z r φ Q (P!)
  rw [←change_field] at root bk
  refine ⟨bk,root,?_⟩
  have bill:=(OPE.Strobe.atone T (R.family.beta z.1 z.2) (seamless R.makes z.1 z.2) root.ticket).trans root.mark
  change ‖R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2))‖ ≤ _ at bill
  have law : R.family.omega z.1 z.2 ((Y!)-report R (Y!) u • (1:Cut R.family z.1 z.2)) =
      R.family.omega z.1 z.2 (Y!) -report R (Y!) u :=by
    have nice:Continuous (Y!):=by
      rw [change_field,show (∑a,c! a • (F!) a)=_ from funext (fun U=>Finset.sum_apply U _ _)]
      exact continuous_finsetSum _ fun a _=>(smooth R A z (P!) a).const_smul _
    unfold Family.omega moment
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact nice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  rw [law] at bill
  rw [←WilsonThermometerUnitFilingCylinder.literal R A z r φ Q,
    WilsonCapturedPrimaryShiftedCylinder.original R A z ready r φ Q axis]
  exact bill

end YM.Integration.WilsonThermometerUnitFilingPaidSites
