import YM.Integration.WilsonCapturedPrimaryPhysicalArray
import YM.Integration.WilsonThermometerUnitFilingCylinder

/-! Simultaneous translation of the entire signed thermometer under the original
finite Wilson law. The independent inverse stays evaluated at the submitted cell. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryShiftedCylinder
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato
open Bid RG16 RG16.Literal Trace.Physical.GermGraph MergeProof MergeProof.Accent FVA1 Marker
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open private linear_mean smooth_sum smooth_face from YM.Integration.WilsonThermometerUnitFilingCylinder
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerGradedReading (vector row)
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (z:UVIndex)
local notation "mode" => Stock.census (Fin 3)
local notation "reg" y:max a:max => WilsonCapturedPrimaryPhysicalArray.registered y a

private theorem translated (ready:∀i,R.family.ref (grade i).val ≤ z.1) (s:Badge) (y:Sites R z)
    (t:Site (R.family.side z.1 z.2)) : row A z (fun i=>y i+t) s=row A z y s :=by
  let tokens (i:Fin 3) : R.family.book.Token :=
    ⟨(grade i).val,A.station.wheel.atCut z (index A (grade i)) (vector A s i)⟩
  exact R.family.anchored (p:=z.2) R.makes tokens ready t y

theorem face (ready:∀i,R.family.ref (grade i).val ≤ z.1) (s:Badge) (y:Sites R z) (a:Option (Fin 3)) :
    R.family.omega z.1 z.2 (placed R A z s y)=
      R.family.omega z.1 z.2 (placed R A z s (reg y a)) :=by
  change row A z y s=row A z (reg y a) s
  have position:(reg y a)=(fun i=>y i+ -(a.elim 0 y)) :=
    funext (fun i=>sub_eq_add_neg _ _)
  rw [position]
  exact (translated R A z ready s y _).symm

theorem entry (ready:∀i,R.family.ref (grade i).val ≤ z.1)
    (y:Sites R z) (a:Option (Fin 3)) (Q:Poly mode) :
    R.family.omega z.1 z.2 (source R A z y Q)=
      R.family.omega z.1 z.2 (source R A z (reg y a) Q) :=by
  unfold source
  rw [linear_mean R z _ _ (smooth_face R A z y),linear_mean R z _ _ (smooth_face R A z (reg y a))]
  exact sum_congr rfl (fun s _=>congrArg (wallet Q s*·) (face R A z ready s.val y a))

theorem original (ready:∀i,R.family.ref (grade i).val ≤ z.1) (r:ℝ) (φ:Test 3)
    (Q:Sites R z→Poly mode) (axis:Sites R z→Option (Fin 3)) :
    R.family.omega z.1 z.2 (WilsonThermometerUnitFilingCylinder.cylinder R A z r φ Q)=
    R.family.omega z.1 z.2 (∑y:Sites R z,WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z) y • source R A z (reg y (axis y)) (Q y)) :=by
  let w:=WilsonSeparatedOriginalThermometerCells.weight φ
    (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
  have lhs:=linear_mean R z w (fun y=>source R A z y (Q y))
    (fun y=>smooth_sum R z _ _ (smooth_face R A z y))
  have rhs:=linear_mean R z w (fun y=>source R A z (reg y (axis y)) (Q y))
    (fun y=>smooth_sum R z _ _ (smooth_face R A z (reg y (axis y))))
  exact lhs.trans ((sum_congr rfl (fun y _=>congrArg (w y*·) (entry R A z ready y (axis y) (Q y)))).trans rhs.symm)

end YM.Integration.WilsonCapturedPrimaryShiftedCylinder
