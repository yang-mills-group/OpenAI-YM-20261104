import YM.Integration.WilsonPositionProgramTrialPublicJointPivotLocated
import YM.Integration.WilsonPhysicalCommonSignedAperture

/-! The re-expression of a finite-order signed response in its own fitted section. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotFitted
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPhysicalRosePositionFace (located predicted)
open WilsonPositionProgramTrialPublicJointPivotRose (Live tested)
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
def undress {d n : ℕ} (T : Change G d) (ht : Bijective (stand T)) (A : Row G d n) : Row G d n :=
  A.compLinearMap (fun _ => (LinearEquiv.ofBijective (stand T) ht).symm.toLinearMap)
theorem named {d n : ℕ} (T : Change G d) (ht : Bijective (stand T)) (A : Row G d n) (v : Fin n → Sec G d) :
    undress T ht A (fun j => stand T (v j)) = A v := by
  apply congrArg A
  funext j
  exact (LinearEquiv.ofBijective (stand T) ht).symm_apply_apply _
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)

def debit {r : ℝ} (rp : 0 < r) (Q : Prediction G 6) (T : Change G 6)
    (A : Row G 6 3) (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q))) : ℝ :=
  let φ := Rose.test Z.criterion
  let model := offered (fun _:Fin 3=>()) (fun _:Unit=>T) (undress ((Z.store.survey 6).firstPass (Z.store.prepared 6) Q) hq A)
  let actual := tested φ (located F J r) (WilsonPositionProgramTrialPublicJointPivotLocated.live F J φ rp)
  let D := Z.store.survey 6
  ‖rows actual - rows model‖ +
    ‖docket D (fun _:Unit=>hierarchy F J 6 r) - docket D (retag (fun _:Unit=>T) (fun _:Unit=>Q))‖ *
      ‖rows model‖

theorem original {ι : Type*} (u : Filter ι) (age : ι → ℝ) (near : Tendsto age u trail)
    (lead : Leading F J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ι → Prediction G 6) (T : ι → Change G 6)
      (_ : (Z.store.survey 6).Via Q (u:=u)) (_ : Tendsto (fun i => guide G 6 (T i)) u (𝓝 0)),
      ∀ᶠ i in u, ∀ (rp : 0 < age i) (A : Row G 6 3) (hq : Bijective (stand ((Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i)))),
        |Rose.cT Z.criterion.cut G Z.criterion.image * WilsonPositionHomogeneousFrame.reading F J Z (age i) -
          (A (Rose.tag G)).re| ≤ C * debit F J Z rp (Q i) (T i) A hq := by
  obtain ⟨C,cp,paid⟩ := WilsonPhysicalCommonSignedAperture.original (Z.store.survey 6)
    (Z.store.prepared 6) (fun _:Fin 3=>()) (Rose.tag G) u
  refine ⟨C,cp,fun Q T warm oriented => ?_⟩
  have stored := paid (fun (i:ι) (_:Unit) => hierarchy F J 6 (age i))
    (fun (i:ι) (_:Unit) => Q i) (fun (i:ι) (_:Unit) => T i)
    (fun _ => (WilsonPositionPrescribedScreen.warm F J lead Z.store 6).comp near)
    (fun _ => warm) (fun _ => oriented)
  filter_upwards [stored,near.eventually (WilsonPositionPrescribedScreen.original F J lead Z.store 6).2]
    with i bound sure rp A hq
  let φ := Rose.test Z.criterion
  let tq := (Z.store.survey 6).firstPass (Z.store.prepared 6) (Q i)
  have income := bound (tested φ (located F J (age i)) (WilsonPositionProgramTrialPublicJointPivotLocated.live F J φ rp))
    (undress tq hq A)
  rw [WilsonPositionProgramTrialPublicJointPivotLocated.original F J Z.store Z.criterion rp sure.2.1] at income
  have fitted : WilsonPhysicalNormalizedSignedMenu.positioned (Z.store.survey 6) (Z.store.prepared 6)
      (fun _:Fin 3=>()) (Rose.tag G) (fun _:Unit=>Q i) (undress tq hq A) = A (Rose.tag G) :=
    named tq hq A (Rose.tag G)
  rw [fitted] at income
  rw [WilsonPositionHomogeneousFrame.reading,WilsonPositionThermometerReading.calibrated_denominator,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans income

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotFitted
