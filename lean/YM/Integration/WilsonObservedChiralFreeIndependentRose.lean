import YM.Integration.WilsonPositionProgramTrialPublicJointPivotEvidence
import YM.Integration.WilsonObservedChiralFreeRoseTangent

/-! The entire constant independent position row as a tested Maxwell connected form. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonObservedChiralFreeIndependentRose
open Function Set Finset PowerSeries Spec Table Extraction PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionProgramTrialPublicJointPivotEvidence (independent)
open WilsonPositionProgramTrialPublicJointPivotSeries (cash whole signed)
open WilsonMaxwellThermometerFaces (connected faces)
open scoped Classical Topology BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){simple:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z simple M σ b)(ν:ℝ)

include H ν in
theorem scene_zero {x:Points 3}(hx:x∈conf 3):
    Jury.fxt (Measure.start Z.scheme Z.criterion 6) x 0=scene x 6 := by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  change Jury.fxt _ (⟨x,hx⟩:Stage 3).val 0=_
  rw [Jury.exactC]
  exact (Measure.dawn Z.scheme Z.criterion ν M σ simple data.Taylor data.still data.base) 3 ⟨x,hx⟩

theorem original (φ:Test 3)(p:Fin 3→Sec G 6):
    independent Z M H ν 6 φ 0 0 p=φ.applyTo (fun x=>connected x p) := by
  rw [WilsonPositionProgramTrialPublicJointPivotEvidence.original]
  apply Test.apply_eq
  intro x hx
  let A:=Jury.fxt (Measure.start Z.scheme Z.criterion 6) x
  have step : A 0=scene x 6 := scene_zero Z M H ν hx
  have mode (a:Badge):constantCoeff (whole A (missing p a))=faces x p a := by
    rw [←coeff_zero_eq_constantCoeff_apply,whole,coeff_mk,step]
    rfl
  have zero (P:PowerSeries ℂ):cash 0 0 P=constantCoeff P := by
    simp [cash,coeff_zero_eq_constantCoeff_apply]
  change (trunc (0+1) (signed A p)).eval 0=connected x p
  rw [←WilsonPositionProgramTrialPublicJointPivotSeries.printed 0 0 (signed A p),zero]
  simp only [signed,connected,b3,two_smul,map_sub,map_add,map_mul,constantCoeff_C,mode]

theorem lower (p q:Sec G 4):
    independent Z M H ν 6 (Rose.test Z.criterion) 0 0
      (Graph3.trip (Rose.toll G) (up (by decide:4≤6) p) (up (by decide:4≤6) q))=0 :=
  (original Z M H ν _ _).trans (WilsonObservedChiralFreeRoseTangent.lower_pair Z.criterion simple p q)

end YM.Integration.WilsonObservedChiralFreeIndependentRose
