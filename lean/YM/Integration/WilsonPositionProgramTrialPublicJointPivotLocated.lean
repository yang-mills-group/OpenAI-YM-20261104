import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRose

/-! The integrated original physical position response, including all seven proper or full faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotLocated
open Filter Function Finset Set MeasureTheory Lattice RG PhysicalNext.Repeat.Legato
open RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress FVA2 FVA2.Register Trace.Target
open Spec Table Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize PhysMS
open WilsonPhysicalNormalizedSignedMenu (Row offered)
open WilsonPositionProgramTrialPublicJointPivotRose (Fields Face Live connected faces)
open WilsonPhysicalRosePositionFace (located predicted)
open scoped Classical Topology BigOperators
variable {G : Gauge} {d : ℕ} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S)

theorem declared (s : Face) (p : Fields G d) (T : Fin 3 → Change G d) :
    Rose.missing (fun i => stand (T i) (p i)) s =
      fun i => stand (T i) (Rose.missing p s i) := by
  funext i
  by_cases hi : i ∈ s <;> simp [Rose.missing,hi,solitary]

theorem realized (φ : Test 3) (M : Points 3 → Row G d 3) (hm : Live φ M)
    (p : Fields G d) (T : Fin 3 → Change G d) :
    WilsonPositionProgramTrialPublicJointPivotRose.tested φ M hm (fun i => stand (T i) (p i)) =
      φ.applyTo (fun x => WilsonPositionThermometerConnected.value
        (fun s => M x (fun i => stand (T i) (Rose.missing p s i)))) := by
  rw [WilsonPositionProgramTrialPublicJointPivotRose.original]
  simp_rw [declared]

theorem model (V : Store G) (φ : Test 3) (M : Points 3 → Row G 6 3)
    (hm : Live φ M) (Q : Prediction G 6) :
    WilsonPhysicalNormalizedSignedMenu.positioned (V.survey 6) (V.prepared 6)
      (fun _:Fin 3=>()) (Rose.tag G) (fun _:Unit=>Q)
      (WilsonPositionProgramTrialPublicJointPivotRose.tested φ M hm) =
      φ.applyTo (fun x => WilsonPositionThermometerConnected.value (predicted V Q (M x))) :=
  realized φ M hm (Rose.tag G) (fun _ => (V.survey 6).firstPass (V.prepared 6) Q)

theorem live (φ : Test 3) {r : ℝ} (hr : 0 < r) : Live φ (located F J r) := by
  intro p
  apply φ.smearing
  apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  let v (i : Fin 3) : S.Tag :=
    ⟨6,J r 6 ((Maxwell.Free.fields R.family.labels 6).symm (Rose.missing p s i))⟩
  exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr hx)

theorem original (V : Store G) (K : Rose.Pick V) {r : ℝ} (rp : 0 < r)
    (frame : Bijective (stand (WilsonPositionPrescribedScreen.correction F J V 6 r))) :
    WilsonPhysicalNormalizedSignedMenu.positioned (V.survey 6) (V.prepared 6)
      (fun _:Fin 3=>()) (Rose.tag G) (fun _:Unit=>WilsonPositionPrescribedScreen.hierarchy F J 6 r)
      (WilsonPositionProgramTrialPublicJointPivotRose.tested (Rose.test K) (located F J r)
        (live F J (Rose.test K) rp)) =
      WilsonPositionThermometerReading.tested F (WilsonPositionPrescribedFrame.positioned F J V) K r := by
  rw [model]
  unfold WilsonPositionThermometerReading.tested
  apply congrArg (Rose.test K).applyTo
  funext x
  apply congrArg WilsonPositionThermometerConnected.value
  funext s
  exact WilsonPhysicalRosePositionFace.actual F J V frame x s

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotLocated
