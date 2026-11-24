import YM.Integration.WilsonPositionProgramTrialPublicJointPivotOrdered

/-! The original and independently prescribed signed joint test on every public grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotEvidence
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
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open FVA2.Scale.Jury (Thin fxt)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial


open WilsonPhysicalNormalizedSignedMenu (positioned)
open WilsonPositionProgramTrialPublicJointPivotSeries (cooked signed cash)
open WilsonPositionProgramTrialPublicJointPivotTarget (contracts smooth)
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)
variable {d : ℕ}
def atHome (d : ℕ) (r : ℝ) (x : Points 3) : Row G d 3 :=
  WilsonPhysicalPositionedHomeRows.pins F J (fun _=>r) (r • x)
theorem live (φ : Test 3) {r : ℝ} (hr : 0 < r) : Live φ (atHome F J d r) := by
  intro p
  apply φ.smearing
  apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  let v (i : Fin 3) : S.Tag :=
    ⟨d,J r d ((Maxwell.Free.fields R.family.labels d).symm (Rose.missing p s i))⟩
  exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr hx)

def old (d : ℕ) (φ : Test 3) {r : ℝ} (rp : 0<r) : Row G d 3 :=
  tested φ (atHome F J d r) (live F J φ rp)

theorem actual (φ : Test 3) {r : ℝ} (rp : 0<r) (p : Fin 3 → Sec G d)
    (frame : Bijective (stand (WilsonPositionPrescribedScreen.correction F J Z.store d r))) :
    positioned (Z.store.survey d) (Z.store.prepared d) (fun _:Fin 3=>()) p
      (fun _:Unit=>hierarchy F J d r) (old F J d φ rp) =
      old F (WilsonPositionPrescribedFrame.positioned F J Z.store) d φ rp p := by
  rw [show positioned (Z.store.survey d) (Z.store.prepared d) (fun _:Fin 3=>()) p
      (fun _:Unit=>hierarchy F J d r) (old F J d φ rp) =
      φ.applyTo (fun x => WilsonPositionThermometerConnected.value (fun s =>
        atHome F J d r x (fun i=>stand (WilsonPositionPrescribedScreen.correction F J Z.store d r)
          (Rose.missing p s i)))) from
    WilsonPositionProgramTrialPublicJointPivotLocated.realized φ (atHome F J d r) (live F J φ rp) p _]
  change φ.applyTo _ = φ.applyTo _
  apply congrArg φ.applyTo
  funext x
  apply congrArg WilsonPositionThermometerConnected.value
  funext s
  change S.classMoment (spectator F none) _ (r • x) _ = S.classMoment (spectator F none) _ (r • x) _
  apply congrArg
  funext i
  exact congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J Z.store frame (Rose.missing p s i)).symm

include H ν in
theorem regular (d : ℕ) : Thin (Measure.start Z.scheme Z.criterion d) := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact (Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=d)).light

def independent (d : ℕ) (φ : Test 3) (q : ℕ) (g : ℂ) : Row G d 3 :=
  contracts φ (fun x => cooked (fxt (Measure.start Z.scheme Z.criterion d) x) q g)
    (fun p => φ.smearing (smooth _ (fun k v => regular Z M H ν d 3 k v) p q g))

theorem original (φ : Test 3) (q : ℕ) (g : ℂ) (p : Fin 3 → Sec G d) :
    independent Z M H ν d φ q g p =
      φ.applyTo (fun x => (trunc (q+1)
        (signed (fxt (Measure.start Z.scheme Z.criterion d) x) p)).eval g) := by
  change φ.applyTo (fun x=>cash q g _) = φ.applyTo _
  simp_rw [WilsonPositionProgramTrialPublicJointPivotSeries.printed]

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotEvidence
