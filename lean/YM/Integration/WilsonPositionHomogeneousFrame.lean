import YM.Integration.WilsonPositionHomogeneousNear
import YM.Integration.WilsonPositionPrescribedZero
import YM.Integration.WilsonPositionPrescribedNested

/-! The actual homogeneous field on the measured position thermometer,
on the very same completed original continuum hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousFrame
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionPrescribedScreen
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (Z : WilsonPrescription G)

abbrev reading : ℝ→ℝ := WilsonPositionThermometerReading.reading F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z.criterion
abbrev turn (d : ℕ) (r : ℝ) := WilsonPositionHomogeneousNear.field Z d (reading F J Z r)

/-- Same genuine Maxwell quotient, registered on its original physical dates. -/
def change (d : ℕ) (r : ℝ) : RG17.Free R.family d ≃ₗ[ℂ] RG17.Free R.family d :=
  if h:Bijective (stand (turn F J Z d r)) then
    (Maxwell.Free.fields R.family.labels d).trans ((LinearEquiv.ofBijective _ h).trans (Maxwell.Free.fields R.family.labels d).symm)
  else LinearEquiv.refl ..

def homogeneous (r : ℝ) : PhysMS.tower S := fun d=>
  (change F J Z d r).trans (WilsonPositionPrescribedFrame.positioned F J Z.store r d)

private theorem leg {d : ℕ} {r : ℝ} (h:Bijective (stand (turn F J Z d r))) (v:Sec G d) :
    change F J Z d r ((Maxwell.Free.fields R.family.labels d).symm v)=
    (Maxwell.Free.fields R.family.labels d).symm (stand (turn F J Z d r) v) := by
  rw [change,dif_pos h]
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply]

variable (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
include lead paid in
theorem fitted (hG : G.Simple) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail, Bijective (stand (turn F J Z d r)) :=
  (WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion).eventually
    (WilsonPositionHomogeneousNear.invertible Z d)

include lead paid in
theorem measured (hG:G.Simple) (d:ℕ) : ∀ᶠ r in Trace.Pilot.trail,
    hierarchy F (homogeneous F J Z) d r =
    recruit (stand (turn F J Z d r)) (hierarchy F (WilsonPositionPrescribedFrame.positioned F J Z.store) d r) := by
  filter_upwards [fitted F J Z lead paid hG d,RG17.positiveLength] with r fit hr
  ext n t v
  change hierarchy F (homogeneous F J Z) d r n t v =
      hierarchy F (WilsonPositionPrescribedFrame.positioned F J Z.store) d r n t (fun i=>stand (turn F J Z d r) (v i))
  rw [actual F _ _ _ _ _ hr,actual F _ _ _ _ _ hr]
  apply congrArg t.applyTo;funext x
  apply congrArg (S.classMoment (spectator F none) _ (r•x));funext i
  exact congrArg (WilsonPositionPrescribedFrame.positioned F J Z.store r d) (leg F J Z fit (v i))

include lead paid in
theorem adjacent (hG:G.Simple) (H:WilsonPositionHomogeneousCoefficients.Warrant Z) (d:ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,∀v,
      homogeneous F J Z r (d+1) ((Maxwell.Free.scheme R.family.labels).rise (Nat.le_succ d) v)=
      F.sector.derivatives.rise (Nat.le_succ d) (homogeneous F J Z r d v) := by
  filter_upwards [fitted F J Z lead paid hG d,fitted F J Z lead paid hG (d+1),
    WilsonPositionPrescribedNested.transported F J lead Z.store (WilsonPositionPrescribedFrame.positioned F J Z.store)
      (fun d r fit v => congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J Z.store fit v)) d] with r lo hi prior v
  obtain ⟨u,rfl⟩ := (Maxwell.Free.fields R.family.labels d).symm.surjective v
  change WilsonPositionPrescribedFrame.positioned F J Z.store r (d+1) (change F J Z (d+1) r _) =
    F.sector.derivatives.rise (Nat.le_succ d) (WilsonPositionPrescribedFrame.positioned F J Z.store r d (change F J Z d r _))
  rw [←WilsonPositionPrescribedNested.included,leg F J Z hi]
  have rel:=WilsonPositionHomogeneousNear.includes Z H (Nat.le_succ d) (reading F J Z r) u
  change stand (turn F J Z (d+1) r) (step d u)=step d (stand (turn F J Z d r) u) at rel
  rw [rel,WilsonPositionPrescribedNested.included,prior,leg F J Z lo]

end YM.Integration.WilsonPositionHomogeneousFrame

