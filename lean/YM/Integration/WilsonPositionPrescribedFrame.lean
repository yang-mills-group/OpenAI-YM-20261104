import YM.Integration.WilsonPositionPrescribedNested

/-! One true field tower normalized by the very input Store of the independent
MS prescription. Only the invertible near-free branch enters at late radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedFrame
open Function Filter Set Finset MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS Maxwell Maxwell.Free
open Trace.Pilot XSpace XSpace.Normalize WilsonPositionPrescribedScreen
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ→PhysMS.tower S) (V : Store G)

def change (d : ℕ) (r : ℝ) : RG17.Free C d ≃ₗ[ℂ] RG17.Free C d :=
  if h : Bijective (stand (correction F J V d r)) then
    (Maxwell.Free.fields C.labels d).trans
      ((LinearEquiv.ofBijective _ h).trans (Maxwell.Free.fields C.labels d).symm)
  else LinearEquiv.refl ..

def positioned (r : ℝ) : PhysMS.tower S := fun d=>(change F J V d r).trans (J r d)

theorem leg {d : ℕ} {r : ℝ} (h : Bijective (stand (correction F J V d r))) (v : Sec G d) :
    change F J V d r ((Maxwell.Free.fields C.labels d).symm v) =
      (Maxwell.Free.fields C.labels d).symm (stand (correction F J V d r) v) := by
  rw [change,dif_pos h]
  simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply]

theorem measured (lead : PhysMS.Leading F J) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,
      hierarchy F (positioned F J V) d r = recruit (stand (correction F J V d r)) (hierarchy F J d r) := by
  filter_upwards [(WilsonPositionPrescribedScreen.original F J lead V d).2,RG17.positiveLength] with r good hr
  ext n t v
  change hierarchy F (positioned F J V) d r n t v =
      hierarchy F J d r n t (fun i=>stand (correction F J V d r) (v i))
  rw [actual F _ _ _ _ _ hr,actual F J _ _ _ _ hr]
  apply congrArg t.applyTo;funext x
  change S.classMoment (spectator F none) _ (r•x) _=S.classMoment (spectator F none) _ (r•x) _
  apply congrArg (S.classMoment (spectator F none) _ (r•x));funext i
  exact congrArg (J r d) (leg F J V good.2.1 (v i))

theorem original (lead : PhysMS.Leading F J) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,
      (V.measure d).D (hierarchy F (positioned F J V) d r)=(V.measure d).D (reference G d) := by
  filter_upwards [measured F J V lead d,(WilsonPositionPrescribedScreen.original F J lead V d).2]
    with r equality earned
  rw [equality]
  exact earned.1

theorem adjacent (lead : PhysMS.Leading F J) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,∀ v,
      positioned F J V r (d+1) ((Maxwell.Free.scheme C.labels).rise (Nat.le_succ d) v) =
        F.sector.derivatives.rise (Nat.le_succ d) (positioned F J V r d v) :=
  WilsonPositionPrescribedNested.transported F J lead V (positioned F J V)
    (fun d r h v => congrArg (J r d) (leg F J V h v)) d

end YM.Integration.WilsonPositionPrescribedFrame
