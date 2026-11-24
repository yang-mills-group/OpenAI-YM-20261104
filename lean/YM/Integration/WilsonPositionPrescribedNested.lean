import YM.Integration.WilsonPositionPrescribedScreen
import YM.AllOrder.Leading.Solve

/-! The actual MS prescription on the positive physical hierarchy: the
same measured nonlinear branch commutes with the original Maxwell grade
inclusion. No different normalization tests are introduced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedNested
open Function Filter Set Finset MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize
open WilsonPositionPrescribedScreen
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ→PhysMS.tower S)

theorem included (d : ℕ) (v : Sec G d) :
    (Maxwell.Free.fields C.labels (d+1)).symm (step d v) =
       (Maxwell.Free.scheme C.labels).rise (Nat.le_succ d) ((Maxwell.Free.fields C.labels d).symm v) := by
  apply Maxwell.Free.address_inj C.labels (d+1)
  rw [Maxwell.Free.address_rise,Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply,
      Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply]
  rfl

theorem physical (lead : PhysMS.Leading F J) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,
       recruit (step d) (hierarchy F J (d+1) r)=hierarchy F J d r := by
  filter_upwards [lead.raised (Nat.le_succ d),RG17.positiveLength] with r agree hr
  ext n t v
  change hierarchy F J (d+1) r n t (fun i=>step d (v i))=hierarchy F J d r n t v
  rw [actual F J _ _ _ _ hr,actual F J _ _ _ _ hr]
  simp_rw [included]
  apply t.apply_eq
  intro x hx
  unfold PhysMS.measured
  simp_rw [agree]
  exact AllOrder.Leading.moment_inclusion F.room.kernel.laws.toSymmetric F.phase.transport.injection
    (fun _ : Fin n => Nat.le_succ d) (Work.A05.smul_conf hr hx)
    (fun i => J r d ((Maxwell.Free.fields C.labels d).symm (v i)))

private theorem commute {d : ℕ} (P : Prediction G (d+1)) (m : Change G (d+1)) :
    recruit (step d) (recruit (stand m) P)=recruit (stand (fell d m)) (recruit (step d) P) := by
  ext n t v
  simp only [recruits]
  apply congrArg (P n t);funext i
  exact stoop m (v i)

/-- Exact enrollment of the very same branch in adjacent horizons,
uniformly before all measured fields at those horizons. -/
theorem original (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,
      fell d (correction F J V (d+1) r)=correction F J V d r := by
  let hi := correction F J V (d+1)
  let lo := correction F J V d
  let T : MoveSpace G (d+1)→ₗ[ℝ] MoveSpace G d :=
    (guide G d).toLinearMap.comp ((fell d).comp (guide G (d+1)).symm.toLinearMap)
  have ht := (WilsonPositionPrescribedScreen.original F J lead V (d+1)).1
  have near : Tendsto (fun r=>guide G d (fell d (hi r))) Trace.Pilot.trail (𝓝 0) := by
    have bound : Tendsto (fun r=>T (guide G (d+1) (hi r))) Trace.Pilot.trail (𝓝 (T 0)) :=
      (T.toContinuousLinearMap.continuous.tendsto 0).comp ht
    rw [map_zero] at bound
    apply bound.congr
    intro r
    change guide G d (fell d ((guide G (d+1)).symm (guide G (d+1) (hi r))))=_
    rw [LinearEquiv.symm_apply_apply]
  have uc := WilsonPositionPrescribedScreen.unique F J lead V d (fun r=>fell d (hi r)) near
  filter_upwards [uc,physical F J lead d,(WilsonPositionPrescribedScreen.original F J lead V (d+1)).2]
    with r fit lower higher
  apply (fit.mp _).symm
  let PH := hierarchy F J (d+1) r
  have atHigh : (V.measure (d+1)).D (recruit (stand (hi r)) PH) =
      (V.measure (d+1)).D (reference G (d+1)) := higher.1
  change (V.measure d).D (recruit (stand (fell d (hi r))) (hierarchy F J d r)) =
       (V.measure d).D (reference G d)
  calc
    _ = (V.measure d).D (recruit (step d) (recruit (stand (hi r)) PH)) := by rw [commute,show recruit (step d) PH=_ from lower]
    _ = fell d ((V.measure (d+1)).D (recruit (stand (hi r)) PH)) := (V.respects d _).symm
    _ = fell d ((V.measure (d+1)).D (reference G (d+1))) := congrArg (fell d) atHigh
    _ = (V.measure d).D (reference G d) := by rw [V.respects d];rfl

theorem fields (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail,∀ v : Sec G d,
      stand (correction F J V (d+1) r) (step d v) =
        step d (stand (correction F J V d r) v) := by
  filter_upwards [original F J lead V d] with r nested v
  rw [stoop,nested]

/-- A physical realization of these very corrections inherits the original
adjacent-horizon inclusion on the same extraction. -/
theorem transported (lead : PhysMS.Leading F J) (V : Store G) (P : ℝ → PhysMS.tower S)
    (lift : ∀ d r, Bijective (stand (correction F J V d r)) → ∀ v : Sec G d,
      P r d ((Maxwell.Free.fields C.labels d).symm v) =
        J r d ((Maxwell.Free.fields C.labels d).symm (stand (correction F J V d r) v)))
    (d : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ v,
      P r (d+1) ((Maxwell.Free.scheme C.labels).rise (Nat.le_succ d) v) =
        F.sector.derivatives.rise (Nat.le_succ d) (P r d v) := by
  filter_upwards [(WilsonPositionPrescribedScreen.original F J lead V d).2,
    (WilsonPositionPrescribedScreen.original F J lead V (d+1)).2,
    fields F J lead V d, lead.raised (Nat.le_succ d)] with r lo hi aligns base v
  obtain ⟨u,rfl⟩ := (Maxwell.Free.fields C.labels d).symm.surjective v
  rw [← included, lift _ _ hi.2.1, aligns, included, base, lift _ _ lo.2.1]

end YM.Integration.WilsonPositionPrescribedNested
