import YM.Integration.WilsonOrdinaryPositionPoll
import YM.Integration.WilsonPositionThermometerAtRefAssay

/-! Solve the independent prescription's own nested position equations
on genuine interacting Yang--Mills correlations. Its original Store
and finite real test menu are fixed before physical radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedScreen
open Function Filter Set Finset MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ→PhysMS.tower S)

def point (r : ℝ) (d n : ℕ) (x : Points n) :
    MultilinearMap ℂ (fun _ : Fin n=> Sec G d) ℂ :=
  (S.classMoment (spectator F none) (fun _ : Fin n=>d) (r•x)).compLinearMap
    (fun _ => (J r d).toLinearMap.comp (Maxwell.Free.fields C.labels d).symm.toLinearMap)

theorem smooth {d n : ℕ} (v : Fin n→Sec G d) {r : ℝ} (hr : 0<r) :
    ContinuousOn (fun x=>point F J r d n x v) (conf n) :=
  WilsonOrdinaryPositionPoll.regular F J (fun i=>(Maxwell.Free.fields C.labels d).symm (v i)) hr

def report {r : ℝ} (hr : 0<r) (d : ℕ) {n : ℕ} (t : Test n) :
    MultilinearMap ℂ (fun _ : Fin n => Sec G d) ℂ := by
  refine MultilinearMap.mk' (fun v=> t.applyTo (fun x=>point F J r d n x v)) ?_ ?_
  · intro v i a b
    unfold Test.applyTo
    simp_rw [MultilinearMap.map_update_add,mul_add]
    exact integral_add (t.smearing (smooth F J _ hr)) (t.smearing (smooth F J _ hr))
  intro v i a b
  unfold Test.applyTo
  simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,fun x=>mul_left_comm (t x) a,integral_const_mul]

def positive {r : ℝ} (hr : 0<r) (d : ℕ) : Prediction G d := fun n => {
  toFun t := report F J hr d t
  map_add' t u := by
    apply MultilinearMap.ext;intro v
    change (t+u).applyTo _= t.applyTo _+u.applyTo _
    unfold Test.applyTo
    simp_rw [add_apply,add_mul]
    exact integral_add (t.smearing (smooth F J v hr)) (u.smearing (smooth F J v hr))
  map_smul' a t := by
    apply MultilinearMap.ext;intro v
    change (a•t).applyTo _=a*t.applyTo _
    unfold Test.applyTo
    simp_rw [smul_apply,smul_eq_mul,mul_assoc,integral_const_mul] }

def hierarchy (d : ℕ) (r : ℝ) : Prediction G d :=
  if hr : 0<r then positive F J hr d else reference G d

theorem actual (d n : ℕ) (t : Test n) (v : Fin n→Sec G d) {r : ℝ} (hr : 0<r) :
    hierarchy F J d r n t v =
      t.applyTo (fun x=> PhysMS.measured F none (J r) (d:=fun _=>d)
        (fun j => (Maxwell.Free.fields C.labels d).symm (v j)) r x) := by
  rw [hierarchy,dif_pos hr]
  rfl

theorem zero (d n : ℕ) (v : Fin n→Sec G d) (x : Points n) :
    PhysMS.WickGoal (C:=C) (d:=fun _ : Fin n=>d)
      (fun j=>(Maxwell.Free.fields C.labels d).symm (v j)) x = XSpace.Normalize.scene x d v := by
  let a (i : Fin n) : (Bel C.book).Tag := ⟨d,(Maxwell.Free.fields C.labels d).symm (v i)⟩
  change (Bel C.book).useAt (Bel C.book) x a = _
  rw [Maxwell.Free.display]
  have columns : Maxwell.Free.supply C.labels ∘ a = fun i => (v i).val := by
    funext i;change Maxwell.Free.address C.labels d ((Maxwell.Free.fields C.labels d).symm (v i))=_
    rw [Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply]
  rw [columns]
  rfl

theorem warm (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ) :
    (V.survey d).Via (hierarchy F J d) (u:=Trace.Pilot.trail) := by
  apply tendsto_pi_nhds.mpr;intro i
  apply tendsto_pi_nhds.mpr;intro k
  let w := (V.survey d).scope i
  let v (j : Fin w.n) : Sec G d := Module.finBasis ℝ (Sec G d) (k j)
  let a (j : Fin w.n) := (Maxwell.Free.fields C.labels d).symm (v j)
  have bank := WilsonOrdinaryPositionPoll.tends F J lead w.t a
  have idfree : w.t.applyTo (PhysMS.WickGoal (C:=C) (d:=fun _=>d) a) = reference G d w.n w.t v := by
    change w.t.applyTo _=w.t.applyTo _
    congr 1;funext x;exact zero d w.n v x
  rw [idfree] at bank
  apply bank.congr'
  filter_upwards [RG17.positiveLength] with r hr
  exact (actual F J d w.n w.t v hr).symm

def correction (V : Store G) (d : ℕ) (r : ℝ) : Change G d :=
  (V.survey d).firstPass (V.prepared d) (hierarchy F J d r)

/-- This is the native SetEq belonging to the exact Store that defines the
independent MS subtraction, with its original tests and coefficients; both
instances of the finite nonlinear transformation act simultaneously on all
slots. Its Jacobian and the field change itself are invertible on this branch. -/
theorem original (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ) :
    Tendsto (fun r=>guide G d (correction F J V d r)) Trace.Pilot.trail (𝓝 0) ∧
    ∀ᶠ r in Trace.Pilot.trail,
      Fray.SetEq (V.measure d) (correction F J V d r) (hierarchy F J d r) ∧
      Bijective (stand (correction F J V d r)) ∧
      Bijective (slope (V.measure d) (correction F J V d r) (hierarchy F J d r)) := by
  let D := V.survey d
  have bank := warm F J lead V d
  exact ⟨D.turns_approach (V.prepared d) bank, (D.passed (V.prepared d) bank).and
    ((D.stand_sure (V.prepared d) bank).and (D.still (V.prepared d) bank))⟩

theorem unique (lead : PhysMS.Leading F J) (V : Store G) (d : ℕ) (b : ℝ→Change G d)
    (near : Tendsto (fun r=>guide G d (b r)) Trace.Pilot.trail (𝓝 0)) :
    ∀ᶠ r in Trace.Pilot.trail,
      Fray.SetEq (V.measure d) (b r) (hierarchy F J d r) ↔ correction F J V d r=b r :=
  (V.survey d).unmoor (V.prepared d) (warm F J lead V d) b near

end YM.Integration.WilsonPositionPrescribedScreen
