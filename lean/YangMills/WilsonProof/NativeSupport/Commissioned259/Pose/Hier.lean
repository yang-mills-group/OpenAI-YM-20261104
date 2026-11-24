import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Slip
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Scale
import YM.AllOrder.Leading.Solve
/-! # On the exact continuum operands. W through the common cap D. Same definitions as
 `Integration/WilsonPositionPrescribedScreen` (copied for import purposes) & on any Leading
 tower; use on `positioned F J` at §G and `H`. Non-phase S for this calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose.Paper
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
    ContinuousOn (fun x=>point F J r d n x v) (conf n) := by
  let D(j:Fin n): S.Tag:= ⟨d,J r d ((Maxwell.Free.fields C.labels d).symm (v j))⟩
  exact (S.class_smooth _ (spectate F none).smooth D ).continuousOn.comp (f:=fun x:Points n=>r • x)
    (by fun_prop) (fun x hx=> Work.A05.smul_conf hr hx)

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

lemma use (d n : ℕ) (u : Fin n→Sec G d) (r : ℝ) (x : Points n) : point F J r d n x u = S.classMoment S (fun _=>d) (r • x) (Original.own J r u) := rfl
/-- Exact raising of every slot of `point` in the physical branch. -/
lemma pointing {e d n : ℕ} (hJ : Leading F J) (he : e ≤ d) : ∀ᶠ r in Trace.Pilot.trail,
    ∀ u : Fin n → Sec G e,∀ x∈conf n, point F J r e n x u=point F J r d n x (fun i=>up he (u i)) := by
  filter_upwards [Original.height hJ d, show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin] with r hr s u x hx
  rw [use,use]; unfold Original.own; simp only [hr e he]
  exact Eq.symm (AllOrder.Leading.moment_inclusion (a:=fun _=>e) (d:=fun _=>d) F.room.kernel.laws.toSymmetric F.phase.transport.injection (fun _=>he) (Work.A05.smul_conf s hx) (Original.own J r u))

-- exact W reader. Identified in application with `t` of original construction, same order
-- of projections. So doesn't matter if original uses graded-cap legs or all-six (Leading).
variable {V : Normalize.Store G} (K : Rose.Pick V)
def one_time (U:tower S) (r:ℝ) : ℝ :=
  ((Rose.test K).applyTo (fun x=> log3 (fun i=>point F (fun _=>U) r 6 3 x (Rose.missing (Rose.tag G) i)))).re/Rose.c_T K

def meter (r : ℝ) : ℝ := one_time F K (J r) r
-- name. Latest t defined via W effectively.
lemma value (r : ℝ) : meter F J K r =
    ((Rose.test K).applyTo (fun x=> log3 (fun i=>point F J r 6 3 x (Rose.missing (Rose.tag G) i)))).re/Rose.c_T K := rfl

end YM.FVA2.GradedFar259.Pose.Paper
