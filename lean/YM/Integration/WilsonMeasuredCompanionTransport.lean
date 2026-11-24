import YM.Integration.WilsonThermometerMixedCorridorReading
import YM.Integration.WilsonMeasuredCompanionFace

/-! Hearing the true difference of two entire-source tables at a face that
contains the charged entrant, on the original normalized older Wilson kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionTransport
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Multi QuadraticLocal Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open MergeProof.Accent WilsonThermometerUnitFilingCoarse WilsonGeometricSignedCapture
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){N p t i j:ℕ}
local notation "C" => R.family
local notation "H" => R.family.path
local notation "J" => Stock.census (Fin 3)

def key (s:(J).Mode)(z:(J).Mode):ℂ:=if z=s then 1 else 0

theorem identified (s:(J).Mode)(w:Fin 3→ℝ)(A:Poly (J)):
    take (key s) A=A.part s ∧ weightBill (key s) w=1/Poly.toll w s:=by
  constructor
  · simp [take,key,ite_mul]
  · unfold weightBill
    rw [sum_eq_single s]
    · simp [key]
    · intro z _ ne; simp [key,ne]
    · simp

private theorem table (F:Config G ((C).side t p)→Poly (J))(paid:Integrable F (prior G _))
    (s:(J).Mode)(it:i ≤ t): (fun U=>(gust (H) N p t F i it U).part s)=
    gust (H) N p t (fun U=>(F U).part s) i it:=by
  induction it using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
    simp_rw [gust_step _ _ _ _ _ hi]
    exact (push_get ((C).path.levels.transition_mass ..) (gust_live (C).path N p t _ paid hi) s).trans
      (congrArg _ ih)

private theorem tower (F:Config G ((C).side t p)→ℂ)(it:i ≤ t)(ji:j ≤ i):
    gust (H) N p i (gust (H) N p t F i it) j ji=gust (H) N p t F j (ji.trans it):=by
  induction ji using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ j hj ih =>
    rw [gust_step (H) N p i _ hj,gust_step (H) N p t _ (hj.trans_le it),ih]

theorem through (F:Config G ((C).side t p)→Poly (J))(paid:Integrable F (prior G _))
    (s:(J).Mode)(it:i ≤ t)(ji:j ≤ i):reading R (N:=N) (fun U=>(gust (H) N p t F i it U).part s) j ji=
    reading R (N:=N) (fun U=>(F U).part s) j (ji.trans it):=by
  rw [table R F paid s it]
  unfold reading
  rw [tower R _ it ji]

theorem subtract (F K:Config G ((C).side t p)→ℂ)(payF:Integrable F (prior G _))
    (payK:Integrable K (prior G _))(jt:j ≤ t):reading R (N:=N) (fun U=>F U-K U) j jt=
      reading R (N:=N) F j jt - reading R (N:=N) K j jt:=by
  have field:gust (H) N p t (F-K) j jt=gust (H) N p t F j jt-gust (H) N p t K j jt:=by
    induction jt using Nat.decreasingInduction with
    | self => rw [gust_base,gust_base,gust_base]
    | of_succ i hi ih =>
      rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ F hi,gust_step _ _ _ _ K hi,ih]
      funext V
      simp only [StepData.push,Pi.sub_apply,smul_sub]
      exact integral_sub (StepData.push_slice ((C).path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ payF hi))
        (StepData.push_slice ((C).path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ payK hi))
  unfold reading
  rw [←mul_sub]
  exact congrArg (fun z:ℂ=> _*z) (congrFun field 1)

end YM.Integration.WilsonMeasuredCompanionTransport
