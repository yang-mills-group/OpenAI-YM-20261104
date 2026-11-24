import YM.Integration.WilsonOriginalCensusAttendanceStation
import YM.Integration.WilsonMeasuredPublicEntrancePurchased
/-! Elect the original room once. A common physical school before both regulators
supports every panel drawn from the fixed public arity and grade bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFaculty
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open LocalComparison
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
  {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation WilsonOriginalCensusFundedAttendance
open WilsonReceivedFirstTrace Pert.Asymptotics

def ask (n D q:ℕ):Demand 0 q (fun _:Fin n=>D):=quote 0 q (fun _:Fin n=>D)

theorem dimensions (n D q:ℕ){V:Type}[Fintype V](grades:V → ℕ)(size:Fintype.card V ≤ n)(cap:∀v,grades v ≤ D):
    let course:=ask n D q
    2*q+8 ≤ course.school.order ∧ q+3 ≤ 3*course.vac+2 ∧ course.school.order ≤ Burn.horizon course.vac+1 ∧
    1 ≤ course.school.pieces ∧ Fintype.card V ≤ course.school.pieces ∧ (∑v,grades v) ≤ course.school.horizon:=by
  intro course
  have high:course.school.order=max 0 (2*(q+1)+8):=rfl
  have width:course.school.pieces=max 1 n:=rfl
  have slots:course.school.horizon=∑_:Fin n,D:=rfl
  have vac:course.vac=n+course.school.order+course.school.horizon+q+4:=rfl
  have total:(∑v,grades v) ≤ Fintype.card V*D:=by
    simpa using (Finset.sum_le_sum (s:=Finset.univ) (fun v _=>cap v))
  refine ⟨by omega,by omega,?_,width.symm ▸ le_max_left _ _,size.trans (width.symm ▸ le_max_right _ _),?_⟩
  · change course.school.order ≤ 3*course.vac+1;omega
  · rw [slots];simpa using total.trans (Nat.mul_le_mul_right D size)

def register {V:Type}[Fintype V][DecidableEq V]{k m N:ℕ}{school:Syl.School k}
    (room:Room s R simple)(faculty:Day s R simple school m N)(per:ℕ):
    WilsonReceivedFirstTrace.Registration (m:=m) (N:=N) (k:=k) R (roots s R simple) (tab s R simple)
      faculty.π faculty.Γ (faculty.Ψ per) room.books room.ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
      school.horizon school.pieces:=
  ⟨simple,(faculty.seen per).1,WilsonPhysicalHistoryPriorAperture.law G MintClock.splits,room.chamber,room.hospital,
    school.sense,(by have h:=school.tall;omega : school.horizon ≤ Burn.horizon k+2).trans faculty.hk,
    WilsonOriginalAlternativeFiniteSource.fired⟩

theorem opportunity {k m N:ℕ}{school:Syl.School k}(faculty:Day s R simple school m N)(per i:ℕ)
    (after:m+1 ≤ i)(live:i<N):
    let lesson:=faculty.lessons i (by omega) live
    Nonempty (Oak.Calendar R faculty.hk (roots s R simple) (tab s R simple) faculty.π faculty.Γ
      (faculty.Ψ per) (by omega) (N:=N) lesson) ∧
    ∃op:Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i),
      op.count=school.pieces ∧ op.stage=school.order+1:=by
  intro lesson
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
  obtain ⟨_,attends,_,op,_,_,amount,level⟩:=(faculty.seen per).2.2.2 j (by omega) live
  exact ⟨attends,op,amount,level⟩

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W):
    ∃room:Room s R simple,∀n D q:ℕ,
    let course:=ask n D q
    ∀ᶠ m:ℕ in atTop,
      (WilsonReceivedMeasuredStampPrice.opening R simple q course.school.order course.vac
        (dimensions n D q (fun _:Fin 0=>0) (by simp) (by simp)).1
        (dimensions n D q (fun _:Fin 0=>0) (by simp) (by simp)).2.1 (by norm_num:0<(1:ℝ))) ≤ m+1 ∧
      6*course.school.pieces ≤ R.alloy.B.a.clock.J m ∧
      ∀N,m ≤ N → ∃faculty:Day s R simple course.school m N,
        (∀per i,m ≤ i → i ≤ N → 0<regulatorRun R.family N per i ∧ regulatorRun R.family N per i ≤ 1) ∧
        (∀per i,m ≤ i → i ≤ N → (faculty.Ψ per i).p.supportExponent=100) ∧
        (∀i,(R.family.path.levels.params i).supportExponent=100) ∧
        ∀(V:Type)[Fintype V][DecidableEq V] (per:ℕ),Nonempty
          (WilsonReceivedFirstTrace.Registration (m:=m) (N:=N) (k:=course.vac) R (roots s R simple) (tab s R simple)
            faculty.π faculty.Γ (faculty.Ψ per) room.books room.ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
            course.school.horizon course.school.pieces):=by
  classical
  obtain ⟨⟨room⟩,seats⟩:=WilsonOriginalCensusPhysicalAttendance.original paid
  refine ⟨room,?_⟩
  intro n D q course
  let bound:=dimensions n D q (fun _:Fin 0=>0) (by simp) (by simp)
  let opener:=WilsonReceivedMeasuredStampPrice.opening R simple q course.school.order course.vac
    bound.1 bound.2.1 (by norm_num:0<(1:ℝ))
  have climb:Filter.Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  obtain ⟨ice,frozen⟩:=eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)
  filter_upwards [seats course.vac course.school course.deep,eventually_ge_atTop opener,
    climb.eventually_ge_atTop (6*course.school.pieces),eventually_ge_atTop ice] with m seated open_ tall cold
  refine ⟨open_.trans (Nat.le_succ _),tall,?_⟩
  intro N live
  obtain ⟨faculty⟩:=WilsonOriginalCensusAttendanceStation.choose_day seated live
  refine ⟨faculty,?_,?_,paid.support,fun V _ _ per=>⟨register room faculty per⟩⟩
  · intro per i lo hi
    have day:=frozen i (cold.trans lo) N per hi
    exact ⟨day.1,by linarith only [day.1,day.2]⟩
  · intro per i lo hi
    have day:=(faculty.seen per).1.1.walk i lo hi
    rw [day.truep.point]
    exact paid.support i

end YM.Integration.WilsonMeasuredPublicEntranceFaculty
end
