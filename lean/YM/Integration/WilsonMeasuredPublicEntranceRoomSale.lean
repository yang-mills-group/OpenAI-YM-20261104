import YM.Integration.WilsonMeasuredPublicEntranceFaculty
import YM.Integration.WilsonOriginalAlternativeZeroPost
/-! A course chosen before its cutoffs admits the genuine quiet Wilson gas at the named later edge. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRoomSale
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


open WilsonMeasuredPublicEntranceFaculty WilsonOriginalReceivedChain QuadraticLocal.Earn Marker
open PhysicalNext.Repeat.Legato
variable (room:Room s R simple) {m N per:ℕ}
variable (n D q:ℕ)
variable (faculty:WilsonOriginalCensusAttendanceStation.Day s R simple (WilsonMeasuredPublicEntranceFaculty.ask n D q).school m N)
variable {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
local notation "D_" => WilsonOriginalAlternativeFiniteSource.disks (V:=V)
local notation "K_" => WilsonOriginalAlternativeFiniteSource.sectors (V:=V)
local notation "J_" => Stock.census V
local notation "root_" => roots s R simple
local notation "tab_" => tab s R simple

theorem original (size:Fintype.card V ≤ n)(cap:∀v,grades v ≤ D)
    (i:ℕ)(age:m+1 ≤ i)(live:i<N)(o:V → Site (R.family.side (i+1) per)):
    let school:=(WilsonMeasuredPublicEntranceFaculty.ask n D q).school
    let Ψ:=faculty.Ψ per
    let floor:m ≤ i:=by omega
    let source:=fun (_:Wallet D_) (U:Config G (R.family.side (i+1) per))=>
      ((Ψ (i+1)).eval U:ℂ) • Poly.pass (0:Poly J_)
    ∃P:Post (N:=N) R faculty.hk root_ tab_ faculty.π faculty.Γ Ψ room.books room.ahead
        D_ K_ grades school.order school.horizon school.pieces i floor source,
      Countable P.inputIndex ∧ P.modelIndex=Empty ∧ P.inputIndex=Empty ∧
      P.passport=Passport.point o ∧ P.op.count=school.pieces ∧ P.op.stage=school.order+1 ∧
      P.lesson=faculty.lessons i floor live ∧ P.cost=0 ∧ P.rent=1 ∧ P.w=(fun _=>1) ∧
      (∀x j U,P.input.hard.hard x j U=Poly.bead J_ (((Ψ (i+1)).activities.K j U:ℝ):ℂ)) ∧
      Nonempty (Oak.Calendar R faculty.hk root_ tab_ faculty.π faculty.Γ Ψ floor (N:=N) P.lesson):=by
  intro school Ψ floor source
  have dim:=dimensions n D q grades size cap
  obtain ⟨attends,op,width,stage⟩:=opportunity faculty per i age live
  obtain ⟨P,counted,emptyModel,emptyInput,placed,atOp,trained,cost,rent,weights,hard⟩:=
    WilsonOriginalAlternativeZeroPost.original R faculty.hk root_ tab_ faculty.π faculty.Γ Ψ
      room.books room.ahead grades school.order school.horizon school.pieces floor live
      (register room faculty per) op (faculty.lessons i floor live) o width
      (dim.2.2.2.2.1.trans_eq width.symm) dim.2.2.2.2.2 stage.ge
  exact ⟨P,counted,emptyModel,emptyInput,placed,atOp ▸ width,atOp ▸ stage,trained,cost,rent,weights,
    hard,trained ▸ attends⟩

end YM.Integration.WilsonMeasuredPublicEntranceRoomSale
end
