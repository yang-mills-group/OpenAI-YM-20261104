import YM.Integration.WilsonReceivedChronologicalRosterJointSchools

/-! Intersect the native residents and the separately booked angular realms before
choosing the one physical stop used by all the registered experiments. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterJointCalendar
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{U:Type}[Fintype U]

open WilsonReceivedChronologicalRosterJointSchools (Experiment Grant)
variable {I:Type*}[Fintype I] {tasks:I→Experiment}
  {paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W}
  {paths:FundedOriginalVacuumPaths.prices R.kit}{reserve window:ℕ}{η:ℝ}{tube:LinkTube G}
  (funded:Grant paid paths tasks reserve window η tube)

def Due {p:ℕ→Prop} (_ : ∀ᶠ n:ℕ in atTop,p n)(x:ℕ):Prop:=p x

def Office (i:I)(o:ℕ):Prop:=Due (funded.sold i).choose_spec.choose_spec.choose_spec.2 o

def Faculty {i:I}{o:ℕ}(office:Office funded i o)(anchor:ℕ):Prop:=
  Due office.2.2.choose_spec.2 anchor

theorem original :
    ∀ᶠ o:ℕ in atTop,∃office:∀i,Office funded i o,
      ∀ᶠ anchor:ℕ in atTop,∀i,Faculty funded (office i) anchor:=by
  have resident:∀i:I,∀ᶠ o:ℕ in atTop,Office funded i o:=
    fun i=>(funded.sold i).choose_spec.choose_spec.choose_spec.2
  filter_upwards [Filter.eventually_all.mpr resident] with o ready
  refine ⟨ready,Filter.eventually_all.mpr ?_⟩
  exact fun i=>(ready i).2.2.choose_spec.2

abbrev appointment {o anchor:ℕ}{i:I}{office:Office funded i o}(faculty:Faculty funded office anchor)
    {world:XSpace.Run}{stage:ℕ}{band:WilsonPositionProgramReporterBand.Band R world stage}
    (v:WilsonIndependentCapturedPages.Stop R world band o (WilsonReceivedChronologicalRosterJointSchools.depth tasks)):=
  faculty.choose_spec.choose_spec.2.2 world stage band
    (WilsonReceivedChronologicalRosterJointDepth.sameStop (WilsonReceivedChronologicalRosterJointSchools.aligned tasks i).2.symm v)

end YM.Integration.WilsonReceivedChronologicalRosterJointCalendar
end
