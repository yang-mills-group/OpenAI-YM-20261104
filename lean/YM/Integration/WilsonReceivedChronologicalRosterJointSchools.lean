import YM.Integration.WilsonReceivedChronologicalRosterDenseFiled
import YM.Integration.WilsonReceivedChronologicalRosterJointDepth

/-! Finitely many actual occupied schools, with separate fitted purses, earn their
own finite Taylor degrees at a common preselected physical infrared depth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterJointSchools
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

structure Experiment where
  arity : ℕ
  head : Fin arity
  grades : Fin arity → ℕ
  positive : ∀i,0 < grades i
  lens : Fin arity → ℕ
  chambers : Fin arity → Chamber
  cover : ∀i,grades i < lens i
  caps : Fin arity → ℝ
  nonneg : ∀i,0 ≤ caps i
  fees : ∀i,‖WilsonReceivedCanonicalSocketSeed.present lens i‖ ≤ caps i
  test : Test arity
  pole : ℕ
  target : ℕ
  capital : ℝ
  solvent : 0 ≤ capital

variable {I:Type*}[Fintype I]
def precision (tasks:I→Experiment)(i:I):ℕ :=
  WilsonReceivedChronologicalRosterJointDepth.precision (fun j=>(tasks j).arity) (fun j=>(tasks j).grades)
    (fun j=>(tasks j).pole) (fun j=>(tasks j).target) i

def depth (tasks:I→Experiment):ℕ :=4*WilsonReceivedChronologicalRosterJointDepth.level
  (fun j=>(tasks j).arity) (fun j=>(tasks j).grades) (fun j=>(tasks j).pole) (fun j=>(tasks j).target)

theorem aligned (tasks:I→Experiment)(i:I) :
    (tasks i).target ≤ precision tasks i ∧
    WilsonReceivedChronologicalRosterRanks.infrared (tasks i).grades
      (WilsonReceivedChronologicalRosterRanks.restored (tasks i).arity (tasks i).pole (precision tasks i))=
        depth tasks:=
  WilsonReceivedChronologicalRosterJointDepth.original (fun j=>(tasks j).arity) (fun j=>(tasks j).grades)
    (fun j=>(tasks j).pole) (fun j=>(tasks j).target) i

structure Grant (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(tasks:I→Experiment)(reserve window:ℕ)(η:ℝ)(tube:LinkTube G) where
  aperture : I→ℕ
  travel : I→ℕ
  sold : ∀i,WilsonReceivedChronologicalRosterDenseFiled.Admitted paid paths (tasks i).head (tasks i).grades
    (tasks i).lens (tasks i).chambers (tasks i).caps (tasks i).fees (tasks i).test reserve window
    (precision tasks i) (tasks i).pole (aperture i) (travel i) (tasks i).capital η tube

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(tasks:I→Experiment)(reserve window:ℕ)
    (slow:WilsonWindowReportingPace.Slow R.kit)(tol η:ℝ)(tp:0<tol)(ep:0<η)(school:ℕ)(tube:LinkTube G)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (pieces physical:ℕ)(p:Bool→ℕ)(span:U→ℕ)(lag:U→Bool→ℕ):
    Nonempty (Grant paid paths tasks reserve window η tube):=by
  classical
  choose A travel bought using fun i:I=>WilsonReceivedChronologicalRosterDenseFiled.original paid paths
    (tasks i).head (tasks i).grades (tasks i).positive (tasks i).lens (tasks i).chambers (tasks i).caps
    (tasks i).nonneg (tasks i).cover (tasks i).fees (tasks i).test reserve window (precision tasks i) (tasks i).pole
    (tasks i).capital (tasks i).solvent slow tol η tp ep school tube ready pieces physical p span lag
  exact ⟨⟨A,travel,bought⟩⟩

end YM.Integration.WilsonReceivedChronologicalRosterJointSchools
end
