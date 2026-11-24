import YM.Integration.WilsonViewerElectedHierarchy
import YM.Integration.WilsonOriginalAllOrderCourse
import YM.Integration.WilsonMovingForkElectedPhase
import YM.Integration.WilsonIndependentCapturedPages

/-! The original physical chamber and the future infrared pages can be
appointed on one previously purchased run. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolElection
open Filter Lattice Wilson RG Source Extraction Table Spec RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open XSpace XSpace.Normalize
open RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonPositionProgramReporterBand
open scoped Classical Topology BigOperators
universe u
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  {F:Final R.family order S}{L:EveryPhase.Almanac F}
  {Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
  {J:ℝ→PhysMS.tower S}{H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  {l:Ultrafilter (ℕ×ℕ)}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
  {a:Axis}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {crop:Campaign R}{W:Campaign.Pillars R crop}
local notation "C" => R.family

/-- The funded original roster keeps its own regulator extraction and
facilities. One reporting band, selected before the chamber date, admits
every subsequently requested infrared depth on that very same physical ear. -/
theorem original (simple:G.Simple)
    (chosen:WilsonViewerElectedHierarchy.Selected.{u} F L Q J H arch l simple cohort)
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R crop W)
    (slow:WilsonWindowReportingPace.Slow R.kit)(world:XSpace.Run)
    {b:ℕ}(bp:0<b)(ratio:world.ratio=(3:ℕ)^b)(stage:ℕ):
    Facilities C order S ∧ (l:Filter _)≤order.fuse ∧
    ∃ B:Band R world stage,∀ᶠj:ℕ in atTop,∃u:ℕ,j≤u ∧
      Stop C 0 j u ∧ ∀depth:ℕ,Nonempty (WilsonIndependentCapturedPages.Stop R world B u depth):=by
  obtain ⟨B⟩:=WilsonPositionProgramReporterBand.original R world simple paid.nested bp ratio slow.2 stage
  refine ⟨chosen.facilities,chosen.original,B,?_⟩
  obtain ⟨_,_,_,package⟩:=chosen.facilities.costlier
  filter_upwards [RG16.Literal.forStop C chosen.facilities.simpleGate package.toPackage 0] with j bought
  obtain ⟨u,all⟩:=bought
  let stop:=all 0 le_rfl
  refine ⟨u,stop.live.1,stop,?_⟩
  exact fun depth=>WilsonIndependentCapturedPages.original R world simple slow B u depth

end YM.Integration.WilsonOriginalTwoFlatIRPoolElection
end
