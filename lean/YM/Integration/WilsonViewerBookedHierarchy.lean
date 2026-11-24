import YM.Integration.WilsonViewerMixedHorizons
import YM.Integration.WilsonPositionTraceOrientedFrame
import YM.Integration.WilsonMaxwellThermometerKineticRelease
import YM.Integration.WilsonPublicOutputSmooth

/-! Keep the Rose station and the exterior matrix lanes when selecting the
single public hierarchy from the funded original classroom. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerBookedHierarchy
open Function Filter Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler ThroughLaunch
open AllOrder AllOrder.Transit AllOrder.Transit.WheelP QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonWindowJointPurchase WilsonWindowBookPurchase
open MSbar.Heath OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank WilsonMarkedIndependentPhysicalIntake
open WilsonVacuumPreResetFiniteHeatScale WilsonVacuumPreResetFiniteHeatTable
open Spec Extraction Table Climb OPE OPE.Orbits OPE.Log RG17 PhysMS Trace.Pilot
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonViewerElectedHierarchy
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {φ : ℕ → ℕ}

def OnClass (R : Run G) (simple : G.Simple) (cohort : Ultrafilter (ℕ×ℕ) → Prop) : Prop :=
  ∀ f : Extraction.Order, ∃ (w : Extraction.Order) (S : Table R.family.book)
    (F : Final R.family (f.refine w) S) (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (Y : (Bel R.family.book).Hierarchy)
    (A : Trace.Terrace.Arch R.family) (ℓ : Ultrafilter (ℕ×ℕ)) (rose : ℝ → Group R.family 6),
    WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort ∧ Book (f:=f.refine w) (l:=ℓ) (H:=Y) rose J

theorem on_run {T : Campaign R} (W : Campaign.Pillars R T) (simple : G.Simple) {ε : ℝ}
    (fund : FundedOriginalProperties.{u} simple ε W)
    (matrix : WilsonMatrixTicketFuelPrice.FromStrongBin R.family)
    (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (grant : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) :
    OnClass.{u} R simple cohort := by
  intro v
  obtain ⟨w,T₀,rows,B,z,tr,S,E,projected,base,⟨seed⟩,strong,_⟩ :=
    WilsonMatrixTicketLanesStrongSeed.original R simple v
  obtain ⟨F,_,L,Q,_,_,done,trace,exclude,fac,foundation,_,_,_⟩ :=
    WilsonMatrixTicketLanesRetained.original simple W fund (v.refine w) base seed
  have lanes := matrix (v.refine w) T₀ rows B z tr S E F projected base strong fac.toServices
  let basis := Module.finBasis ℂ ((Bel R.family.book).Field 6)
  obtain ⟨Y,A,ℓ,bliss,P,J,shell,profile,κ,d,e,rose,level,scheme,physical,_,lead,obeys,_,paid,_⟩ :=
    WilsonPositionTraceOrientedFrame.original basis F simple trace
  have bill := WilsonMatrixTicketLanes.on_ultrafilter lanes ℓ bliss.lies
  exact ⟨w,S,F,L,Q,J,Y,A,ℓ,through P J rose,
    ⟨done,trace,exclude,fac,foundation,first_log F fac bliss.lies bill Q.spans,bliss,bliss.lies,
      grant _ _ bliss.lies,bill,lead,obeys,_,_,profile,κ,d,e,level,scheme,physical⟩,paid⟩

theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap)
    (simple : G.Simple) {ε ξ : ℝ} (positive : 0 < ε) (finance : Glacier (a:=a) simple ξ)
    (law : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted law s (ThroughLaunch.raging s q))
    (bills : ℕ → ℕ → Gear G → ℝ) (extra : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonReportingAbsoluteInletSchool.OnRun.{u} cap simple ε law U
        (@WilsonOriginalSeparatedElection.demands G φ simple law split U bills (@extra)) R T W ∧
      WilsonPositionProgramNestedElection.course simple a ξ R.kit ∧ R2I.RG05Joint.AcrossPanels R.kit ∧
      (∀ i, (R.family.path.levels.budget i).supportExponent = 100) ∧ WilsonOriginalSeparatedElection.Quiet R ∧
      ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        OnClass.{u} R simple cohort := by
  obtain ⟨R,T,W,source,course,panels,strip,quiet,_⟩ :=
    WilsonOriginalSeparatedElection.original.{u} a cap U mono simple positive finance law split permitted
      bills (@extra) paid
  have fund : FundedOriginalProperties.{u} simple ε W :=
    by obtain ⟨_,_,_,_,_,_,_,_,_,_,h,_⟩ := source; exact h
  exact ⟨R,T,W,source,course,panels,strip,quiet,
    on_run W simple fund (WilsonMatrixTicketFuelPrice.lanes R finance.price finance.charge course.1)⟩

end YM.Integration.WilsonViewerBookedHierarchy
end
