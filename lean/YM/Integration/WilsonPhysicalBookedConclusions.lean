import YM.Integration.WilsonPhysicalCorrelationAndOrdinaryOPE
import YM.Integration.WilsonViewerBookedHierarchy
import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerFinance
import YM.Integration.WilsonPhysicalOriginalReplicaAndCharacter

/-! The book, finite reflected budgets, original matrix and fine calendar are
purchased on the same campaign before any requested finite physical experiment. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalBookedConclusions
open Filter Table Spec Extraction Climb Lattice PhysMS Trace.Pilot OPE OPE.Orbits
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonViewerElectedHierarchy
open FVA2 FVA2.Register FVA2.Scale Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
variable {a : Axis} {simple : G.Simple} {κ : ℝ} {s : WilsonOriginalAllOrderCourse.Schedule G}

/-- The financed original master for the public conclusions. Only a finite numerical
Rose test and the original finite determining rows of the given experiment remain. -/
def OnRun (R : Run G) (simple : G.Simple) (cohort : Ultrafilter (ℕ×ℕ) → Prop)
    (v : Extraction.Order) : Prop :=
  ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
    (L : EveryPhase.Almanac F) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (Y : (Bel R.family.book).Hierarchy) (arch : Trace.Terrace.Arch R.family)
    (ℓ : Ultrafilter (ℕ×ℕ)) (rose : ℝ → Group R.family 6),
  ∃ run : Selected.{u} F L Q J Y arch ℓ simple cohort, Book (f:=v.refine w) (l:=ℓ) (H:=Y) rose J ∧
    (∀ D, ∃ t : ℕ, ∀ᶠ r in trail, ∃ j m, m ≤ j ∧ r < dock r^t * R.family.S.a j ∧
      R.family.S.a m < r*dock r^t ∧ WilsonPhysicalCommonElection.Ordered F ℓ r j m D (dock r^t)) ∧
    (∀ (I E : Type) [Fintype I] [Fintype E] (d : I → ℕ) (anchor : I),
      type_of% (WilsonPhysicalOriginalReplicaAndCharacter.original (d:=d) (E:=E) run
        (l:=trail) (T:=LogV) anchor PhysMS.to_log_zoom)) ∧
    ∀ (Z : WilsonPrescription G) {d : ℕ}, 0 < d → Z.run.ratio = 3^d → ∀ B : ℕ, 0 < B →
    ∃ fine index : ℝ → ℕ, WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index ∧
      ∀ (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν : ℝ) (dial : Bool)
        {n : ℕ} (d₀ : ℕ) (φ : Test n) (v₀ : Fin n → Sec G d₀),
        WilsonMaxwellThermometerKineticRequest.earned (Y:=ℓ) Z F J rose simple (B:=B) fine index d₀ φ v₀ 1 →
        WilsonPhysicalCorrelationAndOrdinaryOPE.Conclusion run Z M ν dial

theorem on_run (cash : WilsonOriginalAllOrderCourse.Paid.{u} a simple κ s R T W)
    (cohort : Ultrafilter (ℕ×ℕ) → Prop)
    (admit : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ×ℕ)), (l : Filter _) ≤ f.fuse → cohort l)
    (v : Extraction.Order) : OnRun.{u} R simple cohort v := by
  obtain ⟨fund,pace,_⟩ := WilsonPhysicalCommonElection.finances cash
  let lender := OPE.Stroke.PoleC (OPE.Stroke.Earτ a simple)
  have lanes := WilsonMatrixTicketFuelPrice.lanes R lender.price lender.charge cash.nested.1
  obtain ⟨w,S,F,L,Q,J,Y,arch,ℓ,rose,run,book⟩ :=
    WilsonViewerBookedHierarchy.on_run W simple fund lanes cohort admit v
  refine ⟨w,S,F,L,Q,J,Y,arch,ℓ,rose,run,book,WilsonPhysicalCommonElection.before_limits run,?_,?_⟩
  · intro I E _ _ d anchor
    exact WilsonPhysicalOriginalReplicaAndCharacter.original (d:=d) (E:=E) run (l:=trail)
      (T:=LogV) anchor PhysMS.to_log_zoom
  intro Z d hd ratio B hB
  obtain ⟨fine,index,schedule⟩ := WilsonOriginalPositionFineScheme.calendar (R:=R) (Z:=Z) (hG:=simple) (B:=B) (hB:=hB) (pace:=pace)
    (WilsonPositionProgramNestedElection.prior cash.nested) hd ratio
  refine ⟨fine,index,schedule,?_⟩
  intro M ν dial n d₀ φ v₀ first
  exact WilsonPhysicalCorrelationAndOrdinaryOPE.original run Z M ν cash dial rose book hB fine index
    schedule d₀ φ v₀ first

theorem original (a : Axis) (simple : G.Simple) {κ : ℝ} (positive : 0 < κ)
    (s : WilsonOriginalAllOrderCourse.Schedule G) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
    ∃ cash : WilsonOriginalAllOrderCourse.Paid.{u} a simple κ s R T W,
      (type_of% (WilsonOriginalPhysicalFirstEntryOwnerFinance.attached cash)) ∧
      WilsonThermometerClusterProjectionBudget.Ready R.family.path.levels ∧
      WilsonReportLampForecast.Ready R.family.path.levels ∧ FundedOriginalVacuumPaths.prices R.kit ∧
      ∀ cohort : Ultrafilter (ℕ×ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ×ℕ)), (l : Filter _) ≤ f.fuse → cohort l) →
        ∀ v : Extraction.Order, OnRun.{u} R simple cohort v := by
  obtain ⟨R,T,W,cash,bank,lamp,vacuum⟩ :=
    WilsonOriginalPhysicalFirstEntryOwnerFinance.original.{u} a simple positive s
  exact ⟨R,T,W,cash,WilsonOriginalPhysicalFirstEntryOwnerFinance.attached cash,bank,lamp,vacuum,
    fun cohort admit v => on_run cash cohort admit v⟩

end YM.Integration.WilsonPhysicalBookedConclusions
