import YM.Integration.WilsonReportPrescribedFrame
import YM.Integration.WilsonReportSamePillars
import YM.Pier.Scene.Seed

/-! The original finite marked scene, at the measured reporting stop, on
the previously selected continuum sector and its prescribed position
fields. The finite early-sector integral and its regular approximation
refer to the same Wilson law, extraction, and physical coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPrescribedScene
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS Trace
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- One physical stop, one mantle and one layout. All genuine finite,
mutually exclusive early reports and their price are kept on this
particular preassigned Final, even if other Finals could be extracted. -/
theorem selected (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {K : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F K (J r) d) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      Pier.Scene.ScenePlan R F L ∧ ∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d := by
  obtain ⟨u,Q,L,hu,pegs,level,shift,price,_⟩ :=
    WilsonReportPrescribedFrame.selected hG W original pace hB F fac J H paid
  have near : RG17.Panoramic.Comparably R L.level := level ▸ WilsonReportPrescribedFrame.comparable hG pace hB
  have located : RG17.Located L := by
    apply RG17.situated Q L fac.toServices pegs reader
    · intro d
      rw [shift]
      exact RateLE.const _ RG17.ageLarge
    · intro d
      rw [shift]
      exact RateLE.const _ RG17.ageLarge
    rw [shift]
    exact Eventually.of_forall fun _=>rfl
  have seed := WilsonReportSamePillars.original hG W original subsidy pace
  refine ⟨u,Q,L,hu,pegs,level,?_,price⟩
  exact ⟨located,RG17.commands Q L fac.toServices pegs,shift,near,shapesPay R L fac.toServices located pegs,
    fun _ d=>wholeFrame R L fac.toServices seed located near d⟩

end YM.Integration.WilsonReportPrescribedScene
end

