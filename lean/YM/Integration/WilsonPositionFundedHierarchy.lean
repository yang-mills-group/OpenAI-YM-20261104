import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.Integration.WilsonPositionTraceOrientedFrame

/-! The reconstructed reader and the oriented reporting basis on one funded
Wilson run, together with a scaling sequence from that same extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionFundedHierarchy
open Filter Table Spec OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open scoped Topology Classical
universe u

theorem original {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
    (simple : G.Simple) {ε : ℝ} (funded : WilsonLimitConstruction.FundedOriginalProperties.{u} simple ε W)
    {I : Type} [Fintype I] (b : Module.Basis I ℂ ((Bel R.family.book).Field 6)) :
    FVA2.Atoll.Main.Packing simple (FVA2.Atoll.share R.family R.makes (CoefficientBridge.run_valuation R)) ∧
    ∀ v : Extraction.Order, ∃ (w : Extraction.Order) (S : Table R.family.book)
      (F : Final R.family (v.refine w) S) (L : EveryPhase.Almanac F)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin),
      EveryPhase.Completed F L ∧ Target.Result.{u} F simple ∧ Target.Exclusion.{u} F ∧
      OPE.Facilities R.family (v.refine w) S ∧ Foundation F Q ∧
      ∃ (H : (Bel R.family.book).Hierarchy) (arch : Terrace.Arch R.family)
        (l : Ultrafilter (ℕ × ℕ)) (X : Scaling S), Bliss F l arch H ∧
        (∃ V, Over.Scribe (v.refine w) X V arch F.sector l F.room.kernel H) ∧
        WilsonPositionTraceOrientedFrame.Calibrated b F simple H arch l := by
  obtain ⟨-,-,-,-,-,-,-,-,bank,receipt,-⟩ := funded
  refine ⟨bank,fun v => ?_⟩
  obtain ⟨w,S,F,L,Q,done,truth,exclude,physical,foundation,-⟩ := receipt v
  obtain ⟨H,arch,l,bliss,station⟩ := WilsonPositionTraceOrientedFrame.original b F simple truth
  obtain ⟨X,V,scribe⟩ := Trace.Pilot.skyline F simple bliss
  exact ⟨w,S,F,L,Q,done,truth,exclude,physical,foundation,H,arch,l,X,bliss,⟨V,scribe⟩,station⟩

end YM.Integration.WilsonPositionFundedHierarchy
