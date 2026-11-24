import YM.Integration.WilsonMatrixTicketLanesReportedRunMS
import YM.Integration.WilsonMatrixTicketLanesStrongSeed

/-! Original projected physical bases and all-order paid MS finite forest rows on one refined extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedSeed
open Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Extract Dash Spec OPE OPE.RigE MergeProof MergeProof.Accent
open MS MS.Land FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2
open scoped Classical
variable {G : Gauge}

/-- The same original run and one chosen refinement carry the joint finite basis used to test the independent matched marked fields. -/
theorem original (R : Run G) (simple : G.Simple) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial : Bool) :
    ∃ scheme Q : Prescription (Press.portDeck G), Main.Match N simple M scheme dial ∧ Q.team=scheme.team ∧
      TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧ ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (A : Table R.family.book) (L : ℕ → Table R.family.book)
          (B : Bin A) (Z : ∀ d, ℕ → CoordMap R.family d) (tr : Presentation R.family)
          (S : Table R.family.book) (E : DiffPlan S),
          Projected tr (f.refine g) B Z ∧ Base R.family (f.refine g) A L B S E ∧
          Nonempty (Seed R.family (f.refine g) S) ∧ (∀ d, StrongBin R.family B (f.refine g) d) ∧
          (∀ d, UVExt.Slots.StrongBin R.family B (f.refine g) d) ∧
          ∀ (J : ℕ) (hJ : 0 < J) (c : ℝ) (hc : 1 < c),
            WilsonMatrixTicketLanesReportedRun.Statement R M Q (f.refine g) simple J hJ hc := by
  obtain ⟨scheme,Q,matchMS,team,taylor,allProfiles,curve⟩ := WilsonMatrixTicketLanesReportedRunMS.original R simple N M dial
  refine ⟨scheme,Q,matchMS,team,taylor,allProfiles,?_⟩
  intro f
  obtain ⟨g,A,L,B,Z,tr,S,E,projected,base,seed,strong,physical⟩ := WilsonMatrixTicketLanesStrongSeed.original R simple f
  exact ⟨g,A,L,B,Z,tr,S,E,projected,base,seed,strong,physical,curve (f.refine g)⟩

end YM.Integration.WilsonMatrixTicketLanesReportedSeed
