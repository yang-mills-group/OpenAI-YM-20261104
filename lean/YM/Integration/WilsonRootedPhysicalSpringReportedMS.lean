import YM.Integration.WilsonRootedPhysicalSpringAffineRows
import YM.Integration.WilsonMatrixTicketLanesReportedOrigin
import YM.Integration.WilsonMatrixTicketLanesReportedRunMS

/-! The physical scalar estimates and the signed regulator-scale MS report use a common lower calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalSpringReportedMS
open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge} {B : Deck G} 

open WilsonMatrixTicketLanesReportedClock
open WilsonMeasuredWindow

open RG.Supply PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open FVA2.Register YM.FVAAlt2 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep Org
open WilsonRootedPhysicalSpringAffineRows
universe u

/-- The pointwise invoice inside ReportedRun.Statement at its original lower stage. -/
def Filed (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B) (f : Extraction.Order)
    (simple : G.Simple) (J : ℕ) (hJ : 0 < J) {c : ℝ} (hc : 1 < c) (b : ℕ) : Prop :=
    ∀ (u : Filter (ℕ×ℕ)), u ≤ f.fuse →
      ∀ (σ : (w : ActualOuterQuarterProfile.Cutoffs ℝ) → Picks R.family.path w.2.2) (μ : ℝ) (n : ℕ)
        (z : ℝ → Fin n → MS.Tone.QP) (K η : ℝ), 0 ≤ K → ∀ hη : 0 < η,
        (∀ r i, ‖z r i‖ ≤ K) → (∀ r i j, i ≠ j → η ≤ ‖z r i-z r j‖) →
        let m := stop R.family.path.levels simple J
        let U := upper R simple J c
        let depth := fun r => U r-b
        let θ := aperture R simple J c η
        let hθ := (parameters R simple J hJ hc hη).1
        let P := ActualRelativeProfileTrial.trial R (fun r => b+depth r) θ hθ μ z
        let L := WilsonMatrixTicketLanesReportedProfiles.panel R b depth σ
        ∃ (paid : (w : ActualOuterQuarterProfile.Cutoffs ℝ) → Long (L w)) (E : (w : _) → Exhibit (L w)),
          (∀ w, (E w).chart=R.metals.O ∧ (E w).quotes=quotes R.family.path w.2.2 b (depth w.1) ∧
            ∀ V : Warehouse G, CapReady.Article V (L w) (E w) (paid w)) ∧
          (∀ᶠ r in 𝓝[>] (0:ℝ), b+depth r = U r ∧ Real.exp (θ r) = r/R.family.S.a (U r)) ∧
          ∀ (v : Fin n → Label B) (s : Finset (Fin n)) (q order : ℕ) (fee : ℝ), 0 < fee →
            ∀ᶠ w in (𝓝[>] (0:ℝ)).curry u,
              ‖fare (Label.h ∘ v) P.profile (WilsonMatrixTicketLanesMirrorAccuracy.receipts
                (WilsonMatrixTicketLanesNativePrices.warehouse R) P A μ v L E) s q w -
                Dial.tour M v μ (testP P w) s q‖ ≤ fee *
                Pert.Asymptotics.regulatorRun R.family w.2.1 w.2.2 (m w.1) ^ order

theorem posted (R : Run G) (paid : ManuscriptQLocalCofinalAffineFields.Paid R)
    (ready : ∀ through : ℕ, ∃ first : ℕ, After R paid through first)
    {O : Booked B} (M : MS_Data G O) (Q : Prescription B)
    (matched : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) Q)
    (through : ℕ) (f : Extraction.Order) (simple : G.Simple) (J : ℕ) (hJ : 0 < J) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ b : ℕ in atTop, After R paid through b ∧ Filed R M Q f simple J hJ hc b := by
  obtain ⟨first,rows⟩ := ready through
  have reports : ∀ᶠ b : ℕ in atTop, Filed R M Q f simple J hJ hc b :=
    WilsonMatrixTicketLanesReportedRun.original R M Q matched f simple J hJ hc
  filter_upwards [eventually_ge_atTop first, reports] with b enough report
  refine ⟨?_,report⟩
  intro I inst Γ d eligible
  exact rows d (enough.trans eligible)

private theorem interviews (R : Run G) (simple : G.Simple)
    (offer : WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit) : WilsonMatrixTicketLanesReportedOrigin.Fields R := by
  intro f S F L J lead K aligned U B E pegs near n d
  exact WilsonMatrixTicketLanesReportedReturn.original R F L J lead aligned B E pegs near simple offer d

/-- The finite physical field and its signed MS report paid by one marked campaign. -/
def Settled {V : Type} [Fintype V] (simple : G.Simple) (ε : ℝ) (J : Request V)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (S : Prescription (Press.portDeck G)) (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
    (paid : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G)) : Prop :=
  WilsonRootedPhysicalSpringGaussian.Receipt.{u} simple ε J extra γ
    ManuscriptQLocalCofinalAffineFields.schedule R T W paid.1 ∧
  ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
  WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit ∧ WilsonMatrixTicketLanesReportedOrigin.Fields R ∧
  Q.team = S.team ∧ TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
  MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧
  ∀ (through : ℕ) (f : Extraction.Order) (rung : ℕ) (hrung : 0 < rung) (c : ℝ) (hc : 1 < c),
    ∀ᶠ b : ℕ in atTop, After R paid through b ∧ Filed R M Q f simple rung hrung hc b

/-- File an independently priced physical comparison with the MS reporting forecast before the run. -/
theorem purchasedWith {V : Type} [Fintype V] (simple : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (calendar : XSpace.Run) (dial : Bool)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run = calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G)),
        prediction R.kit ∧ Settled.{u} simple ε J extra γ M S R T W paid Q := by
  obtain ⟨N,M,S,run,matched⟩ := Main.solution G simple calendar dial
  let stock := @FundedPredictionSupply.Both G (@WilsonMatrixTicketLanesReportedPrepaid.Paid G) (@prediction)
  obtain ⟨R,T,W,paid,booked,physical,jets,ready⟩ :=
    WilsonRootedPhysicalSpringAffineRows.purchasedWith.{u} simple hε J extra γ hγ (@stock)
      (fun s t => FundedPredictionSupply.both (WilsonMatrixTicketLanesReportedPrepaid.allPrices (G:=G) s t)
        (price s t))
  obtain ⟨offer,other⟩ := booked
  obtain ⟨Q,team,taylor,profiles⟩ := WilsonMatrixTicketLanesFundedScheme.existing R N matched
  exact ⟨N,M,S,run,matched,R,T,W,paid,Q,other,physical,jets,offer,interviews R simple offer,team,taylor,profiles,
    fun through f rung hrung _ hc => posted R paid ready M Q taylor through f simple rung hrung hc⟩


/-- The independent MS calendar and prescription are chosen before the physical run and every
base stage. The same campaign then pays the submitted signed finite report, its measured
conditional jets and the independently held Gaussian field estimates. -/
theorem original {V : Type} [Fintype V] (simple : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run = calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G)),
        WilsonRootedPhysicalSpringGaussian.Receipt.{u} simple ε J extra γ
          ManuscriptQLocalCofinalAffineFields.schedule R T W paid.1 ∧
        ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
        WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit ∧ WilsonMatrixTicketLanesReportedOrigin.Fields R ∧
        Q.team = S.team ∧ TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
        MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧
        ∀ (through : ℕ) (f : Extraction.Order) (rung : ℕ) (hrung : 0 < rung) (c : ℝ) (hc : 1 < c),
          ∀ᶠ b : ℕ in atTop, After R paid through b ∧ Filed R M Q f simple rung hrung hc b := by
  obtain ⟨N,M,S,run,matched,R,T,W,paid,Q,_,settled⟩ :=
    purchasedWith.{u} simple hε J extra γ hγ calendar dial (@FundedPredictionSupply.Always G)
      (fun s t => FundedPredictionSupply.always s (ThroughLaunch.raging s t))
  exact ⟨N,M,S,run,matched,R,T,W,paid,Q,settled⟩

end YM.Integration.WilsonRootedPhysicalSpringReportedMS
end
