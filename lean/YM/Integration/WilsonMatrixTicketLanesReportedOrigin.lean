import YM.Integration.WilsonOriginalHighRun
import YM.Integration.WilsonMatrixTicketLanesReportedReturn
import YM.Integration.WilsonMatrixTicketLanesReportedSeed

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedOrigin
open Filter RG RG.Supply Spec Extraction OPE OPE.RigE MergeProof MergeProof.Accent
open Next.Extract Dash PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MS MS.Land FVA2 FVA2.Register RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2
open RG12 RG17 Table SharpGram.Lenses Pier.Lair OPE.Orbits Climb Ward PhysMS Trace.Pilot SharpGram
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonOriginalMarkedExistence
open WilsonMatrixTicketLanesReportedPrepaid
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge}

/-- The whole finite joint fields and forecasts use this original run at every
later cutoff and every period, with their genuine measured field representatives. -/
def Fields (R : Run G) : Prop :=
  ∀ {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)
    (L : RG17.Layout F) (J : ℝ → PhysMS.tower S),PhysMS.Leading F J →
    ∀ {K : (Bel R.family.book).Hierarchy},
    (∀ d : ℕ, ∀ᶠ r in trail, AlignO F.sector F.room.kernel.spin K d (J r d)) →
    ∀ {U : Filter (ℕ×ℕ)} (B : Mantle F U),Services R.family f S → Pegs B L →
      (∀ᶠ r in trail,R.family.S.a (L.level r) ≤ r ∧
        r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2) →
      ∀ {n : ℕ} (d : Fin n → ℕ),∃ e : Fin n → ℕ,∀ q cap (ε : ℝ),0 < ε → ∀ᶠ r in trail,
        ∀ x : ∀i,RG17.Free R.family (d i),∃ w : ∀i,R.family.label (d i),
          (∀i,master L (d i) r (w i) = J r (d i) (x i) ∧ mass R.family (d i) (L.shift (d i) r (w i)) ≤
            R.family.path.levels.clock.hatBeta (L.level r)^(e i)*‖x i‖) ∧
          WilsonMatrixTicketLanesReportedReturn.Compared R F L r d w x (q+2*((∑ i,e i)+1)) q cap ε

/-- The separately elected MS prescription and its finite-volume skyread use the
original warehouse on this run and its own projected strong basis. -/
def Scheme (R : Run G) (simple : G.Simple) : Prop :=
  ∀ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial : Bool),
    ∃ scheme Q : Prescription (Press.portDeck G), Main.Match N simple M scheme dial ∧ Q.team=scheme.team ∧
      TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧ ∀ f : Extraction.Order,
        ∃ (g : Extraction.Order) (A : Table R.family.book) (L : ℕ → Table R.family.book)
          (B : Bin A) (Z : ∀ d, ℕ → CoordMap R.family d) (tr : Presentation R.family)
          (S : Table R.family.book) (E : DiffPlan S),
          Projected tr (f.refine g) B Z ∧ Base R.family (f.refine g) A L B S E ∧
          Nonempty (Seed R.family (f.refine g) S) ∧ (∀ d,StrongBin R.family B (f.refine g) d) ∧
          (∀ d,UVExt.Slots.StrongBin R.family B (f.refine g) d) ∧ ∀ (J : ℕ) (hJ : 0<J) (c : ℝ) (hc : 1<c),
            WilsonMatrixTicketLanesReportedRun.Statement R M Q (f.refine g) simple J hJ hc

/-- Other genuine original expenses are elected before the same
physical run and its original correlation and existence witnesses. -/
theorem alongside (simple : G.Simple) {ε : ℝ} (positive : 0 < ε)
    (extra : Prediction G) (funded : FundedPredictionSupply.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),extra R.kit ∧ Paid G R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧ Charged R ∧ Fields R ∧ Scheme R simple := by
  obtain ⟨R,T,W,accepted,_,_,_,correlations,properties,charged⟩ := WilsonOriginalHighRun.selectedWith.{u} simple positive
    (@FundedPredictionSupply.Both G (@extra) (@Paid G))
    (fun s t=>FundedPredictionSupply.both (funded s t) (allPrices (G:=G) s t))
  refine ⟨R,T,W,accepted.1,accepted.2,correlations,properties,charged,?_,WilsonMatrixTicketLanesReportedSeed.original R simple⟩
  intro f S F L J lead K aligned U B E pegs near n d
  exact WilsonMatrixTicketLanesReportedReturn.original R F L J lead aligned B E pegs near simple accepted.2 d

/-- The single actual funded Yang–Mills selection and its independent MS prescription,
together with the proved quantitative nonlinear one-block profile on the same run. -/
theorem original (simple : G.Simple) {ε : ℝ} (positive : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),Paid G R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} simple ε W ∧ Charged R ∧ Fields R ∧ Scheme R simple := by
  obtain ⟨R,T,W,_,both⟩ := alongside.{u} simple positive (@FundedPredictionSupply.Always G)
    (fun s t=>FundedPredictionSupply.always s (ThroughLaunch.raging s t))
  exact ⟨R,T,W,both⟩

end YM.Integration.WilsonMatrixTicketLanesReportedOrigin
