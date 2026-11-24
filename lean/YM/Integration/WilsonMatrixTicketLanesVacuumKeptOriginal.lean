import YM.Integration.WilsonMatrixTicketLanesVacuumOriginal
import YM.Integration.WilsonMatrixTicketLanesVacuumKeptWave

/-! The independent series, the nonzero physical Ward test and its complete
earlier hard numerator on one original reporting layout. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesVacuumKeptOriginal
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn WilsonInvariantActionPairCovariance
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonMatrixOriginalLogarithmicRate WilsonMatrixOriginalReportingMargin
open WilsonCoeffUV.Bank WilsonMatrixTicketLanesVacuumWard
open MS MS.Land RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2 WilsonLimitConstruction.FundedCompanySelection
open PhysicalNext.Repeat.Legato OPE.Therm Table FVA2 FVA2.Register Pert.Asymptotics
open MS MS.Land RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2 WilsonLimitConstruction.FundedCompanySelection
open WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing WilsonMatrixTicketLanesRegisteredHearing
open WilsonMatrixTicketLanesVacuumPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)

def Filed (simple:G.Simple):Prop:=
  ∀(f:Extraction.Order)(S:Table R.family.book)(F:Final R.family f S)(L:Layout F),
    ∀B:ℕ,17≤B→L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B→
    ∀(a b:ℝ→R.family.label 4)(φ:Test 2)(χ:ℂ→L[ℝ]ℝ)(n:ℕ),
    ∀ᶠr in trail,∀hr:0<r,∃k,L.level r=k+1 ∧
    ∀ᶠz:ℕ×ℕ in L.lens,∃j:k+1<z.1,∃birth:R.family.ref 4 ≤ k+1,
    let labels:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let live:k<z.1:=by omega
    ∀select:(Fin 2→Site (R.family.side z.1 z.2))→ℕ,
    let w:=fun x=>score R j (hard R j (select x))
    signed R .previousCovariance live birth labels (dilate hr φ) χ w+
      signed R .previousCumulant live birth labels (dilate hr φ) χ w=
      WilsonMatrixTicketLanesRegisteredHearing.panel R live birth labels (dilate hr φ) χ (fun x=>WilsonMatrixTicketLanesVacuumKeptWave.lower R j n (select x)) ∧
    signed R .all live birth labels (dilate hr φ) χ w=
      WilsonMatrixTicketLanesRegisteredHearing.panel R live birth labels (dilate hr φ) χ (fun x=>WilsonMatrixTicketLanesVacuumKeptWave.all R j n (select x))

theorem hearing (simple:G.Simple) (paid:WilsonOldActionForecast.Eligible R.kit):Filed R simple:=by
  obtain ⟨marker,checkout⟩:=WilsonOldActionForecast.issued R paid
  intro f S F L B wide level a b φ χ n
  obtain ⟨m,ok⟩:=eventually_atTop.mp (WilsonMatrixTicketLanesVacuumKeptWave.purchased R simple marker checkout n)
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  filter_upwards [grow.eventually_ge_atTop (max m (R.family.ref 4)+1)] with r size hr
  let k:=L.level r-1
  have whereAt:L.level r=k+1:=by dsimp [k];omega
  have born:R.family.ref 4 ≤ k+1:=by omega
  have future:∀ᶠz:ℕ×ℕ in f.fuse,L.level r<z.1:=by
    change ∀ᶠ_:ℕ in atTop,∀ᶠi:ℕ in atTop,L.level r<f.mesh i
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop _
  refine ⟨k,whereAt,?_⟩
  filter_upwards [future.filter_mono L.certified] with z later
  have j:k+1<z.1:=by omega
  refine ⟨j,born,?_⟩
  intro labels live select
  exact ok k (by omega) z.1 z.2 j born labels (dilate hr φ) χ select

theorem original (simple:G.Simple) {ε:ℝ} (ep:0<ε) (v:ℕ→Gear G→ℝ) (calendar:XSpace.Run) (dial:Bool):
    ∃(N:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S:Prescription (Press.portDeck G)),N.run=calendar ∧ Main.Match N simple M S dial ∧
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T)(Q:Prescription (Press.portDeck G)),
      FundedOriginalProperties.{u} simple ε W ∧ NativeFVAPlateau.Correlations R ∧
      Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧
      WilsonMatrixTicketLanesVacuumOriginal.Measured R N simple Q ∧ Filed R simple:=by
  have fees:WilsonFundedWindowMenu.AllPrices (@FundedPredictionSupply.Always G):=fun s _=>
    WilsonFundedWindowMenu.from_guard (WilsonFundedWindowCompany.of_prepaid (FundedPredictionSupply.always s _))
  obtain ⟨N,M,S,calendar₀,matched,V,T,W,Q,_,early,funded,correlations,team,taylor,story,physical⟩:=
    WilsonMatrixTicketLanesVacuumElection.purchasedWith.{u} simple ep v calendar dial (@FundedPredictionSupply.Always G) fees
  exact ⟨N,M,S,calendar₀,matched,V,T,W,Q,funded,correlations,team,taylor,story,
    WilsonMatrixTicketLanesVacuumOriginal.on_run V N simple W funded v early Q physical,
    hearing V simple early.2.2.2.2.1⟩

end YM.Integration.WilsonMatrixTicketLanesVacuumKeptOriginal
