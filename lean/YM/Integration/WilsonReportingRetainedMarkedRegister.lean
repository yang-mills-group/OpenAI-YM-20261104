import YM.Integration.WilsonReportingRetainedMarkedPortfolio
import YM.Integration.WilsonRootedSubmittedTail

/-! The signed physical angular loss on every requested retained ordinary
and compulsory occurrence issued for the original incoming prepared field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingRetainedMarkedRegister
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi LocalLTE
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE
open ManuscriptQLocalMarkedHeightRun WilsonReportingRetainedMarkedPortfolio
open WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open Merge Tree RG16 OPE.Therm WilsonPositionSeparatedProfileReportingPrimary
open WilsonReportingMolecularMaskRegion MeasureTheory
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    {J : Request V} (R : Run G) (A : NumericSchedule R.family J) (extra : Stage → ℕ → ℝ)
    (γ : ℝ) (paid : QLocalRequestedSectorCalendar.Paid J (acquisition G J) extra γ R.kit)

/-- The conductor, its renewed and crossed original finance, and the
integrated signed rooted matrices share the identical fine incoming
carrier and all the originally submitted regular and forced occurrences. -/
theorem original (simple : G.Simple) (angle : posted R) (p : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family Γ), d.level = m+1 →
    ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
    let lev := R.alloy.B.a
    let i := lev.clock.J d.level
    let j := lev.clock.J (d.level+1)
    let book := paid.choose j i
    let Q := R.kit.target j i
    let β := lev.clock.hatBeta d.level
    let L := (lev.clock.op d.level d.period).patch.L
    let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level
    let gf := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let ν := scene R.family.path d.cutoff d.period d.level
    ∃ H : WilsonRootedSubmittedTail.CashAt I book,
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      Crossed J γ R A d book H (I.inherited + ManuscriptQLocalVacuumRadius.bill F.vacuum.packets gf 1) ∧
      High (expense J Q) H J Γ ((2*gf)^(J.order+1)) ∧
      ∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
      let M := (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base x E K).terms
      let ℓ := ManuscriptQLocalMarkedHeightRun.length J
      ∀ (φ : Fan.Stars H (fun i => (M i).M) → Config G (R.family.side d.level d.period) → ℂ)
        {C : ℝ}, 0 ≤ C →
      (∀ z, ¬ Height.tiredN H ℓ z.1 →
        ∀ U ∉ House.chilly (G:=G) (cover (Captain.reachability z.1)) (angularCut β), ‖φ z U‖ ≤ C) →
      Ac.Hit (fun z : Fan.Stars H (fun i => (M i).M) => Captain.reachability z.1) (radiusB β)
        (fun z => if ¬ Height.tiredN H ℓ z.1 then
          Poly.price F.inputRadii (signed H Chi.canonical M (angularCut β) ν φ z) else 0)
        ((expense J Q).earn-1) ((C*(ε*g^p))*(((betaF G β L)^2)^Fintype.card V)) := by
  classical
  filter_upwards [WilsonReportingRetainedMarkedPortfolio.original Γ J R simple angle p ep,
    (tendsto_add_atTop_nat 1).eventually (ManuscriptQLocalMarkedHeightRun.issued (Γ:=Γ) R A extra γ paid simple)]
    with m purchased source d hd
  rcases d with ⟨N,per,k,live,forest,tag,colors,field⟩
  change k = m+1 at hd
  subst k
  intro F η I input
  obtain ⟨H,renewed,crossed,high,submitted,capital⟩ := source _ rfl F I input
  refine ⟨H,renewed,crossed,high,?_⟩
  intro base x E K
  dsimp only
  intro φ C C0 rough
  exact purchased N live per H _ high _ _ F.fineRoots F.inputRadii (rosterBill I) F.input_radius_positive
    (submitted base x E K) capital φ C0 rough

end YM.Integration.WilsonReportingRetainedMarkedRegister
