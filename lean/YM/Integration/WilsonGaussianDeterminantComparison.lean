import YM.Integration.WilsonGaussianDeterminantOrders

/-! The single physical reporting conductor meeting the high, laminate, and
incoming marked-source obligations, the packed connected word and the Gaussian determinant for every finite order, and any further original physical chart prescription on that very same H and booking. -/
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantComparison
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}

open FVA2 FVA2.CityHistory FVA2.Register FVAAlt2 FormalOPE.RG10.BlockGauge
open MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
universe u
def On {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G)
    (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
      extra γ R.kit) : Prop := ∀ {Γ : Census V} (A : NumericSchedule R.family J) (p j : ℕ) (ε : ℝ), 0<ε →
    ∀ᶠ m in (atTop : Filter ℕ), ∀ (d : LocalFormal.Datum R.family Γ), d.level=m →
      ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
      let lev := R.alloy.B.a
      let i := lev.clock.J d.level
      let j₁ := lev.clock.J (d.level+1)
      let book := paid.choose j₁ i
      let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Y := QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
        (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
      let S := lev.clock.op d.level d.period
      let β := lev.clock.hatBeta d.level
      let Q := R.kit.target j₁ i
      ∃ H : Cash book.W β book.μ S.patch.L (target J Q) book.order book.c
            (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        ManuscriptQLocalMarkedHeightRun.High (expense J Q) H J Γ ((2*g)^(J.order+1)) ∧
        WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L book.order ≤ 1+Real.log (betaF G β S.patch.L) ∧
        WilsonGaussianDeterminantOrders.Word χ H p g ε ∧ WilsonGaussianDeterminantOrders.Due χ H p j g ε

theorem of_cash (R : Run G) (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J
      (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G)) extra γ R.kit)
    (simple : G.Simple)
    (cash : WilsonGaussianDeterminantTender.On R J χ (WilsonCoherentMayerCovarianceCalendar.decal G)
      extra γ paid) : On R J χ extra γ paid := by
  intro Γ A p j ε positive
  filter_upwards [cash A, WilsonGaussianDeterminantOrders.purchased R simple p j positive] with
    m available costs d hm F η I hi
  obtain ⟨H,ren,cross,high,_,_,_,_,word,deviation,coupling,determinant⟩ := available d hm F I hi
  subst m
  exact ⟨H,ren,cross,high,deviation,costs d.cutoff d.period d.below χ H coupling word determinant⟩

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
          WilsonGaussianDeterminantTender.On R J χ (WilsonCoherentMayerCovarianceCalendar.decal G)
            extra γ booking ∧ On R J χ extra γ booking := by
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,booking,report,cash⟩ :=
    WilsonGaussianDeterminantReportedMS.purchased.{u} simple hε J χ extra γ hγ calendar dial
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,booking,report,cash,
    of_cash R J χ extra γ booking simple cash⟩

end YM.Integration.WilsonGaussianDeterminantComparison
