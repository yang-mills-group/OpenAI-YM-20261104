import YM.Integration.WilsonGaussianDeterminantQuarticMS
import YM.Integration.WilsonGaussianMeasuredFourthUniform
import YM.Integration.WilsonRootedPhysicalSpringUnitMS

/-! A single original campaign checks both scalar tests and the independent MS report.
Each measured four-direction price contains only the requested tolerance and coupling
power, with the original radius and changed-site attenuation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantUniformMS
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
open ManuscriptQLocalCofinalAffineFields (schedule)
universe u
def Common {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (simple : G.Simple)
    (R : Run G) (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (Q : Prescription (Press.portDeck G))
    (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
    (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (paid : QLocalRequestedSectorCalendar.Paid J
      (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
      extra γ R.kit) : Prop :=
  ∀ {Γ : Census V} (A : NumericSchedule R.family J) (through power : ℕ) (f : Extraction.Order)
    (rung : ℕ) (hrung : 0<rung) (c : ℝ) (hc : 1<c) (p j : ℕ) (ε : ℝ), 0<ε →
    ∀ᶠ b : ℕ in atTop,
      WilsonRootedPhysicalSpringAffineRows.After R affine (max (max through 4) power) b ∧
      WilsonRootedPhysicalSpringReportedMS.Filed R M Q f simple rung hrung hc b ∧
      ∀ (d : LocalFormal.Datum R.family Γ), b ≤ d.level →
        WilsonRootedPhysicalSpringUnitMS.Fields R d table (max through 4) power ∧
        WilsonGaussianMeasuredFourthUniform.At R d table power ε ∧
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

theorem common {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (simple : G.Simple)
    (R : Run G) (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (Q : Prescription (Press.portDeck G))
    (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
    (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
    (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
    (paid : QLocalRequestedSectorCalendar.Paid J
      (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
      extra γ R.kit)
    (previous : WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders paid)
    (fields : WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table) :
    Common simple R J χ extra γ M Q affine table paid := by
  intro Γ A through power f rung hrung c hc p j ε hε
  filter_upwards [previous (Γ:=Γ) A through power f rung hrung c hc p j ε hε,
    fields (max through 4) power f rung hrung c hc,WilsonGaussianMeasuredFourthUniform.eventually R
      simple table orders.1 power hε] with b prior priced uniform
  refine ⟨prior.1,prior.2.1,?_⟩
  intro d hd
  exact ⟨priced.2.2 d hd,uniform d hd,(prior.2.2 d hd).2.2.2⟩

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
        (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        Common simple R J χ extra γ M Q affine table booking := by
  let δ := WilsonCoherentMayerCovarianceCalendar.decal G
  let joint := WilsonGaussianDeterminantTender.joined G J χ δ
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,report,fields,unit⟩ :=
    WilsonRootedPhysicalSpringUnitMS.purchasedWith.{u} simple hε J extra γ hγ calendar dial
      (@QLocalRequestedSectorCalendar.Paid G V J joint extra γ)
      (fun s t => QLocalRequestedSectorCalendar.prepaid J joint extra γ simple hγ s (ThroughLaunch.raging s t))
  have prior : WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking :=
    WilsonGaussianDeterminantQuarticMS.common simple R J χ extra γ M Q affine orders booking fields
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,report,fields,unit,prior,
    common simple R J χ extra γ M Q affine orders table booking prior unit⟩

end YM.Integration.WilsonGaussianDeterminantUniformMS
