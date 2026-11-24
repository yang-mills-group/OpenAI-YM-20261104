import YM.Integration.WilsonGaussianDeterminantComparison
import YM.Integration.WilsonGaussianMeasuredFourthTest
import YM.Integration.WilsonRootedPhysicalSpringStoredMS

/-! A single original existence run pays the MS prescription, the all-order measured
affine scalar and its explicit quartic, the normalized determinant and the signed
finite integral. Their numerical statements hold on every sufficiently late physical
datum after the independent orders, requested accuracy and probes have been fixed. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantQuarticMS
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
private theorem price {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
    (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit) (through power : ℕ)
    (height : 4 ≤ R.alloy.B.a.clock.J (d.level+1))
    (fields : WilsonRootedPhysicalSpringStoredMS.Fields R d orders (max through 4) power) :
    WilsonGaussianMeasuredFourthTest.Tested R d orders.1 power := by
  intro k q t z U Y Z o N r s κ c ρ W geo C K a b c e
  have bounds := fields k q t z U Y Z o
  exact WilsonGaussianMeasuredFourthTest.tested R d orders.1 height k q t z U Y Z o
    (le_max_right through 4) bounds.2.2.1 bounds.2.2.2.1 a b c e

def Common {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (simple : G.Simple)
    (R : Run G) (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (Q : Prescription (Press.portDeck G))
    (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
    (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
    (paid : QLocalRequestedSectorCalendar.Paid J
      (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
      extra γ R.kit) : Prop :=
  ∀ {Γ : Census V} (A : NumericSchedule R.family J) (through power : ℕ) (f : Extraction.Order)
    (rung : ℕ) (hrung : 0<rung) (c : ℝ) (hc : 1<c) (p j : ℕ) (ε : ℝ), 0<ε →
    ∀ᶠ b : ℕ in atTop,
      WilsonRootedPhysicalSpringAffineRows.After R affine (max (max through 4) power) b ∧
      WilsonRootedPhysicalSpringReportedMS.Filed R M Q f simple rung hrung hc b ∧
      ∀ (d : LocalFormal.Datum R.family Γ), b ≤ d.level →
        WilsonRootedPhysicalSpringStoredMS.Fields R d orders (max through 4) power ∧
        WilsonGaussianMeasuredFourth.At R d orders.1 ∧
        WilsonGaussianMeasuredFourthTest.Tested R d orders.1 power ∧
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
    (paid : QLocalRequestedSectorCalendar.Paid J
      (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
      extra γ R.kit)
    (fields : WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders) :
    Common simple R J χ extra γ M Q affine orders paid := by
  let δ := WilsonCoherentMayerCovarianceCalendar.decal G
  have cash : WilsonGaussianDeterminantComparison.On R J χ extra γ paid :=
    WilsonGaussianDeterminantComparison.of_cash R J χ extra γ paid simple
    (WilsonGaussianDeterminantTender.opens R J χ δ extra γ paid simple)
  intro Γ A through power f rung hrung c hc p j ε hε
  obtain ⟨threshold,above⟩ := eventually_atTop.mp (cash (Γ:=Γ) A p j ε hε)
  have late := (R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 4
  obtain ⟨degree,high⟩ := eventually_atTop.mp late
  filter_upwards [fields (max through 4) power f rung hrung c hc,
    WilsonGaussianMeasuredFourth.eventually R orders.1,eventually_ge_atTop threshold,eventually_ge_atTop degree]
    with b offered fourth hb hdg
  refine ⟨offered.1,offered.2.1,?_⟩
  intro d hd
  have stored := offered.2.2 d hd
  exact ⟨stored,fourth d hd,price R d orders through power (high d.level (hdg.trans hd)) stored,
    above d.level (hb.trans hd) d rfl⟩

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        Common simple R J χ extra γ M Q affine orders booking := by
  let δ := WilsonCoherentMayerCovarianceCalendar.decal G
  let joint := WilsonGaussianDeterminantTender.joined G J χ δ
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,booking,report,fields⟩ :=
    WilsonRootedPhysicalSpringStoredMS.purchasedWith.{u} simple hε J extra γ hγ calendar dial
      (@QLocalRequestedSectorCalendar.Paid G V J joint extra γ)
      (fun s t => QLocalRequestedSectorCalendar.prepaid J joint extra γ simple hγ s (ThroughLaunch.raging s t))
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,booking,report,fields,
    common simple R J χ extra γ M Q affine orders booking fields⟩

end YM.Integration.WilsonGaussianDeterminantQuarticMS
