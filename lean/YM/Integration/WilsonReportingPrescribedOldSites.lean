import YM.Integration.QLocalOriginalQReadout

/-! One common genuine ultraviolet entrance date for every componentwise
choice of real source cell and subcell in the shared signed spatial profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldSites
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction QLocalOriginalQHistory
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)

theorem original (T : Campaign R)
    (ord : ∀ k, k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
      ∀ (b : ℕ) (fine : b≤d.level+1) (parents : V → Site (R.family.side b d.period))
        (residues : V → Site (R.family.S.toDepth fine d.period).count)
        (Q : MS.Land.Prescription B) (μ : ℝ) (ks : V → ℕ)
        (period : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val),
        d.cutoff=d.level+1 →
        let sites := fun i=>(R.family.S.toDepth fine d.period).assemble (parents i,residues i)
        ∃ first : ActualOriginalQInitialInput.start R hG u J A ord ≤ d.level,
        ∃ I : FullPreparedInputAt (ActualOriginalQInitialInput.input R hG u J A d Q sites μ ks ord first period) 0,
          Retained.NativeIntake I ∧ I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1) ∧
          I.regularPrice=0 ∧ I.forcedPrice=0 ∧ Origin R hG u J A d Q sites μ ks I := by
  filter_upwards [QLocalOriginalQState.both R hG u J A ord T] with m finance
  intro d atDate b fine parents residues Q μ ks period cut
  exact QLocalOriginalQReadout.born R hG u J A ord finance.1 d atDate Q _ μ ks period cut

end YM.Integration.WilsonReportingPrescribedOldSites
