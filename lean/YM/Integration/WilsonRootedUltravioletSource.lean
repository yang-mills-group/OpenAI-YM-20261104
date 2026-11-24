import YM.Integration.WilsonRootedUltravioletElection
import YM.Integration.WilsonPreparedPointSource

/-! The actual original point source enters the high-sector calculation on the
selected campaign. The ultraviolet witness carries its full signed startup gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedUltravioletSource
open Filter Function Finset Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE RGLocalTaylor
open Org GapsLocal.Renew ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonOriginalMarkedExistence
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V)
    (A : NumericSchedule R.family J) (T : Campaign R)
    (stage : ∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power)
    (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "paid₀" => WilsonRootedUltravioletElection.point R u J extra γ paid

/-- The prepared source and observed integrated response share a physical ultraviolet
cut, the complete input density and a cash admitting the untouched signed fields. -/
def AtCut (q : ℕ) (τ : ℝ) : Prop :=
  ∀ᶠ m in (atTop : Filter ℕ), ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
    ∀ (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (orders : V → ℕ)
      (per : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val), d.cutoff=d.level+1 →
    ∃ start : ActualOriginalQInitialInput.start R hG u J A stage ≤ d.level,
    let F := ActualOriginalQInitialInput.input R hG u J A d Q o μ orders stage start per
    ∃ I : FullPreparedInputAt F 0, Retained.NativeIntake I ∧
      I.carrier.rep = R.family.path.rep d.cutoff d.period (d.level+1) ∧
      HEq I.input (ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders) ∧
      I.regularPrice = 0 ∧ I.forcedPrice = 0 ∧
      let lev := R.alloy.B.a
      let book := (paid₀).choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let old := ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
      let carry := ManuscriptQLocalVacuumFamily.carry (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
        (QLocalInheritedPhysicalInlet.carried I I.prepared.remainder)
      ∃ H : WilsonRootedSubmittedTail.CashAt I book,
        WilsonRootedSubmittedTail.Submitted I H ((2*g)^((J₀).order+1)) ∧
        WilsonRootedObservedRate.Observed I H (τ*g^q) ∧
        (∀ M ≤ (lev.clock.op d.level d.period).patch.J, ∃ a : ℝ, Laminate.Known H (toll (J₀)) a 1
          (Height.asset (expense (J₀) (R.kit.target (lev.clock.J (d.level+1)) (lev.clock.J d.level))))
          (J₀).outputFieldOrder (J₀).outputDistanceOrder M) ∧
        (∀ (base x : IndependentTests (J₀).tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
          QLocalMarkedSourceCalendar.Priced (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H base x E K) ∧
        ∀ (x : TestSpace (J₀).tests) U, (I.input.leaf x).density U = (Real.exp (-I.calibration.amount U) : ℂ) •
          (Poly.pass (F.packets.read x g U) * ((QLocalInheritedRegularSlots.marked old carry).leaf x).density U)

include T in
theorem physical (q : ℕ) (hq : q ≤ J.order) {τ : ℝ} (ht : 0 < τ) :
    AtCut R hG u J A stage extra γ paid q τ := by
  filter_upwards [ActualOriginalQInitialAtTop.eventually_prepared R hG u J A T stage,
    WilsonRootedLightSelection.onPaid (Γ:=Stock.census V) R (A₀) extra γ (paid₀) hG,
    WilsonRootedObservedRate.power R hG J.order q hq ht] with m prep grant small d hd Q o μ orders per top
  obtain ⟨start,I,inlet,carrier,input,reg,forced⟩ := prep d hd Q o μ orders per top
  obtain ⟨H,_,_,submitted,known,phases,material⟩ := grant d hd _ I inlet
  subst m
  exact ⟨start,I,inlet,carrier,input,reg,forced,H,submitted,
    WilsonRootedObservedRate.original I H submitted (small d.cutoff d.period d.below),known,phases,material⟩

/-- Run, orbit purchase and log kinetic path precede every actual source label
and every test. The first cutoff supplies the original field and the measured tail. -/
theorem selected (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit)
        (stage : ∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power),
      R2I.Funded ((Mallow.orbitD G).paired (Charity.RG12.garment10 G)) R T ∧
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R ∧
      ∀ {B : MS.Local.Physical.Deck G} (u : V → MS.Rake.Label B) (A : NumericSchedule R.family J),
        ∀ q ≤ J.order, ∀ τ > 0, AtCut R hG u J A stage extra γ paid q τ := by
  obtain ⟨R,T,W,paid,stage,spring,salary,light,marks,bill,corr,original,charged⟩ :=
    WilsonRootedUltravioletElection.selected.{u} hG hε J extra γ hγ
  exact ⟨R,T,W,paid,stage,spring,salary,light,marks,bill,corr,original,charged,
    fun u A q hq τ ht => physical R hG u J A T stage extra γ paid q hq ht⟩

end YM.Integration.WilsonRootedUltravioletSource
end
