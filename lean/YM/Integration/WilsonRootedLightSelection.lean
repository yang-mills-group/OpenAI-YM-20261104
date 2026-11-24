import YM.Integration.WilsonOriginalHighLightCalendar
import YM.Integration.WilsonRootedSubmittedTail
import YM.Integration.WilsonOriginalLogLight

/-! One kinetic path supplies the complete original density and its signed
high and low rooted bounds at the elected physical calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedLightSelection
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
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
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    {J : Request V} (R : Run G) (A : NumericSchedule R.family J) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit)

def Admitted : Prop :=
  ∀ᶠ m in (atTop : Filter ℕ), ∀ (d : LocalFormal.Datum R.family Γ), d.level=m →
    ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
    let lev := R.alloy.B.a
    let i := lev.clock.J d.level
    let j := lev.clock.J (d.level+1)
    let book := paid.choose j i
    let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let inlet := QLocalInheritedPhysicalInlet.rep I
    let old := ManuscriptQLocalVacuumFamily.source inlet F.layers g 1
    let carry := ManuscriptQLocalVacuumFamily.carry inlet F.layers g 1
      (QLocalInheritedPhysicalInlet.carried I I.prepared.remainder)
    let S := lev.clock.op d.level d.period
    let Q := R.kit.target j i
    ∃ H : WilsonRootedSubmittedTail.CashAt I book,
      Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
      Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
      WilsonRootedSubmittedTail.Submitted I H ((2*g)^(J.order+1)) ∧
      (∀ M ≤ S.patch.J, ∃ a : ℝ, Laminate.Known H (toll J) a 1 (Height.asset (expense J Q))
        J.outputFieldOrder J.outputDistanceOrder M) ∧
      (∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
        QLocalMarkedSourceCalendar.Priced (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H base x E K) ∧
      ∀ (x : TestSpace J.tests) U, (I.input.leaf x).density U=(Real.exp (-I.calibration.amount U) : ℂ) •
        (Poly.pass (F.packets.read x g U)*((QLocalInheritedRegularSlots.marked old carry).leaf x).density U)

theorem onPaid (hG : G.Simple) : Admitted (Γ:=Γ) R A extra γ paid := by
  unfold Admitted
  filter_upwards [WilsonRootedJointCalendar.issued (Γ:=Γ) R A extra γ paid hG] with m issued d hm F η I hi
  obtain ⟨H,ren,cross,h,low,phases,_,reserve⟩ := issued d hm F I hi
  exact ⟨H,ren,cross,WilsonRootedSubmittedTail.accepted I H h reserve,low,phases,
    ManuscriptQLocalMarkedHeightRun.material R A d F I hi⟩

theorem purchased (slow : ℝ → ℝ) (movable : Stationary.Movable slow) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit),
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin slow ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R ∧
      ∀ (Γ : Marker.Census V) (A : NumericSchedule R.family J), Admitted (Γ:=Γ) R A extra γ paid := by
  obtain ⟨R,T,W,paid,salary,light,marks,checkout,correlations,funded,charged⟩ :=
    WilsonOriginalHighLightCalendar.selected.{u} slow movable hG hε J
      (WilsonRootedJointCalendar.scheme G J) extra γ hγ
  exact ⟨R,T,W,paid,salary,light,marks,checkout,correlations,funded,charged,
    fun Γ A => onPaid (Γ:=Γ) R A extra γ paid hG⟩

theorem logarithmic (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit),
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R ∧
      ∀ (Γ : Marker.Census V) (A : NumericSchedule R.family J), Admitted (Γ:=Γ) R A extra γ paid :=
  purchased Real.log WilsonOriginalLogLight.movable hG hε J extra γ hγ

end YM.Integration.WilsonRootedLightSelection
end
