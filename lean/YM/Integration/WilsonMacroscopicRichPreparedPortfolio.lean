import YM.Integration.WilsonMacroscopicRichOriginalPortfolio
import YM.Integration.WilsonReportingPrescribedOldSites

/-! The true input of the same enrolled marked RG12 preparation, with its native calibration,
denominator, and all independently specified sites, at each earlier positive Wilson field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichPreparedPortfolio
open Filter Function Finset Lattice Wilson RG Source Labels Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction QLocalOriginalQHistory
open scoped Classical Topology BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}
    (R:Run G)(hG:G.Simple)(u:V→MS.Rake.Label B)(J:Request V)(A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)
    (o:V→Site (R.family.side (d.level + 1) d.period))(μ:ℝ)(ks:V→ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level + 1) o
local notation "clock₀" => μ-R.family.S.scale d.cutoff
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ ks
local notation "T₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks
theorem enrolled {F:AnalyticInput (ActualOriginalQPointSetup.request R u J) (ActualOriginalQInitialInput.schedule R hG u J A) d}
    {η:ℝ}(I:FullPreparedInputAt F η)(authority:QLocalOriginalQHistory.Origin R hG u J A d Q o μ ks I) (x:TestSpace (J₀).tests):
    (I.input.leaf x).density=((T₀).leaf x).density:=by
  obtain ⟨_,_,_,source,state,paid⟩:=authority
  exact (state.current x).trans ((gust_base R.family.path d.cutoff d.period (d.level + 1) (source x)).trans
    (eq_of_heq (paid x x HEq.rfl)))

theorem measured {F:AnalyticInput (ActualOriginalQPointSetup.request R u J) (ActualOriginalQInitialInput.schedule R hG u J A) d}
    {η:ℝ}(I:FullPreparedInputAt F η)(authority:QLocalOriginalQHistory.Origin R hG u J A d Q o μ ks I)
    (age:∀a:ActualOriginalQReaders.Slot u,R.family.ref a.2.size ≤ d.level + 1)
    (x:TestSpace (J₀).tests){j:ℕ}(live:j ≤ d.level + 1)(s:(Stock.census V).Mode)
    (U:Config G (R.family.side j d.period)):
    ((((R.family.path.rep d.cutoff d.period j).eval U)⁻¹) • gust R.family.path d.cutoff d.period
      (d.level + 1) (I.input.leaf x).density j live U).part s =
      actualTransport R.family (N:=d.cutoff)
        (WilsonMacroscopicRichOriginalPortfolio.roster R Q (D₀) u (clock₀) ks (VariableScaling.tests (c₀) x) s) live U:=by
  have upper:=Nat.succ_le_of_lt d.below
  have H:=WilsonReportingPrescribedOldMicroscopic.original R Q (D₀) u (clock₀) ks hG upper age
    (VariableScaling.tests (c₀) x) live s U
  rw [WilsonMacroscopicRichOriginalPortfolio.corrected] at H
  rw [enrolled R hG u J A d Q o μ ks I authority x,
    funext (ActualOriginalQInitialPreparation.input_density R hG u J A d Q o μ ks x)]
  exact H

end YM.Integration.WilsonMacroscopicRichPreparedPortfolio
