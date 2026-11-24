import YM.Integration.WilsonMacroscopicRichPreparedPortfolio
/-! The original independently selected RG12 word, at each actual upper site.
The original calibration of each physically tested native field is retained. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichQSiteInput
open Filter Function Finset Lattice Wilson RG Source Labels Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction QLocalOriginalQHistory
open scoped Classical Topology BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G}
    (R:Run G)(hG:G.Simple)(u:V→MS.Rake.Label B)(J:Request V)(A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)
    (o:V→Site (R.family.side (d.level + 1) d.period))(μ:ℝ)(ks:V→ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level + 1) o
local notation "clock₀" => μ-R.family.S.scale d.cutoff
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ ks
local notation "T₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks
def observation (x:TestSpace (J₀).tests)(s:(Stock.census V).Mode):Config G (R.family.side (d.level+1) d.period)→ℂ:=
  WilsonMacroscopicRichOriginalPortfolio.roster R Q (D₀) u (clock₀) ks (VariableScaling.tests (c₀) x) s

theorem sites (x:TestSpace (J₀).tests)(s:(Stock.census V).Mode)(U:Config G (R.family.side (d.level+1) d.period)):
    observation R hG u J A d Q o μ ks x s U=
      ∏i∈s.val,((VariableScaling.tests (c₀) x) i).val 0 *
        WilsonMacroscopicRichOriginalPortfolio.observation R Q (d.level+1) d.period (u i) (clock₀) (ks i) (o i) U:=by
  unfold observation WilsonMacroscopicRichOriginalPortfolio.roster
  apply Finset.prod_congr rfl
  intro i _
  rw [show ActualRunQlocalNativeTuple.root (D₀) i=o i from ActualOriginalQPointDatum.root_eq ..]
  congr 1
  exact ActualOriginalQPointDatum.reader_eq R d.period (d.level+1) o (fun a=>(J.tests a).D) (fun _=>0) i _

theorem continuousField (x:TestSpace (J₀).tests)(s:(Stock.census V).Mode):
    Continuous (observation R hG u J A d Q o μ ks x s):=by
  unfold observation;rw [←WilsonMacroscopicRichOriginalPortfolio.corrected]
  exact ActualStartupNormalizedQ.mode_continuous Q (D₀) u (clock₀) ks _ s

end YM.Integration.WilsonMacroscopicRichQSiteInput
