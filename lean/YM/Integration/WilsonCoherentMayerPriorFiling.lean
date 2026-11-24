import YM.Integration.WilsonCoherentMayerPriorChronicle
import YM.Integration.WilsonLimitConstruction.FundedSignedCatalogue
import YM.Integration.RunFormalChain

/-! On the actual run the signed catalogue's full compact Wilson reading has the very same extension whose coefficients are the original finite, normalized marked Fk. Both use the submitted previous colors, forest, tag, and physical source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorFiling
open Filter Lattice Wilson RG Source Marker Precision Exterior
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction ActualOriginalQReaders
open MS.Local.Physical Extra.Histories PhysicalWilsonActionConvention
open RG3.Script.Picnic IterationFour.Vacuum MergeProof MergeProof.Accent
open WilsonReportingPrescribedOldRawForecast (raw)
open WilsonCoherentMayerPriorChronicle (reading)
open scoped Classical
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V][Nonempty V]{B:Deck G}(R:Run G)(hG:G.Simple)(u:V→MS.Rake.Label B)
    (J₀:Request V)(A₀:NumericSchedule R.family J₀)(d₀:LocalFormal.Datum R.family (Stock.census V))
    (Q:MS.Land.Prescription B)(o:V→Site (R.family.side (d₀.level+1) d₀.period))(μ:ℝ)(ks:V→ℕ)
    {J:Request V}{A:NumericSchedule R.family J}{d:LocalFormal.Datum R.family (Stock.census V)}
    {F:AnalyticInput J A d}{η:ℝ}{I:FullPreparedInputAt F η}
    {K:NumericPrices A}{caps:Handoff.OutputCapacities}
local notation "JB" => ActualOriginalQPointSetup.request R u J₀
local notation "YR" => RunFormalChain.fromRun R

theorem original (origin:QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (age:∀a:Slot u,R.family.ref a.2.size≤d₀.level+1)
    (M:SignedAnalyticOutput caps (YR) K F)(S:FundedRenderedBank.Bank I (FundedSignedCostModels.catalogue M))
    (t:IndependentTests J.tests):
    let h:=ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
    let b:=VariableScaling.tests (fun _=>(h:ℂ)) (testInclusion J.tests t)
    let actual:=reading R d.cutoff d.period d.level (S.output.output.leaf b).density
    let old:=reading R d.cutoff d.period d.level (S.output.residual.leaf b).density
    let f:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    ∃t₀:IndependentTests (JB).tests,HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
    ∃live:d.level≤d₀.level+1,
      HEq actual (reading R d₀.cutoff d₀.period d.level (gust R.family.path d₀.cutoff d₀.period (d₀.level+1)
        (raw R hG u J₀ d₀ Q o μ ks t₀) d.level live)) ∧
      (∀U,(old U).part (Stock.census V).quiet=1 ∧ massLog (actual U)=M.model.read b f U+massLog (old U)) ∧
      ∀ v:fieldDir G (R.family.side d.level d.period) 1,
        let U:=represent (f • v)
        massLog (actual U)-massLog (old U)=M.prescribed.extension b f v ∧
        ∀k:ℕ,k≤J.order → ((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun z:ℝ=>M.prescribed.extension b z v) 0 (fun _=>1)=
          Order.observe (Stock.census V) J.order (Order.logMarked (Bulk.Fk (d.kernel (YR)) d.forest d.tag
            (F.colors b) v J.order)) k:=by
  intro h b actual old f
  obtain ⟨t₀,test,live,arrived,paid⟩:=WilsonCoherentMayerPriorChronicle.original R hG u J₀ A₀ d₀ Q o μ ks
    origin age (FundedSignedCostModels.catalogue M) S t
  refine ⟨t₀,test,live,arrived,paid,?_⟩
  intro v U
  have pos:0<f:=Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt d.below)
  refine ⟨?_,fun k hk=>M.prescribed.coefficients b v k hk⟩
  rw [M.prescribed.value b f pos.ne' v]
  exact sub_eq_iff_eq_add.mpr (paid U).2

end YM.Integration.WilsonCoherentMayerPriorFiling
