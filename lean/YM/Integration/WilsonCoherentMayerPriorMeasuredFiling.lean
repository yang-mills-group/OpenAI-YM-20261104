import YM.Integration.WilsonCoherentMayerPriorSampler

/-! The entire arrived original signed logarithm with the old cofactor removed, at positive coupling, versus its independently prescribed genuine finite Fk. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorMeasuredFiling
open Filter Lattice Wilson RG Source Marker Precision Exterior
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction ActualOriginalQReaders
open MS.Local.Physical Extra.Histories PhysicalWilsonActionConvention
open RG3.Script.Picnic IterationFour.Vacuum MergeProof MergeProof.Accent
open WilsonReportingPrescribedOldRawForecast (raw)
open WilsonCoherentMayerPriorChronicle (reading)
open WilsonMeasuredPathTaylor WilsonCoherentMayerPriorAtom NativePaidPacketColors
open Comparison.Density.RenderM Next.SectorChange.Flat
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V][Nonempty V]{B:Deck G}(R:Run G)(hG:G.Simple)(u:V→MS.Rake.Label B)
    (J₀:Request V)(A₀:NumericSchedule R.family J₀)(d₀:LocalFormal.Datum R.family (Stock.census V))
    (Q:MS.Land.Prescription B)(o:V→Site (R.family.side (d₀.level+1) d₀.period))(μ:ℝ)(ks:V→ℕ)
    {J:Request V}{A:NumericSchedule R.family J}{d:LocalFormal.Datum R.family (Stock.census V)}
    {F:AnalyticInput J A d}{η:ℝ}{I:FullPreparedInputAt F η}
    {K:NumericPrices A}{caps:Handoff.OutputCapacities}
local notation "JB" => ActualOriginalQPointSetup.request R u J₀
local notation "YR" => RunFormalChain.fromRun R

theorem measured (origin:QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (age:∀a:Slot u,R.family.ref a.2.size≤d₀.level+1)
    (M:SignedAnalyticOutput caps (YR) K F)(S:FundedRenderedBank.Bank I (FundedSignedCostModels.catalogue M))
    (t:IndependentTests J.tests)(s:(Stock.census V).Mode)(hs:s.val.Nonempty)
    (a:Directions G (R.family.side d.level d.period)){L:ℝ}(hL:0≤L)(legs:∀e,speed a e≤L)
    (q ord:ℕ)(enough:q+M.model.powerCap≤ord)(hord:ord≤J.order):
    let h:=ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
    let b:=VariableScaling.tests (fun _=>(h:ℂ)) (testInclusion J.tests t)
    let actual:=reading R d.cutoff d.period d.level (S.output.output.leaf b).density
    let old:=reading R d.cutoff d.period d.level (S.output.residual.leaf b).density
    let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let U:=represent (g•labels a)
    2*L*|g|/A.outputWidth d.level≤1 →
    (old U).part (Stock.census V).quiet=1 ∧
      Poly.toll (fun v=>F.outputRadii v/F.kernelCosts v/‖(h:ℂ)‖) s*
      ‖(massLog (actual U)-massLog (old U)).part s-
        ∑k∈Finset.range (ord+1),(g:ℂ)^k*
          (Order.observe (Stock.census V) J.order (Order.logMarked
            (Bulk.Fk (d.kernel (YR)) d.forest d.tag (F.colors b) (labels a) J.order)) k).part s‖≤
      ((powers M.model).card:ℝ)*(fee (A.outputWidth d.level) L q g*K.geometry d.level):=by
  intro h b actual old g U small
  obtain ⟨t₀,_,live,_,law,_⟩:=WilsonCoherentMayerPriorFiling.original R hG u J₀ A₀ d₀ Q o μ ks origin age M S t
  have record:=law U
  have positive:1≤h:=le_max_left _ _
  have value:massLog (actual U)-massLog (old U)=M.model.read b g U:=sub_eq_iff_eq_add.mpr record.2
  refine ⟨record.1,?_⟩
  rw [value]
  exact WilsonCoherentMayerPriorSampler.purchased R M (fun _=>(h:ℂ)) (fun _ =>by exact_mod_cast (by linarith: h≠0))
    s hs t a hL legs q ord enough hord small

end YM.Integration.WilsonCoherentMayerPriorMeasuredFiling
