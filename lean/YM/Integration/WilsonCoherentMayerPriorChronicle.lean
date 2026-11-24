import YM.Integration.WilsonCoherentMayerPriorMeasured

/-! The holder at each genuinely descended date has the full transported Wilson source as its normalized numerator. The vacuum and all proper earlier submoments remain on the original period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorChronicle
open Filter Lattice Wilson RG Source Marker Precision
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction ActualOriginalQReaders
open MS.Local.Physical Extra.Histories
open RG3.Script.Picnic IterationFour.Vacuum MergeProof MergeProof.Accent
open WilsonReportingPrescribedOldRawForecast (raw)
open scoped Classical
variable {G:Gauge}{V:Type}[DecidableEq V]{Γ:Census V}

def reading (R:Run G)(N p j:ℕ)(Y:Config G (R.family.side j p)→Poly Γ)
    (U:Config G (R.family.side j p)):Poly Γ:=((R.family.path.rep N p j).eval U)⁻¹ • Y U

private lemma matched (R:Run G) {N N₀ p p₀ j:ℕ} (cut:N=N₀)(per:p=p₀)
    {Y:Config G (R.family.side j p)→Poly Γ}{Z:Config G (R.family.side j p₀)→Poly Γ}
    (same:HEq Y Z)(one:∀ U,(reading R N₀ p₀ j Z U).part Γ.quiet=1):
    HEq (reading R N p j Y) (reading R N₀ p₀ j Z) ∧ ∀ U,(reading R N p j Y U).part Γ.quiet=1:=by
  subst N₀;subst p₀;cases eq_of_heq same;exact ⟨HEq.rfl,one⟩

variable [Fintype V][Nonempty V]{B:Deck G}(R:Run G)(hG:G.Simple)(u:V→MS.Rake.Label B)
    (J₀:Request V)(A₀:NumericSchedule R.family J₀)(d₀:LocalFormal.Datum R.family (Stock.census V))
    (Q:MS.Land.Prescription B)(o:V→Site (R.family.side (d₀.level+1) d₀.period))(μ:ℝ)(ks:V→ℕ)
    {J:Request V}{A:NumericSchedule R.family J}{d:LocalFormal.Datum R.family (Stock.census V)}
    {F:AnalyticInput J A d}{η:ℝ}{I:FullPreparedInputAt F η}
local notation "JB" => ActualOriginalQPointSetup.request R u J₀

theorem original (origin:QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (age:∀a:Slot u,R.family.ref a.2.size≤d₀.level+1)
    (M:FundedRenderedBank.Catalogue J d)(S:FundedRenderedBank.Bank I M)(t:IndependentTests J.tests):
    let h:=ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
    let b:=VariableScaling.tests (fun _=>(h:ℂ)) (testInclusion J.tests t)
    let actual:=reading R d.cutoff d.period d.level (S.output.output.leaf b).density
    let old:=reading R d.cutoff d.period d.level (S.output.residual.leaf b).density
    ∃t₀:IndependentTests (JB).tests,HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
    ∃live:d.level≤d₀.level+1,
      HEq actual (reading R d₀.cutoff d₀.period d.level (gust R.family.path d₀.cutoff d₀.period (d₀.level+1)
        (raw R hG u J₀ d₀ Q o μ ks t₀) d.level live)) ∧
      ∀U,(old U).part (Stock.census V).quiet=1 ∧
        massLog (actual U)=M.model.read b (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U+
          massLog (old U):=by
  intro h b actual old
  obtain ⟨t₀,test⟩:=QLocalOriginalQHistory.unit origin.tests t
  obtain ⟨live,field⟩:=QLocalOriginalQHistory.physical R hG u J₀ A₀ d₀ Q o μ ks origin M S
    (testInclusion J.tests t) (testInclusion _ t₀) test
  let birth:=raw R hG u J₀ d₀ Q o μ ks t₀
  let arrived:=gust R.family.path d₀.cutoff d₀.period (d₀.level+1) birth d.level live
  have deposited:HEq (S.output.output.leaf b).density arrived:=field
  have quiet (U): (reading R d₀.cutoff d₀.period d.level arrived U).part (Stock.census V).quiet=1:=by
    let D:=ActualOriginalQPointSetup.pointDatum R J₀ d₀.period (d₀.level+1) o
    let z:=testInclusion _ t₀
    let word:=ActualStartupNormalizedQ.modeObservable Q D u (μ-R.family.S.scale d₀.cutoff) ks z
    have one:word (Stock.census V).quiet=fun _=>(1:ℂ):=by
      funext Z;simp [word,ActualStartupNormalizedQ.modeObservable,Census.quiet]
    have trueWord:=WilsonReportingPrescribedOldMicroscopic.original R Q D u (μ-R.family.S.scale d₀.cutoff) ks hG
      d₀.below age z live (Stock.census V).quiet U
    change (reading R d₀.cutoff d₀.period d.level arrived U).part (Stock.census V).quiet=
      actualTransport R.family (N:=d₀.cutoff) (word (Stock.census V).quiet) live U at trueWord
    rw [one,actualTransport_const R.family R.makes d₀.below] at trueWord
    exact trueWord
  obtain ⟨line,present⟩:=matched R origin.cutoff origin.period deposited quiet
  exact ⟨t₀,test,live,line,fun U=>WilsonCoherentMayerPriorMeasured.original M S b U (present U)⟩

end YM.Integration.WilsonCoherentMayerPriorChronicle
