import YM.Integration.WilsonSeparatedOriginalSlabWatchSignedDebit
import YM.Integration.WilsonReportingUVLikelihood
import YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

/-! Each directional observation of the complete signed residual uses one physical posterior on the original ultraviolet fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPosterior
open OPE OPE.Therm Push.GridApprox
open Function Set Lattice Wilson RG Source Analysis Next.Foundations Push.Local Bid RG16.Literal
open Trace.Physical Trace.Physical.GermGraph RGComparison.Core16 RG05Readout Records Extra.Histories
open PhysicalNext.Repeat.Legato MergeProof Accent WilsonMacroscopicForwardTransfer
open WilsonMacroscopicRichFlatFibre WilsonMacroscopicRichFlatPosteriorLaw MeasureTheory
open private pushed from YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){u N p h:ℕ}
local notation "C"=>R.family

theorem physical (T:Slices (C).path.levels p)(live:u<N)(Y:Cut C N p)(ct:Continuous Y)
    (V:Config G ((C).side u p)):
    WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y V=
      ((C).S.a u:ℂ)^h * ∫W,Y W ∂law R N p live V:=by
  letI:IsProbabilityMeasure (scene (C).path N p N):=probability R.makes.wilson le_rfl
  have integrable:Integrable Y (scene (C).path N p N):=ct.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have numerator:credit C N p h Y u live.le V=((C).S.a u:ℂ)^h*dyes C u N p live.le Y V:=by
    have bareEq (W:Config G ((C).side N p)):((C).path.rep N p N).eval W=bare ((C).beta N p) W:=congrFun (R.makes.wilson.starts N p).2 W
    have same:(fun W=>(((C).path.rep N p N).eval W:ℂ)*Y W)=(fun W=>(bare ((C).beta N p) W:ℂ)*Y W):=by funext W;rw [bareEq W]
    unfold credit dyes;rw [pushed,same];rfl
  have pos:(((C).path.rep N p u).eval V:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos R.makes.wilson live.le V).ne'
  have den:=WilsonMacroscopicRichReportedPosterior.density R T live.le h Y V
  rw [numerator] at den
  rw [←reading R live le_rfl V Y integrable,←WilsonReportingUVLikelihood.exterior_eq R N p live.le Y V]
  change _=((C).S.a u:ℂ)^h*(dyes C u N p live.le Y V/(((C).path.rep N p u).eval V:ℂ))
  field_simp [pos];linear_combination -den

def measureJet (live:u<N)(Y:Cut C N p)(trial:(C).label h)(t:Probe G h):ℂ:=
  Germ.jet (C).params t ((C).path.rep N p u).p.threshold 0 (fun V=>((C).S.a u:ℂ)^h*
    ∫W,(Y W-(C).O N p trial 0 W) ∂law R N p live V)

theorem original (T:Slices (C).path.levels p)(live:u<N)(Y:Cut C N p)(ct:Continuous Y)(trial:(C).label h)(t:Probe G h):
    WilsonSeparatedOriginalSlabWatchSignedDebit.hearing R T live.le Y trial t=measureJet R live Y trial t:=by
  unfold WilsonSeparatedOriginalSlabWatchSignedDebit.hearing measureJet
  congr 1;funext V;exact physical R T live _ (ct.sub ((C).continuousO ..)) V

end YM.Integration.WilsonSeparatedOriginalSlabWatchPosterior
