import YM.Integration.WilsonReportingUVTranslation
import YM.Integration.WilsonMatrixTicketLanesReportedPlatedBank

/-! Retain the actual change of the Wilson conditional likelihood between
a genuine microscopic position and its embedded reporting center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestPlatedShift
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source OPE OPE.Therm Push.GridApprox
open RG05Readout Native Address Many Records Harvest Extra.Histories
open PhysicalNext.Repeat.Legato MergeProof Accent WilsonMacroscopicForwardTransfer
open WilsonMacroscopicRichFlatFibre WilsonReportingUVStencil
open FVA2 RG12 RG17 Extraction Spec Table RG16.Literal
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Astage
open WilsonTranslatedFactory Next.Rank.Price Pert.Asymptotics
open WilsonMatrixTicketLanesReportedPivot WilsonMatrixTicketLanesReportedPlating
open private pushed from YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p d j:ℕ}
local notation "C" => R.family

def movement (live:j<N)(v:(C).label d)(a z:Site ((C).side N p))(W:Config G ((C).side j p)):ℂ:=
  let K:=likelihood R N p live W
  (∫ U,(C).O N p v a U*(K (pull 1 (-(z-a)) U)-K U) ∂scene (C).path N p N)/
    (dose (H:=(C).path) (p:=p) j W N:ℂ)

theorem measured (live:j<N)(v:(C).label d)(a z:Site ((C).side N p))(W:Config G ((C).side j p)):
    actualTransport C (N:=N) ((C).O N p v z) live.le W =
      actualTransport C (N:=N) ((C).O N p v a) live.le W+movement R live v a z W:=by
  let μ:=scene (C).path N p N
  let K:=likelihood R N p live W
  let X:=(C).O N p v a
  let D:ℂ:=dose (H:=(C).path) (p:=p) j W N
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson le_rfl
  have cash (y:Site ((C).side N p)):actualTransport C (N:=N) ((C).O N p v y) live.le W=
      (∫U,(C).O N p v y U*K U ∂μ)/D:=by
    have legal:Integrable ((C).O N p v y) μ:=((C).continuousO N p d v y).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    exact (WilsonReportingUVLikelihood.normalized R N p live.le _ W).symm.trans
      ((WilsonReportingUVLikelihood.exterior_eq R N p live.le _ W).trans
        (WilsonMacroscopicRichFlatFibre.measured R live le_rfl _ legal W))
  have moved:(C).O N p v z=fun U=>evaluate X U (z-a):=by
    funext U
    change _=(C).O N p v a (pull 1 (z-a) U)
    rw [pull_one,(C).translation,show a+(z-a)=z by abel]
  have fine:μ=law G ((C).side N p) ((C).beta N p):=WilsonMacroscopicForwardTransfer.top R.makes N p
  have turn:(∫U,(C).O N p v z U*K U ∂μ)=∫U,X U*K (pull 1 (-(z-a)) U) ∂μ:=by
    rw [moved,fine]
    exact WilsonReportingUVTranslation.transpose _ X K _
  have envX:Envelope X:=by
    have h:Continuous X:=(C).continuousO N p d v a
    obtain ⟨B,cap⟩:=isCompact_univ.exists_bound_of_continuousOn h.continuousOn
    exact ⟨h.measurable,B,fun U=>cap U (mem_univ _)⟩
  have envK:Envelope K:=enrolled R N p live W
  have shifted:Envelope (fun U=>K (pull 1 (-(z-a)) U)):=by
    obtain ⟨smooth,A,bound⟩:=envK
    exact ⟨smooth.comp (continuous_pull 1 _).measurable,A,fun U=>bound _⟩
  have split:(∫U,X U*(K (pull 1 (-(z-a)) U)-K U) ∂μ)=
      (∫U,X U*K (pull 1 (-(z-a)) U) ∂μ)-(∫U,X U*K U ∂μ):=by
    simp only [mul_sub]
    exact integral_sub ((envX.mulC shifted).integrableC μ) ((envX.mulC envK).integrableC μ)
  rw [cash z,cash a,turn]
  change (∫U,X U*K (pull 1 (-(z-a)) U) ∂μ)/D =
    (∫U,X U*K U ∂μ)/D + (∫U,X U*(K (pull 1 (-(z-a)) U)-K U) ∂μ)/D
  rw [split,sub_div,add_sub_cancel]

theorem deposited (live:j ≤ N)(X:Goods G ((C).side N p))(W:Config G ((C).side j p)):
    actualTransport C (N:=N) X live W=credit C N p 0 X j live W/(((C).path.rep N p j).eval W:ℂ):=by
  rw [←WilsonReportingUVLikelihood.normalized R N p live]
  have top (U):((C).path.rep N p N).eval U=bare ((C).beta N p) U:=congrFun (R.makes.wilson.starts N p).2 U
  simp only [credit,pow_zero,one_smul,Records.dyes,pushed,Extra.Histories.liftVac,top]

variable {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(L:Layout F)

theorem original (r:ℝ)(w:(C).label d)(aged:(C).ref d ≤ L.level r)(live:L.level r<N)
    (z:Site ((C).side N p))(W:Config G ((C).side (L.level r) p)):
    let y:=((C).S.toDepth live.le p).parent z
    let a:=anchor (C).S p live.le y
    let v:=atRef L d r (N,p) w
    let Q:=entry R.makes live.le y (((C).factory d N p).terminal.symm v)
    let Y:=(C).path.rep N p (L.level r)
    actualTransport C (N:=N) ((C).O N p v z) live.le W=
      (∑ i,column R F L d r w i*Light (WilsonCoherentTerminalFrame.lamp R d i) ((C).side (L.level r) p) y W)+
      (((C).S.a (L.level r):ℂ)^d)⁻¹*WilsonMatrixTicketLanesReportedCredit.remainder R Q Y y W+
      movement R live v a z W:=by
  intro y a v Q Y
  rw [measured R live v a z W,deposited R live.le ((C).O N p v a) W]
  exact congrArg (fun q:ℂ=>q+movement R live v a z W)
    (WilsonMatrixTicketLanesReportedPlatedBank.held R F L d r w N p aged live.le y W)

end YM.Integration.WilsonReportHarvestPlatedShift
