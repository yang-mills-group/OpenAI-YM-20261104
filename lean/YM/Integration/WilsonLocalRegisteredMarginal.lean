import YM.Integration.WilsonLocalMarginalPrimary
import YM.Integration.WilsonLocalRetainedReportingExperiment
import YM.Integration.WilsonLocalReportingConditionalCost

/-! The actual signed compact incoming roster and its retained Taylor
experiment, including the rejected part at its original joint RMS price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalRegisteredMarginal
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open WilsonLocalMarginalPrimary WilsonLocalReportingConditionalCost
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I]

def Estimate (R:Run G) {m N per:ℕ} (live:m+1<N) (P:ChartRatio G)
    (q grade:ℕ) (r ε:ℝ) (d:I→ℕ) (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (c:ℂ) (χ:ℂ→L[ℝ]ℝ)
    (H M:Config G (R.family.side (m+1) per)→ℝ) : Prop :=
  let C:=cold R m per d o
  let B:=incident R T d o
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  let g:=regulatorRun R.family N per (m+1)
  let upper:=scene R.family.path N per (m+1)
  let lower:=scene R.family.path N per m
  let F:=fun U=>H U*M U
  let δ:=(ε/2)*g^q
  let A:=‖χ‖*‖c‖*originalMass R d y
  let good (h:Config G (R.family.side (m+1) per)→ℝ):=actualAverage R.family (N:=N) (C.indicator (fun U=>|h U|))
  let outlay:=fun V=>(δ*good F V+(2*δ*A)*good H V)+actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|F U|)) V
  Integrable outlay lower ∧ (∫V,outlay V ∂lower)≤ε*g^q*(Real.sqrt (∫U,‖F U‖^2 ∂upper)+A*Real.sqrt (∫U,‖H U‖^2 ∂upper)) ∧
    ∀V,let retained:=∫z in panel R m per d o T r,
      WilsonLocalRetainedReportingWeight.adjusted P q R live grade T B V z * H (state T B z) *
        χ (c*polynomial T B R d θ y o (q+2*reserve R d) z) ∂law P r T B
    |actualAverage R.family (N:=N) F V-retained|≤outlay V

theorem funded (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (c:ℂ) (χ:ℂ→L[ℝ]ℝ)
    (H M:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→Envelope M→
    (∀U∈cold R m per d o,M U=held R d o (R.family.path.rep N per (m+1)).p.threshold y c χ U)→
    Estimate R live P q grade r ε d y o T c χ H M := by
  let η:=ε/2
  have pos:0<η:=half_pos ep
  filter_upwards [WilsonLocalRetainedReportingExperiment.measured R simple marks fees slow J clear P hp pr sr rv d q grade ord pos,
    WilsonLocalHeldCurvatureMarginal.original R stoves simple slow d q pos] with m current rough N live per y o T c χ H M eh gh em same
  unfold Estimate;intro C B θ g upper lower F δ A good outlay
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  have ef:Envelope F:=eh.mul em
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have dp:0≤δ:=mul_nonneg pos.le (pow_nonneg gp _)
  have ap:0≤A:=mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (prod_nonneg fun i _=>Work.G08.size_nonneg ..)
  have ap':0≤2*δ*A:=mul_nonneg (mul_nonneg zero_le_two dp) ap
  obtain ⟨iv,cv⟩:=regular R live.le F ef ms
  obtain ⟨iw,cw⟩:=regular R live.le H eh ms
  obtain ⟨iz,cz⟩:=rough N live.le per o F ef
  let Z:=actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|F U|))
  refine ⟨((iv.const_mul δ).add (iw.const_mul (2*δ*A))).add iz,?_,?_⟩
  · change (∫V,(δ*good F V+(2*δ*A)*good H V)+Z V ∂lower)≤_
    have iF:Integrable (fun V=>δ*good F V) lower:=iv.const_mul δ
    have iH:Integrable (fun V=>(2*δ*A)*good H V) lower:=iw.const_mul (2*δ*A)
    have together:Integrable (fun V=>δ*good F V+(2*δ*A)*good H V) lower:=iF.add iH
    have iZ:Integrable Z lower:=iz
    rw [integral_add together iZ,integral_add iF iH,integral_const_mul,integral_const_mul]
    exact (add_le_add (add_le_add (mul_le_mul_of_nonneg_left cv dp) (mul_le_mul_of_nonneg_left cw ap')) cz).trans_eq
      (by dsimp only [η,δ];ring)
  · intro V retained
    let actual:=held R d o θ y c χ
    have replace (s:ℝ→ℝ):C.indicator (fun U=>s (H U*actual U))=C.indicator (fun U=>s (F U)):=by
      funext U
      by_cases hit:U∈C
      · simp only [indicator_of_mem hit,F,same U hit,actual,θ]
      · simp only [indicator_of_notMem hit]
    have first:=replace id
    simp only [id_eq] at first
    have quote:=current N live per y o T V c χ H eh gh
    change |actualAverage R.family (N:=N) (C.indicator (fun U=>H U*actual U)) V-retained|≤
      δ*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U*actual U|)) V+
      (2*((‖χ‖*‖c‖)*(δ*originalMass R d y)))*good H V at quote
    rw [first,replace abs,show 2*((‖χ‖*‖c‖)*(δ*originalMass R d y))=2*δ*A by dsimp only [A];ring] at quote
    exact (abs_sub_le (actualAverage R.family (N:=N) F V) (actualAverage R.family (N:=N) (C.indicator F) V) retained).trans
      ((add_le_add (rejected R live.le V F ef ms) quote).trans_eq (add_comm ..))

theorem original (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (c:ℂ) (χ:ℂ→L[ℝ]ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let θ:=(R.family.path.rep N per (m+1)).p.threshold
    Estimate R live P q grade r ε d y o T c χ H (held R d o θ y c χ) ∧
    Estimate R live P q grade r ε d y o T c χ H (mark R d o θ y c χ) := by
  filter_upwards [funded R stoves simple marks fees slow P hp J clear d q grade ord ep pr sr rv,
    on_event R d simple] with m bill old N live per y o T c χ H eh gh
  intro θ
  exact ⟨bill N live per y o T c χ H _ eh gh (bounded R d o θ y c χ) (fun _ _=>rfl),
    bill N live per y o T c χ H _ eh gh (legitimate R d o θ y c χ).1
      (fun U hu=>congrArg (fun a:ℂ=>χ (c*a)) (old N per live.le o y U hu))⟩

end YM.Integration.WilsonLocalRegisteredMarginal
