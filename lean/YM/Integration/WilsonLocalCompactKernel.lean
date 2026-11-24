import YM.Integration.WilsonLocalExteriorCalibration
import YM.Integration.WilsonLocalHeldDerivatives

/-! On the full Wilson forest, with no plaquette cutoff, replace the
previous action by its original retained action and an exterior factor.
The signed lower-boundary score stays on the same conditional law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactKernel
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Further.LogJets
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre WilsonLocalHeldKernelChart
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def adjusted (R:Run G) {N per m:ℕ} (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (F:Config G (R.family.side (m+1) per)→ℝ) (u:T.Slice G) :=
  let v:=((cut T (moving T B)) u).2
  let P:=approximation R (p:=per) live grade
  (base R live grade T B v*P.eval (T.drape u))*F (T.drape u)

theorem signed (R:Run G) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (F:Config G (R.family.side (m+1) per)→ℝ),
    let B:=incident R T d o
    let W:=fun U=>(R.family.path.rep N per (m+1)).eval U*F U
    let A:=adjusted R live grade T B F
    let g:=regulatorRun R.family N per (m+1)
    let ν:=prior G (R.family.side (m+1) per)
    Measurable F → Envelope W → Pinned (R.family.path.levels.clock.op m per) W →
    Integrable A (T.order G) ∧ |(∫U,W U ∂ν)-(∫u,A u ∂T.order G)|≤ε*g^q*∫U,‖W U‖ ∂ν := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenue,fields R simple marks fees slow d q grade ord ep] with m offer bill N live per o T F
  intro B W A g ν mf ew pw
  let E:=moving T B
  let Q:=R.family.path.rep N per (m+1)
  let P:=approximation R (p:=per) live grade
  let v:=fun u:T.Slice G=>((cut T E) u).2
  let X:=fun u:T.Slice G=>T.drape u
  letI:IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  have mx:Measurable X:=T.continuous_drape.measurable
  have mq:Measurable Q.eval:=(Q.envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have mp:Measurable P.eval:=(OriginalMarkedRunCovariance.keep_envelope R live (offer N per live)).meas
  have qp:∀U,0<Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have mv:Measurable v:=measurable_snd.comp (cut T E).measurable
  have origin:Measurable (fun u:T.Slice G=>state (G:=G) T B (v u,0)):=(measurable_state T B).comp (mv.prodMk measurable_const)
  have mA:Measurable A:=((((mq.comp origin).div (mp.comp origin)).mul (mp.comp mx)).mul (mf.comp mx))
  have e:Envelope (fun u=>W (X u)):=⟨ew.meas.comp mx,ew.cost.choose,fun u=>ew.cost.choose_spec (X u)⟩
  have good:(∀ᵐ u ∂T.order G,‖W (X u)-A u‖≤ε*g^q*‖W (X u)‖):=by
    filter_upwards [] with u
    let x:=((cut T E) u).1
    have eq:filled T E (v u) x=X u:=by
      change T.drape ((cut T E).symm ((cut T E) u))=T.drape u
      rw [MeasurableEquiv.symm_apply_apply]
    have rate:=((bill N live per o T (v u)).2 x).1
    rw [eq] at rate
    exact WilsonLocalHeldKernelIntegral.point _ _ _ _ (qp (X u)).le rate
  obtain ⟨integral,loss⟩:=WilsonLocalReportingDensityIntegral.difference (T.order G) (e.integrable _) mA good
  refine ⟨integral,?_⟩
  rw [T.pack W (ew.integrable ν) pw,T.pack (fun U=>‖W U‖) (ew.integrable ν).norm
    (fun h pins U=>congrArg norm (pw h pins U))]
  exact loss

end YM.Integration.WilsonLocalCompactKernel
