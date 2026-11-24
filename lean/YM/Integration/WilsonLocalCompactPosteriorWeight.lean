import YM.Integration.WilsonLocalCompactScore
import YM.Integration.WilsonLocalCompactQuotient

/-! A retained full-compact posterior from the true Wilson kernel and the
sampled exterior calibration. Its unnormalized weight uses no coarse action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactPosteriorWeight
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre WilsonLocalHeldKernelChart
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per m:ℕ}

def amount (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (V:Config G (R.family.side m per)) (u:T.Slice G):ℝ :=
  let v:=((cut T (moving T B)) u).2
  let U:=T.drape u
  (R.family.path.levels.clock.op m per).density (R.family.path.β N per (m+1)) U V*
    (base R live grade T B v*(approximation R (p:=per) live grade).eval U)

def scaled (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (V:Config G (R.family.side m per)) (u:T.Slice G):ℝ :=
  let v:=((cut T (moving T B)) u).2
  let U:=T.drape u
  reduced R N per m V U*(base R live grade T B v*(approximation R (p:=per) live grade).eval U)

theorem cancel (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (V:Config G (R.family.side m per)) (u:T.Slice G):
    amount R live grade T B V u=(R.family.path.rep N per m).eval V*scaled R live grade T B V u:=by
  have positive:0<(R.family.path.rep N per m).eval V:=Multi.AxisShift.chosen_positive R.makes.wilson (by omega) V
  unfold amount scaled reduced
  field_simp [positive.ne']

private theorem ribbon {k x y δ:ℝ} (kn:0≤k) (rate:|x-y|≤δ*x) :
    |k*x-k*y|≤δ*(k*x):=by
  rw [←mul_sub,abs_mul,abs_of_nonneg kn]
  exact (mul_le_mul_of_nonneg_left rate kn).trans_eq (by ring)

theorem fields (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per)),
    let B:=incident R T d o
    let ρ:=fun u:T.Slice G=>actualConditionalDensity R.family N per m V (T.drape u)
    let p:=scaled R live grade T B V
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    Measurable p ∧ ∀u,0≤ρ u ∧ 0≤p u ∧ |ρ u-p u|≤δ*ρ u ∧ |ρ u-p u|≤δ*p u := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenue,WilsonLocalRetainedCompactFibre.fields R simple marks fees slow d q grade ord ep]
    with t offer permitted N live per o T V
  intro B ρ p δ
  let Q:=R.family.path.rep N per (t+1)
  let P:=approximation R (p:=per) live grade
  let X:=fun u:T.Slice G=>T.drape u
  let E:=moving T B
  let v:=fun u:T.Slice G=>((cut T E) u).2
  have qp:∀U,0<Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have pp:∀U,0<P.eval U:=OriginalMarkedRunCovariance.keep_positive R live (offer N per live)
  have mq:Measurable Q.eval:=(Q.envelope (R.makes.wilson.represents N per (t+1) live.le).good).meas
  have mp:Measurable P.eval:=(OriginalMarkedRunCovariance.keep_envelope R live (offer N per live)).meas
  have mr:Measurable (reduced R N per t V):=by
    have eq:(fun U=>actualConditionalDensity R.family N per t V U/Q.eval U)=reduced R N per t V:=by
      funext U
      rw [density,mul_div_cancel_right₀ _ (qp U).ne']
    rw [←eq]
    exact (WilsonCoherentMeasuredChart.driver R t per N live.le V).meas.div mq
  have mx:Measurable X:=T.continuous_drape.measurable
  have mv:Measurable v:=measurable_snd.comp (cut T E).measurable
  have origin:Measurable (fun u:T.Slice G=>state (G:=G) T B (v u,0)):=(measurable_state T B).comp (mv.prodMk measurable_const)
  refine ⟨(mr.comp mx).mul (((mq.comp origin).div (mp.comp origin)).mul (mp.comp mx)),?_⟩
  intro u
  let x:=((cut T E) u).1
  have eq:filled T E (v u) x=X u:=by
    change T.drape ((cut T E).symm ((cut T E) u))=T.drape u
    rw [MeasurableEquiv.symm_apply_apply]
  have receipt:=permitted N live per o T (v u)
  have rate:=receipt.2 x
  rw [eq] at rate
  let α:=base R live grade T B (v u)
  let h:=reduced R N per t V (X u)
  have hn:0≤h:=div_nonneg ((R.family.path.levels.clock.op t per).density_positive ..)
    (Multi.AxisShift.chosen_positive R.makes.wilson (m:=t) (N:=N) (p:=per) (by omega) V).le
  have yes:ρ u=h*Q.eval (X u):=density R N per t V (X u)
  change 0≤ρ u ∧ 0≤h*(α*P.eval (X u)) ∧ |ρ u-h*(α*P.eval (X u))|≤δ*ρ u ∧
    |ρ u-h*(α*P.eval (X u))|≤δ*(h*(α*P.eval (X u)))
  rw [yes]
  refine ⟨mul_nonneg hn (qp _).le,mul_nonneg hn (mul_nonneg receipt.1.le (pp _).le),ribbon hn rate.1,?_⟩
  exact (abs_sub_comm ..).le.trans (ribbon hn ((abs_sub_comm ..).le.trans rate.2))

end YM.Integration.WilsonLocalCompactPosteriorWeight
