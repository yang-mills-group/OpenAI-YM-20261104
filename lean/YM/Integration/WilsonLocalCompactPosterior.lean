import YM.Integration.WilsonLocalCompactPosteriorWeight

/-! The full compact RG12 posterior normalized against itself. A tested
constant cancels exactly before paying the relative density error. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactPosterior
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre WilsonLocalHeldKernelChart
open WilsonLocalCompactPosteriorWeight
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per m:ℕ}

theorem tested (live:m<N) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ)
    (eh:Envelope H) (gh:GaugeInvariant H):
    let f:=fun u:T.Slice G=>actualConditionalDensity R.family N per m V (T.drape u)*H (T.drape u)
    Integrable f (T.order G) ∧ (∫u,f u ∂T.order G)=actualAverage R.family (N:=N) H V := by
  intro f
  let w:=fun U=>actualConditionalDensity R.family N per m V U*H U
  have ew:Envelope w:=(WilsonCoherentMeasuredChart.driver R m per N live V).mul eh
  have pw:Pinned (R.family.path.levels.clock.op m per) w:=by
    intro a pins U
    have k:=projected R N per m (fun l=>l V) a pins U
    change reduced R N per m V (Lattice.gauge a U)=reduced R N per m V U at k
    dsimp only [w]
    have fixed:(R.family.path.rep N per (m+1)).eval (Lattice.gauge a U)=(R.family.path.rep N per (m+1)).eval U:=
      Next.Rank.gauge_eval (R.makes.wilson.represents N per (m+1) live).good a U
    rw [density,density,k,fixed,gh a U]
  have ef:Envelope f:=⟨ew.meas.comp T.continuous_drape.measurable,ew.cost.choose,fun u=>ew.cost.choose_spec (T.drape u)⟩
  letI:IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  exact ⟨ef.integrable _,(T.pack w (ew.integrable _) pw).symm⟩

private theorem deviation {X:Type} [MeasurableSpace X] {H:X→ℝ} (eh:Envelope H) (b:ℝ):Envelope (fun x=>|H x-b|):=by
  obtain ⟨B,bank⟩:=eh.cost
  refine ⟨(eh.meas.sub measurable_const).abs,B+‖b‖,fun x=>?_⟩
  rw [Real.norm_eq_abs,abs_abs,←Real.norm_eq_abs]
  exact (norm_sub_le ..).trans (add_le_add_left (bank x) _)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let a:=amount R live grade T B V
    let μ:=T.order G
    let Z:=∫u,a u ∂μ
    let v:=actualAverage R.family (N:=N) H V
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    Integrable a μ ∧ Integrable (fun u=>a u*H (T.drape u)) μ ∧ 0<Z ∧
    (R.family.path.rep N per m).eval V≤(1+δ)*Z ∧ (∫u,a u/Z ∂μ)=1 ∧
    |(∫u,a u*H (T.drape u) ∂μ)/Z-v| ≤ δ*(1+δ)*actualAverage R.family (N:=N) (fun U=>|H U-v|) V := by
  filter_upwards [WilsonLocalCompactPosteriorWeight.fields R simple marks fees slow d q grade ord ep] with t sold N live per o T V H eh gh
  intro B a μ Z v δ
  let f:=fun u:T.Slice G=>actualConditionalDensity R.family N per t V (T.drape u)
  let p:=scaled R live grade T B V
  let h:=fun u:T.Slice G=>H (T.drape u)
  let c:=(R.family.path.rep N per t).eval V
  have cp:0<c:=Multi.AxisShift.chosen_positive R.makes.wilson (by omega) V
  have law (u):a u=c*p u:=cancel R live grade T B V u
  have hf:=tested R live.le T V H eh gh
  have unit:=tested R live.le T V (fun _=>1) (Envelope.const 1) (fun _ _=>rfl)
  change Integrable (fun u=>f u*1) μ ∧ (∫u,f u*1 ∂μ)=actualAverage R.family (N:=N) (fun _=>1) V at unit
  simp only [mul_one,actualAverage_const R.family R.makes live.le] at unit
  have weight:=sold N live per o T V
  have dn:0≤δ:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have earned:=WilsonLocalCompactQuotient.centered (p:=p) (h:=h) μ dn unit.1 unit.2 weight.1
    (eh.meas.comp T.continuous_drape.measurable) hf.1 (fun u=>⟨(weight.2 u).1,(weight.2 u).2.2⟩)
  change Integrable p μ ∧ Integrable (fun u=>p u*h u) μ ∧ 0<(∫u,p u ∂μ) ∧ 1≤(1+δ)*(∫u,p u ∂μ) ∧
    |(∫u,p u*h u ∂μ)/(∫u,p u ∂μ)-(∫u,f u*h u ∂μ)|≤δ*(1+δ)*∫u,‖f u*(h u-∫u,f u*h u ∂μ)‖ ∂μ at earned
  have center:(∫u,f u*h u ∂μ)=v:=hf.2
  rw [center] at earned
  obtain ⟨pi,phi,zp,budget,estimate⟩:=earned
  have absolute (u):‖f u*(h u-v)‖=f u*|h u-v|:=by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (weight.2 u).1]
  have dev:=(tested R live.le T V (fun U=>|H U-v|) (deviation eh v) (fun g U=>congrArg (fun z=>|z-v|) (gh g U))).2
  simp_rw [absolute] at estimate
  change (∫u,f u*|h u-v| ∂μ)=_ at dev
  rw [dev] at estimate
  have aeq:a=(fun u=>c*p u):=funext law
  have heq:(fun u=>a u*H (T.drape u))=(fun u=>c*(p u*h u)):=by funext u;rw [law,mul_assoc]
  have denominator:Z=c*(∫u,p u ∂μ):=by dsimp only [Z];rw [aeq,integral_const_mul]
  have numerator:(∫u,a u*H (T.drape u) ∂μ)=c*(∫u,p u*h u ∂μ):=by rw [heq,integral_const_mul]
  have Zp:0<Z:=denominator ▸ mul_pos cp zp
  refine ⟨aeq ▸ pi.const_mul c,heq ▸ phi.const_mul c,Zp,?_,?_,?_⟩
  · change c≤(1+δ)*Z
    rw [denominator,mul_left_comm]
    exact le_mul_of_one_le_right cp.le budget
  · rw [integral_div];exact div_self Zp.ne'
  · rw [numerator,denominator,mul_div_mul_left _ _ cp.ne']
    exact estimate

end YM.Integration.WilsonLocalCompactPosterior
