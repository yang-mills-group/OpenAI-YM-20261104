import YM.Integration.WilsonLocalHeldCurvatureMarginal

/-! Volume-independent marginal comparison for the true signed held
Wilson derivatives. The displayed majorant also admits a correlated
coarse test, with the same physical lower measure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldMarginalExperiment
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalReportingChartIntegral WilsonLocalHeldKernelChart
open WilsonLocalAnchoredKernel WilsonLocalHeldCurvatureMarginal WilsonLocalHeldDerivatives
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I]

theorem original (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (l:List (Directions G (R.family.side m per))) (H:Config G (R.family.side (m+1) per)→ℝ) (L:ℝ),
    Envelope H→GaugeInvariant H→0≤L→(∀V,Measurable (measured R N per m V l))→
    (∀V U,|measured R N per m V l U| ≤ L*actualConditionalDensity R.family N per m V U)→
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let ν:=prior G (R.family.side (m+1) per)
    let μ:=law G T B r
    let upper:=scene R.family.path N per (m+1)
    let lower:=scene R.family.path N per m
    let expense:=fun V=>(ε/2)*g^q*L*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V+
      L*actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V
    Integrable expense lower ∧ (∫V,expense V ∂lower) ≤ ε*g^q*L*Real.sqrt (∫U,‖H U‖^2 ∂upper) ∧
    ∀V,let a:=forecast P q R live grade T B C (fun F=>leftDerivs F l V) H
       Integrable a μ ∧ |(∫U,measured R N per m V l U*H U ∂ν)-(∫z,a z ∂μ)| ≤ expense V := by
  let η:=ε/2
  have hpη:0<η:=half_pos ep
  filter_upwards [WilsonLocalHeldDerivatives.original R simple marks fees slow P hp J clear d q grade order hpη pr sr rv,
    WilsonLocalHeldCurvatureMarginal.original R stoves simple slow d q hpη] with m issued events N live per o T l H L env gi positive seen price
  intro B C g ν μ upper lower expense
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  letI:IsProbabilityMeasure upper:=probability R.makes.wilson live.le
  obtain ⟨imax,cost⟩:=events N live.le per o H env
  obtain ⟨inside,mean⟩:=push R live.le (absolute env ms)
  refine ⟨(inside.const_mul (η*g^q*L)).add (imax.const_mul L),?_,fun V=>issued N live per o T V l H L positive (seen V) env gi (price V)⟩
  let F:=Real.sqrt (∫U,‖H U‖^2 ∂upper)
  have F₀:0≤F:=Real.sqrt_nonneg _
  have radius:Real.sqrt (upper.real C)≤1:=(Real.sqrt_le_sqrt (measureReal_le_one (μ:=upper) (s:=C))).trans_eq Real.sqrt_one
  have interior:(∫V,actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V ∂lower)≤F:=
    mean.le.trans ((tested upper ms H env).trans (mul_le_of_le_one_left F₀ radius))
  let e:=actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|))
  let f:=actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|))
  change (∫V,η*g^q*L*e V+L*f V ∂lower)≤_
  rw [integral_add (inside.const_mul (η*g^q*L)) (imax.const_mul L),integral_const_mul,integral_const_mul]
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact (add_le_add (mul_le_mul_of_nonneg_left interior (mul_nonneg (mul_nonneg hpη.le (pow_nonneg gp _)) positive))
    (mul_le_mul_of_nonneg_left cost positive)).trans_eq (by change η*g^q*L*F+L*(η*g^q*F)=ε*g^q*L*F;unfold η;ring)

end YM.Integration.WilsonLocalHeldMarginalExperiment
