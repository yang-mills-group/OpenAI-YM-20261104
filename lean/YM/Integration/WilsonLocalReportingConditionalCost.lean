import YM.Integration.WilsonLocalHeldMarginalExperiment

/-! Whole compact incoming fields, with the actual held kernel. The base
law costs its true upper quadratic moment and needs no extra score fee. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingConditionalCost
open Filter Set MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalReportingChartIntegral WilsonLocalHeldKernelChart WilsonLocalAnchoredKernel
open WilsonLocalHeldCurvatureMarginal WilsonLocalHeldDerivatives
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

theorem regular (R:Run G) {m per N:ℕ} (live:m<N)
    (H:Config G (R.family.side (m+1) per)→ℝ) (eh:Envelope H)
    {C:Set (Config G (R.family.side (m+1) per))} (ms:MeasurableSet C) :
    let v:=scene R.family.path N per (m+1)
    let w:=scene R.family.path N per m
    let good:=actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|))
    Integrable good w ∧ (∫V,good V ∂w)≤Real.sqrt (∫U,‖H U‖^2 ∂v) := by
  intro v w good
  letI:IsProbabilityMeasure v:=probability R.makes.wilson live
  obtain ⟨int,mean⟩:=push R live (absolute eh ms)
  have sz:Real.sqrt (v.real C)≤1:=(Real.sqrt_le_sqrt (measureReal_le_one (μ:=v) (s:=C))).trans_eq Real.sqrt_one
  exact ⟨int,mean.le.trans ((tested v ms H eh).trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) sz))⟩

theorem rejected (R:Run G) {m per N:ℕ} (live:m<N)
    (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ) (eh:Envelope H)
    {C:Set (Config G (R.family.side (m+1) per))} (ms:MeasurableSet C) :
    |actualAverage R.family (N:=N) H V-actualAverage R.family (N:=N) (C.indicator H) V|≤
      actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V := by
  let ρ:=actualConditionalDensity R.family N per m V
  have paid (U):|ρ U|≤1*ρ U:=(abs_of_nonneg (actualConditionalDensity_nonneg R.family R.makes live V U)).le.trans_eq (one_mul _).symm
  have q:=WilsonLocalHeldRough.original R live V ρ H ms (WilsonCoherentMeasuredChart.driver R m per N live V).meas eh paid
  have issued (U):C.indicator (fun u=>ρ u*H u) U=ρ U*(C.indicator H U):=by
    by_cases hit:U∈C <;> simp [hit]
  simpa only [issued,actualAverage,smul_eq_mul,one_mul,ρ] using q

theorem measured (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (H:Config G (R.family.side (m+1) per)→ℝ),
    Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let μ:=law G T B r
    let upper:=scene R.family.path N per (m+1)
    let lower:=scene R.family.path N per m
    let expense:=fun V=>(ε/2)*g^q*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V+
      actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V
    Integrable expense lower ∧ (∫V,expense V ∂lower) ≤ ε*g^q*Real.sqrt (∫U,‖H U‖^2 ∂upper) ∧
    ∀V,let a:=forecast P q R live grade T B C (fun F=>F V) H
       Integrable a μ ∧ |actualAverage R.family (N:=N) H V-(∫z,a z ∂μ)| ≤ expense V := by
  filter_upwards [WilsonLocalHeldMarginalExperiment.original R stoves simple marks fees slow P hp J clear d q grade ord ep pr sr rv]
    with m bought N live per o T H env gi
  have law:=bought N live per o T [] H 1 env gi zero_le_one (fun V=>(WilsonCoherentMeasuredChart.driver R m per N live.le V).meas) (fun V U=>by
    change |actualConditionalDensity _ _ _ _ V U|≤_
    rw [abs_of_nonneg (actualConditionalDensity_nonneg R.family R.makes live.le V U),one_mul])
  simpa only [WilsonLocalHeldDerivatives.measured,leftDerivs,actualAverage,smul_eq_mul,mul_one,one_mul] using law

end YM.Integration.WilsonLocalReportingConditionalCost
