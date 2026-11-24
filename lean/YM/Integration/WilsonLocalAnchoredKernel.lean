import YM.Integration.WilsonLocalAnchoredReportingFactor
import YM.Integration.WilsonLocalHeldKernelChart

/-! An arbitrary signed reading of the actual held transition against the
complete compact prior and the finite retained action anchored at the same
exterior. The coarse normalization remains inside the chosen reading. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalAnchoredKernel
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonLocalConditionalWilsonFactor
open WilsonLocalReportingChartIntegral WilsonLocalHeldKernelChart
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def signal (R:Run G) (N per m:ℕ) (read:(Config G (R.family.side m per)→ℝ)→ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ) (U:Config G (R.family.side (m+1) per)) :=
  read (fun V=>reduced R N per m V U)*(R.family.path.rep N per (m+1)).eval U*H U

def forecast (P:ChartRatio G) (q:ℕ) (R:Run G) {N per m:ℕ} (live:m+1<N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (C:Set (Config G (R.family.side (m+1) per))) (read:(Config G (R.family.side m per)→ℝ)→ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ) (z:Field (G:=G) T B) : ℝ :=
  let Q:=R.family.path.rep N per (m+1)
  let A:=approximation R (p:=per) live grade
  let U:=sampled T B z
  let U0:=sampled T B (z.1,0)
  let φ:=factor P q (R.family.path.β N per (m+1)) (regulatorRun R.family N per (m+1)) T B z
  if U∈C then φ*(Q.eval U0/A.eval U0)*(read (fun V=>reduced R N per m V U)*A.eval U*H U) else 0

theorem reenter (P:ChartRatio G) (q:ℕ) (R:Run G) {N per m:ℕ} (live:m+1<N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (C:Set (Config G (R.family.side (m+1) per))) (read:(Config G (R.family.side m per)→ℝ)→ℝ)
    (H:Config G (R.family.side (m+1) per)→ℝ) (z:Field (G:=G) T B) :
    forecast P q R live grade T B C read H z = WilsonLocalAnchoredReportingFactor.multiplier P q R live grade T B z*
      C.indicator (signal R N per m read H) (sampled T B z) := by
  by_cases yes:sampled T B z∈C
  · rw [forecast,if_pos yes,indicator_of_mem yes]
    exact (WilsonLocalAnchoredReportingFactor.field P q R live grade T B z _ _).symm
  · rw [forecast,if_neg yes,indicator_of_notMem yes,mul_zero]

theorem source (R:Run G) {N per m:ℕ} (live:m<N) (V:Config G (R.family.side m per))
    (read:(Config G (R.family.side m per)→ℝ)→ℝ) (H:Config G (R.family.side (m+1) per)→ℝ) {L:ℝ}
    (positive:0≤L) (mr:Measurable (fun U=>read (fun W=>reduced R N per m W U))) (eh:Envelope H)
    (gi:GaugeInvariant H) (paid:∀U,|read (fun W=>reduced R N per m W U)| ≤ L*reduced R N per m V U) :
    let h:=signal R N per m read H
    let ρ:=actualConditionalDensity R.family N per m V
    Envelope h ∧ Pinned (R.family.path.levels.clock.op m per) h ∧ ∀U,‖h U‖ ≤ L*(ρ U*|H U|) := by
  intro h ρ
  let Q:=R.family.path.rep N per (m+1)
  have qp:∀U,0 < Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live
  have bought:=R.makes.wilson.represents N per (m+1) live
  have eQ:Envelope Q.eval:=Q.envelope bought.good
  have bound (U):‖h U‖ ≤ L*(ρ U*|H U|) := by
    rw [show h U=read (fun W=>reduced R N per m W U)*Q.eval U*H U from rfl,
      Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (qp U)]
    calc _ ≤ (L*reduced R N per m V U)*Q.eval U*|H U| :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (paid U) (qp U).le) (abs_nonneg _)
         _ = L*(ρ U*|H U|) := by change _=L*(actualConditionalDensity R.family N per m V U*|H U|);rw [density];ring
  have ew:=WilsonCoherentMeasuredChart.driver R m per N live V
  have eabs:Envelope (fun U=>|H U|):=⟨eh.meas.abs,eh.cost.imp fun _ h U=>by simpa only [Real.norm_eq_abs,abs_abs] using h U⟩
  obtain ⟨k,price⟩:=(ew.mul eabs).cost
  refine ⟨⟨(mr.mul eQ.meas).mul eh.meas,L*k,fun U=>(bound U).trans (mul_le_mul_of_nonneg_left ?_ positive)⟩,?_,bound⟩
  · exact (le_abs_self _).trans (price U)
  · intro a pins U
    exact congrArg₂ (·*·) (congrArg₂ (·*·) (projected R N per m read a pins U)
      (Next.Rank.gauge_eval bought.good a U)) (gi a U)

theorem original (R:Run G) (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (read:(Config G (R.family.side m per)→ℝ)→ℝ) (H:Config G (R.family.side (m+1) per)→ℝ) (L:ℝ),
    0≤L→Measurable (fun U=>read (fun W=>reduced R N per m W U))→Envelope H→GaugeInvariant H→
    (∀U,|read (fun W=>reduced R N per m W U)|≤L*reduced R N per m V U)→
    let B:=incident R T d o
    let C:=cold R m per d o
    let μ:=law G T B r
    let h:=signal R N per m read H
    let a:=forecast P q R live grade T B C read H
    let g:=regulatorRun R.family N per (m+1)
    Integrable a μ ∧ |(∫U,C.indicator h U ∂prior G (R.family.side (m+1) per))-(∫z,a z ∂μ)| ≤
      ε*g^q*L*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  filter_upwards [WilsonLocalAnchoredReportingFactor.purchased R simple marks fees slow P hp J clear d q grade order ep rv,
    WilsonLocalHeldKernelChart.original R simple slow J clear P hp pr sr d,
    WilsonLocalReportingChartIntegral.original R simple slow J clear P hp pr sr d] with m tariff physical compare N live per o T V read H L pos mr eh gi priced
  intro B C μ h a g
  let ρ:=actualConditionalDensity R.family N per m V
  let chart:=entry P T B C h
  let k:=entry P T B C (fun U=>ρ U*|H U|)
  let Φ:=WilsonLocalAnchoredReportingFactor.multiplier P q R live grade T B
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  obtain ⟨e,pins,amount⟩:=source R live.le V read H pos mr eh gi priced
  have iz:Integrable chart μ:=integrable P hp T B ms e pr sr
  have eh':Envelope (fun U=>|H U|):=⟨eh.meas.abs,eh.cost.imp fun _ h U=>by simpa only [Real.norm_eq_abs,abs_abs] using h U⟩
  have ik:Integrable k μ:=integrable P hp T B ms ((WilsonCoherentMeasuredChart.driver R m per N live.le V).mul eh') pr sr
  obtain ⟨mφ,bill⟩:=tariff N live per o T
  have eq:a=(fun z=>Φ z*C.indicator h (sampled T B z)):=funext (reenter P q R live grade T B C read H)
  have ma:Measurable a:=eq ▸ mφ.mul ((e.meas.indicator ms).comp (sampled_m T B))
  have cost:∀ᵐz ∂μ,‖chart z-a z‖ ≤ ε*g^q*‖chart z‖ := by
    filter_upwards [ball_ae (G:=G) T B r] with z hz
    rw [eq];by_cases here:sampled T B z∈C
    · exact WilsonLocalHeldKernelIntegral.point _ _ _ _ (Chart.jacobian_nonneg _) (bill z ⟨hz,here⟩)
    · simp only [chart,entry,indicator_of_notMem here,mul_zero,sub_zero,norm_zero,le_refl]
  obtain ⟨ia,rated⟩:=WilsonLocalReportingDensityIntegral.difference μ iz ma cost
  have dominate (z):‖chart z‖ ≤ L*k z := by
    by_cases here:sampled T B z∈C
    · simp only [chart,k,entry,indicator_of_mem here,norm_mul,Real.norm_of_nonneg (Chart.jacobian_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (amount _) (Chart.jacobian_nonneg _)).trans_eq (by ring)
    · simp only [chart,k,entry,indicator_of_notMem here,mul_zero,norm_zero,le_refl]
  have total:=integral_mono iz.norm (ik.const_mul L) dominate
  rw [integral_const_mul] at total
  have truth:=physical per o T h e pins
  have absRead:=compare N live.le per o T V _ eh' (fun k U=>congrArg abs (gi k U))
  change actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V=∫z,k z ∂μ at absRead
  rw [←absRead] at total
  rw [truth]
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact ⟨ia,rated.trans ((mul_le_mul_of_nonneg_left total (mul_nonneg ep.le (pow_nonneg gp _))).trans_eq (by ring))⟩

end YM.Integration.WilsonLocalAnchoredKernel
