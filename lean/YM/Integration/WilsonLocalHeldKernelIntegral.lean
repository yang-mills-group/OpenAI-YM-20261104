import YM.Integration.WilsonLocalConditionalWilsonFactor

/-! A signed held-field kernel on the original fine action. The local
Haar/Wilson polynomial is independent of the held coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldKernelIntegral
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics WilsonReportingForestPivots
open WilsonLocalConditionalWilsonFactor WilsonLocalReportingChartIntegral
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] {c f:Side} {S:StepData c f}

def predicted (P:ChartRatio G) (p:ℕ) (β g:ℝ) (T:Forest S.ratio) (B:Finset T.Free)
    (C:Set (Config G f)) (h:Config G f→ℝ) (z:Field (G:=G) T B) : ℝ :=
  factor P p β g T B z*C.indicator h (sampled T B z)

theorem point (j f x δ:ℝ) (jpos:0 ≤ j) (price:|j-f| ≤ δ*j) :
    ‖j*x-f*x‖ ≤ δ*‖j*x‖ := by
  rw [←sub_mul,norm_mul,norm_mul,Real.norm_of_nonneg jpos,←mul_assoc,Real.norm_eq_abs (j-f)]
  exact mul_le_mul_of_nonneg_right price (norm_nonneg x)

theorem signed (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε r:ℝ}
    (ep:0 < ε) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (h:Config G (R.family.side (m+1) per)→ℝ),
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let β:=R.family.path.β N per (m+1)
    let μ:=law G T B r
    let a:=entry P T B C h
    let b:=predicted P p β g T B C h
    Measurable h→Integrable a μ→Integrable b μ ∧
      |(∫z,a z ∂μ)-(∫z,b z ∂μ)| ≤ ε*g^p*∫z,‖a z‖ ∂μ := by
  filter_upwards [priced R simple slow P hp J clear d p ep rv] with m bill N live per o T h
  intro B C g β μ a b mh original
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  apply WilsonLocalReportingDensityIntegral.difference μ original
    ((regular P p β g T B).mul ((mh.indicator ms).comp (sampled_m T B)))
  filter_upwards [ball_ae (G:=G) T B r] with z hz
  change ‖a z-b z‖ ≤ ε*g^p*‖a z‖
  by_cases hc:sampled T B z∈C
  · exact point _ _ _ _ (Chart.jacobian_nonneg _) (bill N live per o T z hz hc)
  · simp only [a,b,entry,predicted,indicator_of_notMem hc,mul_zero,sub_zero,norm_zero,le_refl]

theorem normalized (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (p:ℕ) {ε r:ℝ}
    (ep:0 < ε) (pr:0 < r) (sr:r < Chart.small G P) (rv:r ≤ J.r) :
    ∀ᶠm:ℕ in atTop,∀N,m < N→∀per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (D H:Config G (R.family.side (m+1) per)→ℝ) (L:ℝ),
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let β:=R.family.path.β N per (m+1)
    let ρ:=actualConditionalDensity R.family N per m V
    let μ:=law G T B r
    let a:=entry P T B C (fun U=>D U*H U)
    let b:=predicted P p β g T B C (fun U=>D U*H U)
    Measurable D→Envelope H→GaugeInvariant H→(∀U,|D U| ≤ L*ρ U)→
    Integrable a μ ∧ Integrable b μ ∧ |(∫z,a z ∂μ)-(∫z,b z ∂μ)| ≤
      (ε*g^p*L)*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  filter_upwards [signed R simple slow P hp J clear d p ep rv,
    WilsonLocalReportingChartIntegral.original R simple slow J clear P hp pr sr d] with m paid trace N live per o T V D H L
  intro B C g β ρ μ a b seen env invariant bounded
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  obtain ⟨h0,ph,lower⟩:=WilsonHeldExteriorLaw.upper_floor R N per m live
  have ew:Envelope ρ:=(WilsonHeldExteriorLaw.regularity R N per m live V (R.family.path.rep N per (m+1))
    ((R.family.path.rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live).good) ph lower).1
  have eH:Envelope (fun U=>|H U|):=⟨env.meas.abs,env.cost.imp fun _ h U=>by simpa only [Real.norm_eq_abs,abs_abs] using h U⟩
  let k:=entry P T B C (fun U=>ρ U*|H U|)
  have ik:Integrable k μ:=integrable P hp T B ms (ew.mul eH) pr sr
  have mb:Measurable a:=((Chart.Ratio.jacobian_meas hp).comp measurable_snd).mul
    (((seen.mul env.meas).indicator ms).comp (sampled_m T B))
  have bound:∀z,‖a z‖ ≤ L*k z := by
    intro z
    let U:=sampled T B z
    by_cases hc:sampled T B z∈C
    · simp only [a,k,entry,indicator_of_mem hc,norm_mul,Real.norm_of_nonneg (Chart.jacobian_nonneg _),Real.norm_eq_abs]
      calc Chart.jacobian P z.2*(|D U| * |H U|) ≤ Chart.jacobian P z.2*((L*ρ U)*|H U|) :=
             mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (bounded U) (abs_nonneg _)) (Chart.jacobian_nonneg _)
           _ = L*(Chart.jacobian P z.2*(ρ U*|H U|)):=by ring
    · simp only [a,k,entry,indicator_of_notMem hc,mul_zero,norm_zero,le_refl]
  have ia:Integrable a μ:=(ik.const_mul L).mono' mb.aestronglyMeasurable (ae_of_all _ bound)
  obtain ⟨ib,err⟩:=paid N live per o T _ (seen.mul env.meas) ia
  have en:=integral_mono ia.norm (ik.const_mul L) bound
  have val:=trace N live per o T V _ eH (fun t U=>congrArg abs (invariant t U))
  rw [integral_const_mul] at en
  change actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V=∫z,k z ∂μ at val
  rw [←val] at en
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  exact ⟨ia,ib,err.trans ((mul_le_mul_of_nonneg_left en (mul_nonneg ep.le (pow_nonneg gp.le _))).trans_eq (by ring))⟩

end YM.Integration.WilsonLocalHeldKernelIntegral
