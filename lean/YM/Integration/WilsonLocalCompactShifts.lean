import YM.Integration.WilsonLocalCompactSegmentMean

/-! Centering commutes with each normalized compact forest operator and with
the full earlier Wilson transport. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactShifts
open Filter MeasureTheory Lattice RG RG16 Next Wilson
open Tree Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactPosteriorWeight WilsonLocalCompactTransition
open scoped Classical Topology
variable {X:Type} [MeasurableSpace X]

theorem bounded {f:X→ℝ} (ef:Envelope f) (c:ℝ):Envelope (fun x=>f x-c):=by
  refine ⟨ef.meas.sub measurable_const,ef.cost.choose+‖c‖,fun x=>?_⟩
  exact (norm_sub_le ..).trans (add_le_add_left (ef.cost.choose_spec x) _)

theorem normalized {μ:Measure X} {ρ f:X→ℝ} (inte:Integrable ρ μ)
    (unit:(∫x,ρ x ∂μ)≠0) (ef:Envelope f) (c:ℝ):
    (∫x,ρ x*(f x-c) ∂μ)/(∫x,ρ x ∂μ)=(∫x,ρ x*f x ∂μ)/(∫x,ρ x ∂μ)-c:=by
  have paid:Integrable (fun x=>ρ x*f x) μ:=
    (inte.norm.mul_const ef.cost.choose).mono' (inte.aestronglyMeasurable.mul ef.meas.aestronglyMeasurable)
      (Eventually.of_forall fun x=>by
        rw [norm_mul];exact mul_le_mul_of_nonneg_left (ef.cost.choose_spec x) (norm_nonneg _))
  simp only [mul_sub,integral_sub paid (inte.mul_const c),integral_mul_const]
  field_simp

variable {G:Gauge} {I:Type} [Fintype I]

theorem actual (C:Family G) (makes:C.Makes) {N per b:ℕ} (cut:b≤N)
    {H:Config G (C.side b per)→ℝ} (eh:Envelope H) (c:ℝ) {j:ℕ} (live:j≤b):
    actualTransport C (N:=N) (fun U=>H U-c) live=fun V=>actualTransport C (N:=N) H live V-c:=by
  induction live using Nat.decreasingInduction with
  | self=>simp only [actualTransport_base C makes cut]
  | of_succ i hi ih=>
    rw [actualTransport_step C makes cut _ hi,actualTransport_step C makes cut H hi]
    rw [ih]
    funext V
    let ρ:=actualConditionalDensity C N per i V
    have paid:=normalized (actualConditionalDensity_integrable C makes (hi.trans_le cut) V)
      (by rw [actualConditionalDensity_total C makes (hi.trans_le cut) V];exact one_ne_zero)
      (WilsonCoherentEarlier.envelope C makes cut eh hi) c
    simpa only [actualConditionalDensity_total C makes (hi.trans_le cut) V,div_one,actualAverage,smul_eq_mul] using paid

theorem funded (R:Run G) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (grade:ℕ) (ord:5≤grade):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio)
      (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→∀c:ℝ,
    let B:=incident R T d o
    send R live grade T B (fun U=>H U-c)=fun V=>send R live grade T B H V-c:=by
  filter_upwards [WilsonLocalCompactPosterior.original R simple marks fees slow d 0 grade ord zero_lt_one]
    with i law N live per o T H eh c
  intro B;funext V
  have unit:=law N live per o T V (fun _=>1) (Envelope.const 1) (fun _ _=>rfl)
  have pulled:Envelope (fun x:T.Slice G=>H (T.drape x)):=⟨eh.meas.comp T.continuous_drape.measurable,eh.cost.choose,
    fun x=>eh.cost.choose_spec _⟩
  exact normalized unit.1 unit.2.2.1.ne' pulled c

end YM.Integration.WilsonLocalCompactShifts
