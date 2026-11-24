import YM.Integration.WilsonLocalReportingChartIntegral
import YM.Integration.WilsonLocalReportingSpectator

/-! The normalized occupied conditional for a signed original group field:
the numerical integral keeps its full inherited density, the sampled
transition, the compact exterior and the physical cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalReportingDensityIntegral
open Function Filter Set Finset MeasureTheory Metric Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction
open WilsonLocalConditionalResidue WilsonLocalReportingChartIntegral WilsonLocalReportingChartFunctions
open WilsonLocalReportingExpense WilsonLocalInheritedDensity MSbar.Heath OPE.Therm Pert.Asymptotics
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G:Gauge} 

theorem rest_m (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per)) :
    Measurable (WilsonLocalInheritedRatio.rest R.family N per m V) := by
  let C:=R.family
  let β:=C.path.β N per (m+1)
  let y:=(C.path.rep N per m).eval V
  let ρ:=actualConditionalDensity C N per m V
  obtain ⟨b,hb,lo⟩:=WilsonHeldExteriorLaw.upper_floor R N per m hm
  have ew:Envelope ρ:=(WilsonHeldExteriorLaw.regularity R N per m hm V (C.path.rep N per (m+1))
    ((C.path.rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) hm).good) hb lo).1
  have yp:0 < y:=Multi.AxisShift.chosen_positive R.makes.wilson hm.le V
  have eq:WilsonLocalInheritedRatio.rest C N per m V=(fun U=>ρ U*y/bare β U) := by
    funext U
    change _=actualConditionalDensity C N per m V U*y/bare β U
    rw [WilsonLocalInheritedRatio.split]
    change _=(WilsonLocalInheritedRatio.rest C N per m V U*bare β U/y)*y/bare β U
    field_simp [yp.ne',(bare_pos β U).ne']
  rw [eq];exact (ew.meas.mul_const y).div (bare_cont β).measurable

def proposal (P:ChartRatio G) (p:ℕ) (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (g:ℝ)
    (C:Set (Config G (R.family.side (m+1) per))) (H:Config G (R.family.side (m+1) per)→ℝ)
    (z:WilsonLocalReportingChartIntegral.Field (G:=G) T B) :=
  if sampled T B z∈C then model P p R N per m V T B z.1 g (g⁻¹•z.2)*H (sampled T B z) else 0

theorem proposal_m (P:ChartRatio G) (p:ℕ) (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (g:ℝ)
    {C:Set (Config G (R.family.side (m+1) per))} (hc:MeasurableSet C) {H:Config G (R.family.side (m+1) per)→ℝ}
    (hh:Measurable H) : Measurable (proposal P p R N per m V T B g C H) := by
  let E:=moving T B
  let A:=WilsonLocalReportingChartIntegral.Field (G:=G) T B
  let β:=R.family.path.β N per (m+1)
  have hX:Measurable (fun z:A=>g⁻¹•z.2):=(continuous_const_smul g⁻¹).measurable.comp measurable_snd
  have hx:=position_m T B measurable_fst hX g
  have h0:=position_m T B (M:=A) measurable_fst (measurable_const (a:=(0:↥E→G.Color))) g
  have hq:Measurable (fun z:A=>model P p R N per m V T B z.1 g (g⁻¹•z.2)) :=
    (((measurable_const.mul ((rest_m R N per m hm V).comp hx)).mul ((bare_cont β).measurable.comp h0)).div_const _).mul
      (score_m P p β g T B measurable_fst hX measurable_const).exp
  exact Measurable.ite (sampled_m T B hc) (hq.mul (hh.comp (sampled_m T B))) measurable_const

theorem difference {A:Type} [MeasurableSpace A] (μ:Measure A) {a b:A→ℝ} {t:ℝ}
    (ha:Integrable a μ) (hb:Measurable b) (rate:∀ᵐ z ∂μ,‖a z-b z‖ ≤ t*‖a z‖) :
    Integrable b μ ∧ |(∫z,a z ∂μ)-(∫z,b z ∂μ)| ≤ t*∫z,‖a z‖ ∂μ := by
  have h:Integrable (fun z=>a z-b z) μ :=
    (ha.norm.const_mul t).mono' (ha.aestronglyMeasurable.sub hb.aestronglyMeasurable) rate
  have ib:Integrable b μ:=by
    have v:=ha.sub h
    have eq:a-(fun z=>a z-b z)=b:=by funext z;exact sub_sub_cancel _ _
    rwa [eq] at v
  refine ⟨ib,?_⟩;rw [←integral_sub ha ib,←Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans ((integral_mono_ae h.norm (ha.norm.const_mul t) rate).trans_eq (integral_const_mul ..))

end YM.Integration.WilsonLocalReportingDensityIntegral
