import YM.Integration.WilsonMatrixTicketLanesRegisteredLoss
import YM.Integration.WilsonInvariantActionConditionalRegistered
import YM.Integration.WilsonRegisteredLogFare

/-! Removal of the local masks in the genuinely measured nonzero covariance, retaining
the same two original cutoff means and the complete signed earlier fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance
open Function Filter Set MeasureTheory Lattice RG Wilson Source MergeProof Push.Local
open RG12 OPE.Therm Extraction Spec IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics
open LocalComparison RG3.Script.Picnic Push.SectorMeasure WilsonInheritedRegisteredField
open WilsonMatrixTicketLanesConnectedRegistered WilsonMatrixTicketLanesRegisteredNorm
open WilsonInvariantActionRegisteredReturn WilsonMatrixTicketLanesRegulatorColumn
open private measurable from YM.Integration.WilsonMatrixTicketLanesRegisteredLoss
open private integral from YM.Integration.WilsonInvariantActionConditionalRegistered
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:RG17.Layout F) {k N per d:ℕ}

private theorem product {α:Type*} [MeasurableSpace α] {x h:α→ℂ}
    (ex:Envelope x) (eh:Envelope h):Envelope (fun U=>x U*h U):=by
  obtain ⟨D,hD⟩:=ex.cost
  obtain ⟨C,hC⟩:=eh.cost
  refine ⟨ex.meas.mul eh.meas,D*C,fun U=>?_⟩
  rw [norm_mul]
  exact mul_le_mul (hD U) (hC U) (norm_nonneg _) ((norm_nonneg _).trans (hD U))

private theorem mean_form {α:Type} [MeasurableSpace α] (μ:Measure α) [IsFiniteMeasure μ]
    {x h:α→ℂ} (ex:Envelope x) (eh:Envelope h):
    pair (fun a=>∫ U,a U ∂μ) x h=∫ U,x U*(h U-∫V,h V ∂μ) ∂μ:=by
  simp only [pair,mul_sub]
  rw [integral_sub (integral (product ex eh)) ((integral ex).mul_const _),integral_mul_const]

include F L in
theorem centered (simple:G.Simple) (Y:Poetry R.family.path.levels) (d e b q:ℕ) {D C ε:ℝ}
    (hD:0 ≤ D) (hC:0 ≤ C) (hε:0<ε):
    ∀ᶠ k:ℕ in atTop,∀ N,(live:k ≤ N)→∀ per,(R.family.ref d ≤ k)→
      ∀ (v:R.family.label d) (o:Site (R.family.side k per)),
      mass R.family d (entry R d k N per v) ≤ D/(regulatorRun R.family N per k)^e→
      ∀ h:Config G (R.family.side k per)→ℂ,Measurable h→
      (∀U,‖h U‖ ≤ C/(regulatorRun R.family N per k)^b)→
      ‖pair (fun a=>∫U,a U ∂scene R.family.path N per k) (maskError R live v o) h‖ ≤ 
        ε*(regulatorRun R.family N per k)^q:=by
  have price:=WilsonMatrixTicketLanesRegisteredLoss.tested R F L simple Y d e b q hD (C:=2*C)
    (mul_nonneg zero_le_two hC) hε
  filter_upwards [price,WilsonMatrixTicketLanesReportedAccuracy.small R simple 1 zero_lt_one]
    with k bill small N live per age v o invoice h hm cap
  let g:=regulatorRun R.family N per k
  let μ:=scene R.family.path N per k
  letI:IsProbabilityMeasure μ:=probability (p:=per) R.makes.wilson live
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have hh:Envelope h:=⟨hm,C/g^b,cap⟩
  have hhmean:‖∫U,h U ∂μ‖ ≤ C/g^b:=by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ cap)
  let t:=fun U=>h U-∫V,h V ∂μ
  have ht:∀U,‖t U‖ ≤ (2*C)/g^b:=fun U=>(norm_sub_le _ _).trans
    ((add_le_add (cap U) hhmean).trans_eq (by ring))
  have ex:Envelope (maskError R live v o):=⟨measurable R live v o,_,fun U=>loss R F L age live (small N per live) v o U⟩
  have receipt:=bill N live per age v o invoice t (hm.sub measurable_const) ht k le_rfl
  rw [actualTransport_base R.family R.makes live] at receipt
  rw [mean_form μ ex hh]
  exact (norm_integral_le_integral_norm _).trans receipt

/-- Both actual regular invoices at this stage have only a quadratic inverse-coupling
charge above the normalized original cutoff mass. -/
theorem columns (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠ k:ℕ in atTop,∀ N per,k ≤ N→(R.family.path.levels.params k).columns ≤ 4/(regulatorRun R.family N per k)^2:=by
  obtain ⟨a,ha⟩:=eventually_atTop.mp (WilsonRegisteredLogFare.column R simple slow.2)
  filter_upwards [eventually_ge_atTop (a+1)] with k future N per live
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega :k≠0)
  let β:=R.family.path.levels.clock.hatBeta (i+1)
  let g:=regulatorRun R.family N per (i+1)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have hβ:0 ≤ β:=zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have raw:β*g^2 ≤ 2:=WilsonMatrixTicketLanesReportedAccuracy.thermal R (i+1) N per live
  calc
    _ ≤ 2*Real.log β:=ha i (by omega)
    _ ≤ 2*β:=mul_le_mul_of_nonneg_left (Real.log_le_self hβ) zero_le_two
    _ ≤ 4/g^2:=by apply (le_div_iff₀ (pow_pos gp 2)).mpr; nlinarith only [raw]

/-- Keep the nonlinear group field and every old regular term at its actual translated
placement. -/
def unmaskedEarlier (k N per:ℕ) (live:k ≤ N) (v:R.family.label 4)
    (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):ℂ:=
  R.family.O k per (WilsonMatrixTicketLanesReportedPivot.center R k N per v) o U+
    WilsonInvariantActionMixedMaterial.earlier (C:=R.family) R.makes live v o Set.univ U

theorem split (live:k ≤ N) (v:R.family.label 4) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    regular (C:=R.family) R.makes live v o U=unmaskedEarlier R k N per live v o U+maskError R live v o U:=by
  rw [four R live v o U]
  unfold unmaskedEarlier
  ring

end YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance
