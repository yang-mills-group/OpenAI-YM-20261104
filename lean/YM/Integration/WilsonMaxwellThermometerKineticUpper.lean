import YM.Integration.WilsonMaxwellThermometerKineticLog

/-! The absolute kinetic unit holds for every original cutoff and period above the named fine date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticUpper
open Filter Function Set RG Lattice Wilson Source Extraction Table Spec Climb Trace.Pilot PhysMS
open OPE PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FVA2.Register Pert.Asymptotics XSpace
open scoped Topology Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : ℕ} (hB : 0<B)
    (pace : WilsonWindowReportingPace.Slow R.kit) (Z : WilsonPrescription G) {fine index : ℝ→ℕ}
local notation "Visit" => ℝ×(ℕ×ℕ)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "unit" => WilsonMaxwellThermometerKineticLog.unit G
local notation "g" => regulatorRun R.family
local notation "β" => R.family.path.β
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index

private def cuts (j : ℝ→ℕ) : Filter Visit := Filter.comap Prod.fst trail ⊓ 𝓟 {w|j w.1≤w.2.1}

private theorem dates (j : ℝ→ℕ) : Tendsto Prod.fst (cuts j) trail := tendsto_iff_comap.mpr inf_le_left

private theorem live (j : ℝ→ℕ) : ∀ᶠ w : Visit in cuts j,j w.1≤w.2.1 := by
  rw [cuts,eventually_inf_principal]
  exact Eventually.of_forall fun _ h=>h

include hB pace in
private theorem measured (l : Filter Visit) (down : Tendsto Prod.fst l trail)
    (admitted : ∀ᶠ w in l,m w.1≤w.2.1) :
    Tendsto (fun w:Visit=>g w.2.1 w.2.2 (m w.1)/unit w.1) l (𝓝 1) := by
  let s:=R.family.S.scale
  let beta:=fun w:Visit=>β w.2.1 w.2.2 (m w.1)
  have top:=(WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB).comp down
  have measured : Tendsto (fun w:Visit=>beta w/s (m w.1)) l (𝓝 (2*b0 G)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [top.eventually (zeroUp_bound R.family R.makes ep),admitted] with w hw enrolledAt
    exact (show |beta w/s (m w.1)-2*b0 G|<ε from hw w.2.1 w.2.2 enrolledAt)
  have height : Height R.family.S trail LogV m 1 :=
    WilsonMeasuredWindow.measured_stop_height R.family.path.levels simple B
      (WilsonFundedMeasuredWindow.paced R pace) hB to_log_zoom length_rate
  have gross : Tendsto (fun w:Visit=>beta w/LogV w.1) l (𝓝 (2*b0 G)) := by
    have combined:=measured.mul (height.pace.comp down)
    rw [mul_one] at combined
    apply combined.congr'
    filter_upwards [(R.family.S.divergent.comp top).eventually_gt_atTop 0] with w here
    change beta w/s (m w.1)*(s (m w.1)/LogV w.1)=beta w/LogV w.1
    field_simp [show s (m w.1)≠0 from here.ne']
  have pos : 0<2*b0 G := b0_normalizes (G:=G) ▸ G.slopeConstant_pos simple
  have root := (Real.continuous_sqrt.tendsto (2*b0 G)).comp gross
  have ratio := (tendsto_const_nhds (x:=Real.sqrt (2*b0 G))).div root (Real.sqrt_pos.mpr pos).ne'
  rw [div_self (Real.sqrt_pos.mpr pos).ne'] at ratio
  refine ratio.congr' ?_
  filter_upwards [down.eventually (to_log_zoom.eventually_gt_atTop 0),admitted] with w high sold
  have warm : 0<beta w := Overlay.beta_positive R.makes.wilson sold
  change Real.sqrt (2*b0 G)/Real.sqrt (beta w/LogV w.1)=(Real.sqrt (beta w))⁻¹/(Real.sqrt (2*b0 G*LogV w.1))⁻¹
  rw [Real.sqrt_div' _ high.le,Real.sqrt_mul pos.le,div_inv_eq_mul]
  field_simp [(Real.sqrt_pos.mpr high).ne',(Real.sqrt_pos.mpr warm).ne']

include hB pace in
theorem original (schedule : enrolled) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ r in trail, ∀ N per, fine r≤N → |g N per (fine r)/unit r-1|<ε := by
  let l:=cuts fine
  have down:=dates fine
  have enough := live fine
  have upper : ∀ᶠw:Visit in l,m w.1≤w.2.1 := by
    filter_upwards [down.eventually schedule,enough] with w paid permitted using paid.1.trans permitted
  have report:=measured R simple hB pace l down upper
  let Λ:=fun r=>WilsonAdmissionScale.logarithm R.family.path.levels (m r)
  have high:=(WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB)
  have cash:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp high).const_mul (16*(G.slopeConstant+1))
  rw [mul_zero] at cash
  have across : Tendsto (fun w:Visit=>g w.2.1 w.2.2 (fine w.1)/g w.2.1 w.2.2 (m w.1)) l (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hd
    filter_upwards [down.eventually (WilsonMaxwellThermometerKineticAppointment.finite R simple hB Z schedule),
      down.eventually (cash.eventually_lt_const hd),enough] with w bought price room
    rw [Real.dist_eq]
    apply (bought _ _ room).trans_lt
    change 16*(G.slopeConstant+1)*((Λ w.1)^2*Real.exp (-(Λ w.1)))<δ at price
    linarith only [price]
  have head : Tendsto (fun w:Visit=>g w.2.1 w.2.2 (fine w.1)/unit w.1) l (𝓝 1) := by
    have total:=across.mul report
    rw [one_mul] at total
    refine total.congr' ?_
    filter_upwards [upper] with w paid
    have positive : 0<g w.2.1 w.2.2 (m w.1) :=
      inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson paid))
    field_simp [positive.ne']
  have sale:=Metric.tendsto_nhds.mp head ε ep
  rw [show l=Filter.comap Prod.fst trail ⊓ 𝓟 {w:Visit|fine w.1≤w.2.1} from rfl,
    eventually_inf_principal,eventually_comap] at sale
  filter_upwards [sale] with r bought N per granted
  exact bought (r,N,per) rfl granted

end YM.Integration.WilsonMaxwellThermometerKineticUpper
