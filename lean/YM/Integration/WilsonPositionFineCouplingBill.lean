import YM.Integration.WilsonPositionProgramInversionBill
import YM.Integration.WilsonPositionRawDetector

/-! Charge the scalar substitution at the actual Wilson coupling of the fine
endpoint, uniformly in both later physical regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionFineCouplingBill
open Filter Set Finset Function Lattice Wilson RG RG16 RG16.Literal RG16.Guarding
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE OPE.Owl Trace.Pilot Pert.Asymptotics
open XSpace FVA2 FVA2.Register FVA2.Scale MS MS.Land
open WilsonPositionRawMesh WilsonPositionProgramCommonWindow
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (hG : G.Simple) {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit)
    (t : ℝ→ℝ) (physical : Coupling G t)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B
local notation "Λ" => WilsonPositionAuxiliaryReporterCalendar.scale R hG (B:=B)

include hB pace physical in
theorem finer : ∀ᶠ r in trail, ∀ f N per : ℕ, m r≤f → f≤N →
    0<regulatorRun R.family N per f ∧ regulatorRun R.family N per f ≤ 2*t r := by
  have lim := WilsonPhysicalCutoffCurrency.temperature R hG pace hB t physical
  filter_upwards [physical.positive,(tendsto_order.mp lim).1 _ (by norm_num : (1/2:ℝ)<1)] with r hr low f N per after before
  let A:=R.family.path.levels
  let g:=regulatorRun R.family N per f
  let b:=R.family.path.β N per f
  have up := R.makes.wilson.represents N per f before
  have bm : 0<A.clock.hatBeta (m r) := zero_lt_one.trans (A.fits.delayed _)
  have bf : 0<A.clock.hatBeta f := zero_lt_one.trans (A.fits.delayed _)
  have follows : A.clock.hatBeta (m r) ≤ A.clock.hatBeta f :=
    (Real.log_le_log_iff bm bf).mp (WilsonAdmissionScale.logarithm_monotone A hG after)
  have bpos : 0<b := Overlay.beta_positive R.makes.wilson before
  have cash : g^2*b=1 := cashable R.family R.makes before
  have band : A.clock.hatBeta f/2≤b := up.band.1
  have positive : 0<g := g_pos R.makes before
  refine ⟨positive,?_⟩
  change 1/2<A.clock.hatBeta (m r)*(t r)^2 at low
  have pay : g^2≤(2*t r)^2 := by
    apply (mul_le_mul_iff_of_pos_right bpos).mp
    rw [cash]
    have h : A.clock.hatBeta (m r) / 2 ≤ b := ((div_le_div_iff_of_pos_right (by norm_num)).mpr follows).trans band
    nlinarith only [low,mul_le_mul_of_nonneg_right h (sq_nonneg (t r))]
  change g≤2*t r
  nlinarith only [pay,positive,hr,sq_nonneg (g-2*t r)]

variable (Z : WilsonPrescription G) {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M S dial)

private theorem detector_bound (i q : ℕ) {u : ℝ} (hu : |u|≤1) :
    |forward Z (Z.run.step i) q u| ≤ mass Z (Z.run.step i) q *|u| := by
  unfold forward mass
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun k _=>?_ )
  by_cases h : (k:ℕ)=0
  · simp [detector,h,PowerSeries.coeff_zero_eq_constantCoeff_apply,Rose.zero_choice]
  · rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_of_le_one (abs_nonneg u) hu h) (abs_nonneg _)

include hB pace physical H in
theorem interval (q : ℕ) (hq : 0<q) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail, ∀ i:ℕ, (Λ r)^((3:ℝ)/2)≤(i:ℝ)*Real.log Z.run.ratio →
      (i:ℝ)*Real.log Z.run.ratio≤(Λ r)^((3:ℝ)/2)+2*(Λ r) →
      ∀ f N per : ℕ, m r≤f → f≤N →
        let u := regulatorRun R.family N per f
        |u|≤1 ∧ |forward Z (Z.run.step i) q u|≤1 ∧
          (1+mass Z (Z.run.step i) q)^q * |u|^(q+1) ≤ δ*|t r|^q := by
  let ε := min ((1:ℝ)/2) (δ/2^(q+1))
  have ep : 0<ε := lt_min (by norm_num) (div_pos hd (by positivity))
  have issued := WilsonPositionProgramInversionBill.interval R hG hB pace t physical Z H q ep
  have tiny := (physical.conforms hG).eventually_lt_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [issued,finer R hG hB pace t physical,tiny,physical.positive] with r dates stage small live i lower upper f N per fi nf
  obtain ⟨_,_,charge⟩ := dates i lower upper
  obtain ⟨pos,le⟩ := stage f N per fi nf
  let u:=regulatorRun R.family N per f
  let h:=mass Z (Z.run.step i) q
  have hn : 0≤h := sum_nonneg fun k _=>abs_nonneg _
  have hu : |u|≤2*t r := by rwa [abs_of_pos pos]
  have unit : |u|≤1 := by linarith
  have one : h≤(1+h)^q := by
    calc h≤1+h := by linarith
         _ ≤ (1+h)^q := le_self_pow₀ (by linarith) hq.ne'
  have β : (1+h)^q*t r≤ε := by rwa [abs_of_pos live] at charge
  have guard : h*|u|≤1 := calc
    _ ≤ (1+h)^q*(2*t r) := mul_le_mul one hu (abs_nonneg _) (pow_nonneg (by linarith) _)
    _ ≤ 1 := by linarith only [β,show ε≤1/2 from min_le_left ..]
  refine ⟨unit,(detector_bound Z i q unit).trans guard,?_⟩
  change (1+h)^q*|u|^(q+1)≤δ*|t r|^q
  rw [abs_of_pos live]
  have pay := (le_div_iff₀ (by positivity : 0<(2:ℝ)^(q+1))).mp (β.trans (min_le_right ..))
  calc
    _ ≤ (1+h)^q*(2*t r)^(q+1) := by gcongr
    _ = ((1+h)^q*t r*2^(q+1))*(t r)^q := by rw [mul_pow,pow_succ (t r)];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right pay (pow_nonneg live.le _)

end YM.Integration.WilsonPositionFineCouplingBill
