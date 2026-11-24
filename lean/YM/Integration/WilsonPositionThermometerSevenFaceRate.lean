import YM.Integration.WilsonPositionThermometerFinite
import YM.Integration.WilsonPositionThermometerRunning

/-! A uniform grade-nine price on the original seven signed faces implies
the first-order assay at every reporting length. The cutoff limit at a fixed
length precedes the small-length limit. -/
set_option autoImplicit false
set_option format.width 180
noncomputable section
namespace YM.Integration.WilsonPositionThermometerSevenFaceRate
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open XSpace XSpace.Normalize XSpace.Cirrus
open scoped Topology

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) {V : Store G} (K : Rose.Pick V)
    (hG : G.Simple) {B : ℕ}
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B
local notation "c" => Rose.cT K.cut G K.image

/-- Temperature of the actual original history at the physical reporting mesh. -/
def temperature (r : ℝ) (z : ℕ × ℕ) : ℝ := (Real.sqrt (R.family.path.β z.1 z.2 (m r)))⁻¹

/-- A signed grade-eight estimate on the specified common-cutoff numerator.
The three source grades are 3, 2 and 2. -/
def charged (U : Ultrafilter (ℕ × ℕ)) (C η : ℝ) (offer : ℝ → (ℕ × ℕ) → ℂ)
    (first : ℝ → (ℕ × ℕ) → ℝ) : Prop :=
  ∀ᶠ r in trail, ∀ᶠ z in (U : Filter (ℕ × ℕ)),
    let g := temperature (R := R) hG (B := B) r z
    |g^7 * (offer r z).re - first r z*g^8| ≤ C*g^((9 : ℝ)-η)

def rawPrice (U : Ultrafilter (ℕ × ℕ)) (C η : ℝ) (offer : ℝ → (ℕ × ℕ) → ℂ) : Prop :=
  charged (R:=R) hG (B:=B) U C η offer (fun _ _ => c)

/-- The original regulator using fixed representatives of the continuum fields. -/
def price (U : Ultrafilter (ℕ × ℕ)) (C η : ℝ) : Prop :=
  rawPrice (R := R) K hG (B := B) U C η
    (fun r z => (Rose.test K).applyTo (WilsonPositionThermometerRegulator.full J r z))

variable (U : Ultrafilter (ℕ × ℕ)) (prior : (U : Filter (ℕ × ℕ)) ≤ f.fuse)
  (β : ℕ → ℝ) (measured : ∀ j, Tendsto (fun z : ℕ × ℕ => R.family.path.β z.1 z.2 j)
    (U : Filter (ℕ × ℕ)) (𝓝 (β j)))
  (pace : WilsonWindowReportingPace.Slow R.kit) (hB : 0 < B)
local notation "a" => (fun r : ℝ => (Real.sqrt (β (m r)))⁻¹)
local notation "t" => WilsonPositionThermometerReading.reading F J K

include F prior measured pace hB in
/-- The signed cutoff source can be an actual moving lift of the oriented
star. Only its measured continuum limit is used to identify the field. -/
theorem compared {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch H) {C η : ℝ} (e : η < 1)
    (offer : ℝ → (ℕ × ℕ) → ℂ)
    (hears : ∀ᶠ r in trail, Tendsto (offer r) (U : Filter (ℕ × ℕ))
      (𝓝 (WilsonPositionThermometerReading.tested F J K r)))
    (first : ℝ → (ℕ × ℕ) → ℝ) (row : ℝ → ℝ)
    (cut : ∀ᶠ r in trail, Tendsto (first r) (U : Filter (ℕ × ℕ)) (𝓝 (row r)))
    (slope : Tendsto row trail (𝓝 c))
    (book : charged (R:=R) hG (B:=B) U C η offer first) :
    Tendsto (fun r => t r / a r) trail (𝓝 1) ∧ Coupling G t := by
  have link := Trace.Pilot.wilson_link F hG bliss.budgets bliss.keen bliss.lies
  have funded := WilsonPositionThermometerRunning.calendar F U prior β measured hG pace hB _ link
  have ae : 0 < 1-η := sub_pos.mpr e
  have continuum : ∀ᶠ r in trail,
      |a r^7 * (WilsonPositionThermometerReading.tested F J K r).re - row r*(a r)^8| ≤ C*(a r)^((9:ℝ)-η) := by
    filter_upwards [funded.positive, hears, cut, book] with r hp heard fin cost
    have temp : Tendsto (temperature (R := R) hG (B := B) r) (U : Filter (ℕ × ℕ)) (𝓝 (a r)) :=
      ((Real.continuous_sqrt.tendsto _).comp (measured (m r))).inv₀ (inv_pos.mp hp).ne'
    have full := Complex.continuous_re.continuousAt.tendsto.comp heard
    exact le_of_tendsto_of_tendsto (((temp.pow 7).mul full |>.sub (fin.mul (temp.pow 8))).abs)
      (tendsto_const_nhds.mul (((Real.continuous_rpow_const (q := (9 : ℝ)-η) (by linarith)).tendsto _).comp temp))
      cost
  have error : ∀ᶠ r in trail, |t r/a r-row r/c| ≤ (C*(a r)^((1 : ℝ)-η))/|c| := by
    filter_upwards [funded.positive, continuum] with r hp cost
    have exactPower : (a r)^((9:ℝ)-η) = (a r)^8*(a r)^((1:ℝ)-η) := by
      rw [show (9:ℝ)-η = (8:ℝ)+(1-η) by ring, Real.rpow_add hp]
      norm_num
    have factor : (a r)^7*(WilsonPositionThermometerReading.tested F J K r).re - row r*(a r)^8 =
        c*(a r)^8*(t r/a r-row r/c) := by
      rw [← WilsonPositionThermometerReading.calibrated_denominator F J K]
      field_simp [hp.ne',K.fresh.ne]
    rw [factor, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hp.le 8), exactPower] at cost
    apply (le_div_iff₀ (abs_pos.mpr K.fresh.ne)).2
    apply le_of_mul_le_mul_right _ (pow_pos hp 8)
    calc |t r/a r-row r/c| * |c| * (a r)^8 = |c| * (a r)^8 * |t r/a r-row r/c| := by ring
         _ ≤ C*((a r)^8*(a r)^((1 : ℝ)-η)) := cost
         _ = C*(a r)^((1 : ℝ)-η)*(a r)^8 := by ring
  have vanish : Tendsto (fun r => (a r)^((1 : ℝ)-η)) trail (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow ae.ne'] using
      ((Real.continuous_rpow_const ae.le).tendsto (0 : ℝ)).comp (funded.conforms hG)
  have spent : Tendsto (fun r => (C*(a r)^((1 : ℝ)-η))/|c|) trail (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (tendsto_const_nhds (x := C) |>.mul vanish).div_const |c|
  have err : Tendsto (fun r => t r/a r-row r/c) trail (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [error, (tendsto_order.mp spent).2 _ ep] with r paid target
    simpa only [Real.dist_eq,sub_zero] using paid.trans_lt target
  have firstLimit : Tendsto (fun r => row r/c) trail (𝓝 1) := by
    simpa only [div_self K.fresh.ne] using slope.div_const c
  have signed : Tendsto (fun r => t r/a r) trail (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using err.add firstLimit
  exact ⟨signed, WilsonPositionThermometerRunning.original F U prior β measured hG pace hB bliss J K signed⟩

include F prior measured pace hB in
theorem from_cutoff {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch H) {C η : ℝ} (e : η < 1)
    (offer : ℝ → (ℕ × ℕ) → ℂ)
    (hears : ∀ᶠ r in trail, Tendsto (offer r) (U : Filter (ℕ × ℕ))
      (𝓝 (WilsonPositionThermometerReading.tested F J K r)))
    (book : rawPrice (R:=R) K hG (B:=B) U C η offer) :
    Tendsto (fun r => t r/a r) trail (𝓝 1) ∧ Coupling G t :=
  compared F J K hG U prior β measured pace hB bliss e offer hears (fun _ _ => c) (fun _ => c)
    (Eventually.of_forall fun _ => tendsto_const_nhds) tendsto_const_nhds book

/-- The genuine finite signed detector on an auxiliary Wilson mesh. -/
def firstRow (W : Initialize G) (mesh : ℝ → XSpace.Mesh) (r : ℝ) : ℝ :=
  (PowerSeries.coeff 1 (Rose.Detector W K (mesh r))).re

include F prior measured pace hB in
theorem from_program {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch H) {C η : ℝ} (e : η < 1)
    (offer : ℝ → (ℕ × ℕ) → ℂ)
    (hears : ∀ᶠ r in trail, Tendsto (offer r) (U : Filter (ℕ × ℕ))
      (𝓝 (WilsonPositionThermometerReading.tested F J K r)))
    (W : Initialize G) (mesh : ℝ → XSpace.Mesh) (geometry : Tendsto mesh trail Front)
    (book : charged (R:=R) hG (B:=B) U C η offer (fun r _ => firstRow K W mesh r)) :
    Tendsto (fun r => t r/a r) trail (𝓝 1) ∧ Coupling G t := by
  apply compared F J K hG U prior β measured pace hB bliss e offer hears
    (fun r _ => firstRow K W mesh r) (firstRow K W mesh) (Eventually.of_forall fun _ => tendsto_const_nhds)
    _ book
  exact Complex.continuous_re.continuousAt.tendsto.comp ((Rose.diagnosed W K hG).comp geometry)

include F prior measured pace hB in
theorem original {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch H) {C η : ℝ} (e : η < 1)
    (book : price J K hG (B := B) U C η) :
    Tendsto (fun r => t r / a r) trail (𝓝 1) ∧ Coupling G t :=
  from_cutoff F J K hG U prior β measured pace hB bliss e _
    ((show ∀ᶠ r : ℝ in trail, 0 < r from self_mem_nhdsWithin).mono
      fun r hr => WilsonPositionThermometerFinite.signed F J r K hG prior hr) book

end YM.Integration.WilsonPositionThermometerSevenFaceRate
