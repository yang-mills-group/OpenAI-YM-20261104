import YM.TraceExtension.Atlas.Global
import YM.Integration.WilsonPhysicalCutoffCurrency
import YM.Integration.WilsonPositionThermometerReading

/-! Running at the original reporting date, with beta measured on the same
cutoff filter as the physical fields. -/
set_option autoImplicit false
set_option format.width 160
noncomputable section
namespace YM.Integration.WilsonPositionThermometerRunning
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (U : Ultrafilter (ℕ × ℕ)) (prior : (U : Filter (ℕ × ℕ)) ≤ f.fuse)
  (β : ℕ → ℝ)
  (measured : ∀ j, Tendsto (fun z : ℕ × ℕ => R.family.path.β z.1 z.2 j)
    (U : Filter (ℕ × ℕ)) (𝓝 (β j)))
  (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B
local notation "a" => (fun r : ℝ => (Real.sqrt (β (m r)))⁻¹)

include F prior measured pace hB in
/-- The beta limits are those of the very cutoff filter used for reporting. -/
theorem calendar (g : ℝ → ℝ) (hg : Coupling G g) : Coupling G a := by
  obtain ⟨arch, steep⟩ := Trace.Terrace.styling prior F.room.cutoff
  have same : arch.β = β := funext fun j =>
    tendsto_nhds_unique (steep.mintS j) (measured j)
  have price := Trace.Terrace.gamut prior F.room.cutoff steep hG
  have bp (j : ℕ) : 0 < β j := same ▸ Trace.Terrace.measured prior F.room.cutoff steep j
  rw [same] at price
  have cofinal := WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB
  have forecast := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  have measuredRate : Tendsto (fun r => β (m r) * (g r)^2) trail (𝓝 1) := by
    have both := (price.comp cofinal).mul forecast
    rw [one_mul] at both
    apply both.congr fun r => ?_
    have positive := zero_lt_one.trans (R.family.path.levels.fits.delayed (m r))
    change (β (m r) / R.family.path.levels.clock.hatBeta (m r)) *
      (R.family.path.levels.clock.hatBeta (m r) * (g r)^2) = _
    field_simp [positive.ne']
  refine ⟨Eventually.of_forall (fun r => inv_pos.mpr (Real.sqrt_pos.mpr (bp (m r)))), ?_⟩
  have running := hg.running.div measuredRate one_ne_zero
  rw [div_one] at running
  apply running.congr'
  filter_upwards [hg.positive] with r hr
  change LogV r * (g r)^2 / (β (m r) * (g r)^2) = LogV r * (Real.sqrt (β (m r)))⁻¹ ^ 2
  rw [inv_pow, Real.sq_sqrt (bp (m r)).le]
  field_simp [(bp (m r)).ne', hr.ne']

include F prior measured pace hB in
/-- The signed assay uses the actual cubic and two quadratic fields. Applying it
to the chosen positioned frame gives the coupling for the separated profile. -/
theorem original {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch H) (J : ℝ → PhysMS.tower S)
    {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)
    (assay : Tendsto (fun r => WilsonPositionThermometerReading.reading F J K r / a r)
      trail (𝓝 1)) :
    Coupling G (WilsonPositionThermometerReading.reading F J K) := by
  let t := WilsonPositionThermometerReading.reading F J K
  have hg := wilson_link F hG bliss.budgets bliss.keen bliss.lies
  have funded := calendar F U prior β measured hG pace hB (wilson arch) hg
  have ratio : Tendsto (fun r => t r / a r) trail (𝓝 1) := assay
  constructor
  · filter_upwards [funded.positive, (tendsto_order.mp ratio).1 0 zero_lt_one] with r hp hr
    exact (div_pos_iff_of_pos_right hp).mp hr
  · have multiplied := funded.running.mul (ratio.pow 2)
    rw [one_pow, mul_one] at multiplied
    apply multiplied.congr'
    filter_upwards [funded.positive] with r hr
    change LogV r * (a r)^2 * (t r / a r)^2 = LogV r * (t r)^2
    have root_pos := inv_pos.mp hr
    field_simp [root_pos.ne']

end YM.Integration.WilsonPositionThermometerRunning
