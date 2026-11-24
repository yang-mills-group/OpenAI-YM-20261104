import YM.Integration.WilsonPositionProgramTrialAppointment
import YM.Integration.WilsonMaxwellThermometerKineticUpper

/-! The original measured fine coupling and the prescribed unit-tangent
thermometer, evaluated on the finite measured cohort at its actual ticket. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialKinetic
open Filter Set Function PowerSeries Lattice Wilson RG Source Extraction Table Spec
open Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register Climb
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Pert.Asymptotics
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionProgramTrialAppointment (Commission reading expense)
open WilsonMaxwellThermometerKineticCoordinate (printed ground)
open scoped Classical Topology
variable {G : Gauge} (Z : WilsonPrescription G) {R : Run G}
    {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (A : ℝ → Group R.family 6) {Y : Ultrafilter (ℕ × ℕ)}
    {H : (Bel R.family.book).Hierarchy} {arch : Trace.Terrace.Arch R.family}
    (simple : G.Simple) {B : ℕ} (hB : 0 < B) (fine index : ℝ → ℕ)
    (d : Fin 3 → ℕ) (cap : ∀ i, d i < 7) (C : ∀ r, Commission R d (fine r))
local notation "visits" => trail.curry (Y:Filter (ℕ × ℕ))
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J Z.store Z.criterion A
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "mesh" => WilsonMaxwellThermometerKineticFineRose.regulator Z index
local notation "u" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index
local notation "linear" => WilsonPositionRawDetector.linear Z

def trial (w : ℝ × (ℕ × ℕ)) : ℝ :=
  reading R d (C w.1) w.2.1 w.2.2 Z (mesh w) 1 (u w)

def change (w : ℝ × (ℕ × ℕ)) : ℝ :=
  expense R d (C w.1) w.2.1 w.2.2 cap Z (mesh w) 1 (u w)

local notation "finite" => trial Z fine index d C
local notation "bill" => change Z fine index d cap C

def difference (w : ℝ × (ℕ × ℕ)) : ℝ := (out w.1 w.2).re - finite w + bill w
local notation "δ" => difference Z F J A fine index d cap C

theorem measured (w : ℝ × (ℕ × ℕ)) :
    finite w - printed Z (mesh w) 1 (u w) = bill w :=
  WilsonPositionProgramTrialAppointment.original R d (C w.1) _ _ cap Z _ _ _

theorem exact (w : ℝ × (ℕ × ℕ)) (live : u w ≠ 0) :
    thermal w.1 w.2 / u w =
      (δ w / u w + ground Z (mesh w) / u w) / Rose.c_T Z.criterion + linear (mesh w) := by
  rw [WilsonMaxwellThermometerKineticSlope.exact_report Z F J A (mesh w) w.1 w.2 live]
  rw [difference, ← measured Z fine index d cap C w]
  ring

include hB in
/-- The independent response on the appointed kinetic clock. The original
trial ground is included in the filed difference prior to taking this limit. -/
theorem independent (schedule : enrolled) (prior : (Y:Filter _) ≤ f.fuse) :
    Tendsto (fun w => (finite w - bill w) / (Rose.c_T Z.criterion * u w)) visits (𝓝 1) := by
  obtain ⟨cofinal,live⟩ := WilsonMaxwellThermometerKineticFineRose.appointed (R:=R) (f:=f)
    Z simple hB fine index schedule prior
  have slope := Complex.continuous_re.continuousAt.tendsto.comp
    ((Rose.xc Z.scheme Z.criterion simple).comp cofinal)
  have cash := cofinal.eventually (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2
  refine slope.congr' ?_
  filter_upwards [live,cash] with w hw paid
  change linear (mesh w) = _
  rw [← measured Z fine index d cap C w, sub_sub_cancel,
    WilsonMaxwellThermometerKineticSlope.slope,
    WilsonMaxwellThermometerKineticPanel.paid_ground Z (mesh w) paid.1, zero_add]
  field_simp [hw.1.ne', Z.criterion.fresh.ne]

include hB in
theorem observed_iff (schedule : enrolled) (prior : (Y:Filter _) ≤ f.fuse) :
    Tendsto (fun w => thermal w.1 w.2 / u w) visits (𝓝 1) ↔
      Tendsto (fun w => δ w / u w) visits (𝓝 0) := by
  obtain ⟨cofinal,live⟩ := WilsonMaxwellThermometerKineticFineRose.appointed (R:=R) (f:=f)
    Z simple hB fine index schedule prior
  have slope : Tendsto (fun w => linear (mesh w)) visits (𝓝 1) :=
    Complex.continuous_re.continuousAt.tendsto.comp ((Rose.xc Z.scheme Z.criterion simple).comp cofinal)
  have cash := cofinal.eventually (Z.store.nested_solution Z.scheme 6 Cirrus.frontier).2
  have joint : ∀ᶠ w in visits, thermal w.1 w.2 / u w =
      (δ w / u w) / Rose.c_T Z.criterion + linear (mesh w) := by
    filter_upwards [live,cash] with w hw paid
    rw [exact Z F J A fine index d cap C w hw.1.ne',
      WilsonMaxwellThermometerKineticPanel.paid_ground Z (mesh w) paid.1, zero_div, add_zero]
  constructor
  · intro h
    have net := (h.sub slope).mul_const (Rose.c_T Z.criterion)
    rw [sub_self,zero_mul] at net
    refine net.congr' ?_
    filter_upwards [joint] with w h
    rw [h,add_sub_cancel_right,div_mul_cancel₀ _ Z.criterion.fresh.ne]
  · intro h
    have net := (h.div_const (Rose.c_T Z.criterion)).add slope
    rw [zero_div,zero_add] at net
    exact net.congr' (joint.mono fun _ hw => hw.symm)

include hB in
theorem original (pace : WilsonWindowReportingPace.Slow R.kit)
    (bliss : Bliss F Y arch H) (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
    (schedule : enrolled) (paid : Tendsto (fun w => δ w / u w) visits (𝓝 0)) :
    (∀ ε>0, ∀ᶠ r in trail, ∀ N per, fine r ≤ N →
      |regulatorRun R.family N per (fine r) / WilsonMaxwellThermometerKineticLog.unit G r - 1| < ε) ∧
    Tendsto (fun r => θ r / WilsonMaxwellThermometerKineticLog.unit G r) trail (𝓝 1) ∧ Coupling G θ := by
  obtain ⟨_,live⟩ := WilsonMaxwellThermometerKineticFineRose.appointed (R:=R) (f:=f)
    Z simple hB fine index schedule bliss.lies
  have first := (observed_iff Z F J A simple hB fine index d cap C schedule bliss.lies).mpr paid
  have running := (WilsonMaxwellThermometerKineticRunning.original Z F J A simple pace hB bliss book lead u
    (live.mono fun _ hw => hw.1) first
    (WilsonMaxwellThermometerKineticAppointment.original R simple hB Z schedule f Y bliss.lies)).2
  exact ⟨fun _ ep => WilsonMaxwellThermometerKineticUpper.original R simple hB pace Z schedule ep,
    WilsonMaxwellThermometerKineticLog.running simple running,running⟩

end YM.Integration.WilsonPositionProgramTrialKinetic
end
