import YM.Integration.WilsonMaxwellThermometerKineticPanel

/-! Restoring the original Wilson running law after the common finite clock is eliminated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticRunning
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (A : ℝ → Group R.family 6)
    {Y : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} (simple : G.Simple) {B : ℕ}
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "a" => (fun r : ℝ => (Real.sqrt (arch.β (m r)))⁻¹)

/-- The additional signed clock identification yields the original leading coefficient;
the density comparison alone need only identify its common internal variable. -/
theorem original (pace : WilsonWindowReportingPace.Slow R.kit) (hB : 0<B)
    (bliss : Bliss F Y arch H) (book : Book (f:=f) (l:=Y) (H:=H) A J) (lead : Leading F J)
    (axis : ℝ×(ℕ×ℕ) → ℝ) (live : ∀ᶠ w in visits, 0 < axis w)
    (panel : Tendsto (fun w => thermal w.1 w.2 / axis w) visits (𝓝 1))
    (clock : Tendsto (fun w => axis w / g w.1 w.2) visits (𝓝 1)) :
    Tendsto (fun r => θ r / a r) trail (𝓝 1) ∧ Coupling G θ := by
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have funded := WilsonPositionThermometerRunning.calendar F Y bliss.lies arch.β bliss.keen.mintS
    simple pace hB _ link
  have before : ∀ᶠ r in trail, Tendsto (fun z => thermal r z / g r z) (Y:Filter _) (𝓝 (θ r / a r)) := by
    filter_upwards [WilsonPositionRawCutoff.measured Z F J lead A book simple bliss.lies,funded.positive]
      with r heard hr
    have cash : Tendsto (g r) (Y:Filter _) (𝓝 (a r)) :=
      ((Real.continuous_sqrt.tendsto _).comp (bliss.keen.mintS (m r))).inv₀ (inv_pos.mp hr).ne'
    exact heard.div cash hr.ne'
  have full : Tendsto (fun w => thermal w.1 w.2 / g w.1 w.2) visits (𝓝 1) := by
    have both := panel.mul clock
    rw [one_mul] at both
    refine both.congr' ?_
    filter_upwards [live] with w hw
    field_simp [hw.ne']
  have landed : Tendsto (fun r => θ r / a r) trail (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [before,eventually_curry_iff.mp (Metric.tendsto_nhds.mp full _ (half_pos he))]
      with r hv hk
    exact (le_of_tendsto (hv.dist (tendsto_const_nhds (x:=(1:ℝ)))) (hk.mono fun _ h=>h.le)).trans_lt
      (half_lt_self he)
  refine ⟨landed,?_⟩
  exact WilsonPositionThermometerRunning.original F Y bliss.lies arch.β bliss.keen.mintS simple
    pace hB bliss (WilsonPositionPrescribedFrame.positioned F J Z.store) Z.criterion landed

end YM.Integration.WilsonMaxwellThermometerKineticRunning
