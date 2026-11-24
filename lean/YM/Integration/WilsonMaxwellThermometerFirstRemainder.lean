import YM.Integration.WilsonMaxwellThermometerFirstInvoice

/-! At a fixed radius the signed constant can be removed by its own cutoff
limit. A vanishing error in the computed first coefficient costs only that
error times one power of the measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFirstRemainder
open Function Filter Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb Maxwell XSpace XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) {V : Store G}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} (A : ℝ → Group R.family 6)
    (K : Rose.Pick V) (W : Initialize G) (simple : G.Simple) (B : ℕ)
local notation "P" => WilsonPositionPrescribedFrame.positioned F J V
local notation "out" => WilsonPositionGradedThermometerHearing.offer F J V K A
local notation "c" => Rose.c_T K
local notation "first" => WilsonMaxwellThermometerFirstPosition.coefficient F J A K W simple B
local notation "g" => WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "a" => (fun r : ℝ => (Real.sqrt (arch.β (m r)))⁻¹)

/-- Relative error of the full signed integral after subtracting its finite
constant term and the full independently filed first coefficient. -/
def error (zero : ℝ → (ℕ × ℕ) → ℝ) (r : ℝ) (z : ℕ × ℕ) : ℝ :=
  ((out r z).re-zero r z)/g r z - (first r z).re

theorem original (pace : WilsonWindowReportingPace.Slow R.kit) (hB : 0<B)
    (bliss : Bliss F Y arch H) (book : Book (f:=f) (l:=Y) (H:=H) A J)
    (lead : Leading F J) (zero : ℝ→(ℕ×ℕ)→ℝ)
    (constantTerm : ∀ᶠ r in trail, Tendsto (zero r) (Y : Filter _) (𝓝
      (((Rose.test K).applyTo (WilsonPositionGradedThermometerGround.ground
        (WilsonPositionCorrectedCap.adjusted F J V A r))).re)))
    (paid : Tendsto (fun x : ℝ×(ℕ×ℕ) => error F J A K W simple B zero x.1 x.2)
      (trail.curry (Y : Filter _)) (𝓝 0)) :
    Coupling G (WilsonPositionThermometerReading.reading F P K) := by
  let l := Y.toFilter
  have phys := WilsonPositionGradedThermometerGround.original F J V K A book lead simple bliss.lies
  have link := Trace.Pilot.wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have funded := WilsonPositionThermometerRunning.calendar F Y bliss.lies arch.β bliss.keen.mintS
    simple pace hB _ link
  have before : ∀ᶠ r in trail, Tendsto (fun z => ((out r z).re-zero r z)/g r z) l
      (𝓝 ((WilsonPositionThermometerReading.tested F P K r).re / a r)) := by
    filter_upwards [phys,constantTerm,funded.positive] with r q free hp
    rw [q.1,Complex.zero_re] at free
    have t : Tendsto (g r) l (𝓝 (a r)) :=
      ((Real.continuous_sqrt.tendsto _).comp (bliss.keen.mintS (m r))).inv₀ (inv_pos.mp hp).ne'
    simpa [l,Pi.div_def,Function.comp_def] using
      ((Complex.continuous_re.continuousAt.tendsto.comp q.2).sub free).div t hp.ne'
  have independent := WilsonMaxwellThermometerFirstPosition.original F J A K W simple B hB bliss.lies book lead
  have full : Tendsto (fun x : ℝ×(ℕ×ℕ) => ((out x.1 x.2).re-zero x.1 x.2)/g x.1 x.2)
      (trail.curry l) (𝓝 c) := by
    simpa only [error,Function.comp_apply,sub_add_cancel,Complex.ofReal_re,zero_add] using
      paid.add (Complex.continuous_re.continuousAt.tendsto.comp independent)
  have observed : Tendsto (fun r => (WilsonPositionThermometerReading.tested F P K r).re / a r) trail (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [before,eventually_curry_iff.mp (Metric.tendsto_nhds.mp full _ (half_pos he))] with r inner price
    exact (le_of_tendsto (inner.dist (tendsto_const_nhds (x:=c))) (price.mono fun _ h => h.le)).trans_lt (half_lt_self he)
  apply WilsonPositionThermometerRunning.original F Y bliss.lies arch.β bliss.keen.mintS simple pace hB bliss P K
  have slope := observed.div_const c
  rw [div_self K.fresh.ne] at slope
  exact slope.congr fun r => by unfold WilsonPositionThermometerReading.reading; ring

end YM.Integration.WilsonMaxwellThermometerFirstRemainder
end
