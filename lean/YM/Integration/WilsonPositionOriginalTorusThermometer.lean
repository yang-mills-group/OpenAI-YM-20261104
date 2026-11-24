import YM.Integration.WilsonPositionThermometerSevenFaceRate
import YM.Integration.WilsonSeparatedOriginalThermometerDetectorMesh

/-! The signed independent thermometer on the very torus and reporting
scale of the physical cutoff. The two regulated copies have the original
Wilson order of limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalTorusThermometer

open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open XSpace XSpace.Normalize XSpace.Cirrus
open scoped Topology
open WilsonSeparatedOriginalThermometerDetectorMesh

private theorem inner {I : Type*} (U : Ultrafilter I) (Q : ℝ → I → ℝ) {c : ℝ}
    (ordered : Tendsto (fun z : ℝ × I => Q z.1 z.2) (trail.curry (U : Filter I)) (𝓝 c)) :
    ∃ q : ℝ → ℝ, (∀ᶠ r in trail, Tendsto (Q r) (U : Filter I) (𝓝 (q r))) ∧ Tendsto q trail (𝓝 c) := by
  let q (r : ℝ) := limUnder (U : Filter I) (Q r)
  have fibre : ∀ᶠ r in trail, Tendsto (Q r) (U : Filter I) (𝓝 (q r)) := by
    filter_upwards [eventually_curry_iff.mp (Metric.tendsto_nhds.mp ordered 1 zero_lt_one)] with r bounded
    apply tendsto_nhds_limUnder
    obtain ⟨x, _, near⟩ := (isCompact_closedBall c 1).ultrafilter_le_nhds (U.map (Q r))
      (le_principal_iff.mpr (bounded.mono fun _ b => b.le))
    exact ⟨x,near⟩
  refine ⟨q,fibre,Metric.tendsto_nhds.mpr fun ε pos => ?_⟩
  filter_upwards [fibre, eventually_curry_iff.mp (Metric.tendsto_nhds.mp ordered _ (half_pos pos))] with r converge tight
  exact (le_of_tendsto (converge.dist (tendsto_const_nhds (x:=c))) (tight.mono fun _ h => h.le)).trans_lt
    (half_lt_self pos)

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) {V : Store G} (K : Rose.Pick V)
    (hG : G.Simple) {B : ℕ} (W : Initialize G)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B

def actualRow (r : ℝ) (z : ℕ × ℕ) : ℝ :=
  (PowerSeries.coeff 1 (Rose.Detector W K
    (chart R (m r) z.2 (spacing R hG B r) (positive R hG B r)))).re

theorem original (pace : WilsonWindowReportingPace.Slow R.kit) (hB : 0 < B)
    {l : Ultrafilter (ℕ × ℕ)} {arch : Trace.Terrace.Arch R.family}
    {Y : (Bel R.family.book).Hierarchy} (bliss : Bliss F l arch Y) {C η : ℝ} (e : η < 1)
    (offer : ℝ → (ℕ × ℕ) → ℂ)
    (hears : ∀ᶠ r in trail, Tendsto (offer r) (l : Filter (ℕ × ℕ))
      (𝓝 (WilsonPositionThermometerReading.tested F J K r)))
    (book : WilsonPositionThermometerSevenFaceRate.charged (R:=R) hG (B:=B) l C η offer
      (actualRow (R:=R) K hG (B:=B) W)) :
    Coupling G (WilsonPositionThermometerReading.reading F J K) := by
  have original := WilsonSeparatedOriginalThermometerDetectorMesh.actual R hG B hB f
    (l : Filter (ℕ × ℕ)) bliss.lies W K
  obtain ⟨q,cut,slope⟩ := inner l (actualRow (R:=R) K hG (B:=B) W)
    (Complex.continuous_re.continuousAt.tendsto.comp original)
  exact (WilsonPositionThermometerSevenFaceRate.compared F J K hG l bliss.lies arch.β bliss.keen.mintS
    pace hB bliss e offer hears _ q cut slope book).2

end YM.Integration.WilsonPositionOriginalTorusThermometer
