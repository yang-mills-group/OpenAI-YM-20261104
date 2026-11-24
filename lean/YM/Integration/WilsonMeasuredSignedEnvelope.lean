import YM.Integration.WilsonMeasuredSignedScalar

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedEnvelope
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Tree AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal.Advent
open Push Push.Local Push.PriceCompiler AnalyticBridge VerifiedReset RemainderComparison
open AllOrder.Transit WheelP PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pressure ConnectedActivityE6 Filter
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (simple : G.Simple)
variable {m N per k i : ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ a,Rep G (R.family.side a per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started : m ≤ i) (live : i ≤ N)
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "W" => (Ψ i)
local notation "P" => R.family.path.rep N per i
local notation "κ" => LocalComparison.forcedDivisor R.family i

include simple course started live

theorem original (y : Site (R.family.side i per)) (h : Coefficient F (R.family.side i per))
    (fmt : h.Format y R.family.params W) {M : ℝ} (paid : h.remBound y W κ M)
    (actual filed : Config G (R.family.side i per) → ℂ)
    (represented : ∀U, h.density y S W U=actual U-((W).eval U:ℂ)*filed U) :
    let rem := fun U=>actual U/((W).eval U:ℂ)-filed U-account h W U/((W).eval U:ℂ)
    Measurable rem ∧ ∀U,‖rem U‖≤‖h.x 0‖+M := by
  intro rem
  have physical := WilsonMeasuredSignedScalar.original R simple π Γ Ψ course started live y h fmt paid
    actual filed represented
  obtain ⟨point,owners,-⟩ := WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course started live
  have fit := WilsonMeasuredCoefficientTransport.formats h P W point owners fmt
  have L := WilsonMeasuredCoefficientTransport.rent h P W point owners paid
  have good := (R.makes.wilson.represents N per i live).good
  have measurable := (Coefficient.envelope S good (bill h y P L) (format h y P R.family.params fit)).meas
  have same : (W).eval=(P).eval := (QuadraticLocal.Advent.later R π Γ Ψ course started live).view
  have equal : rem=fun U=>(soft h).density y S P U/((P).eval U:ℂ) := by
    funext U
    have entire := physical.2.1 U
    rw [represented U,same] at entire
    have nz : ((P).eval U:ℂ)≠0 := by exact_mod_cast (RG02.Actual.eval_pos R.makes.wilson live U).ne'
    dsimp only [rem]
    rw [same]
    field_simp [nz]
    linear_combination entire
  refine ⟨equal ▸ measurable.div (Complex.continuous_ofReal.measurable.comp ((P).envelope good).meas),?_⟩
  simpa only [rem,actualTransport_base R.family R.makes live] using (physical.1 i le_rfl).1

end YM.Integration.WilsonMeasuredSignedEnvelope
