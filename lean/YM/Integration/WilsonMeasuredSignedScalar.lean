import YM.Integration.WilsonMeasuredScalarRegular
import YM.Integration.WilsonMeasuredOwnerReserve

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedScalar
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

/-- The actual signed numerator and its independently filed field can be
compared in every earlier original conditional after retaining one explicit
hard numerator with its own original partners. -/
theorem original (y:Site (R.family.side i per)) (h:Coefficient F (R.family.side i per))
    (fmt:h.Format y R.family.params W) {M:ℝ} (bill:h.remBound y W κ M)
    (actual filed:Config G (R.family.side i per)→ℂ)
    (represented : ∀ U,h.density y S W U=actual U-((W).eval U:ℂ)*filed U) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=N)
      (fun U=>actual U/((W).eval U:ℂ)-filed U-account h W U/((W).eval U:ℂ))
      (‖h.x 0‖+M) ∧
    (∀ U,h.density y S W U-(soft h).density y S P U=account h W U) ∧
    ∀ U,account h W U≠0 → ∃j,h.forced j U≠0 ∧ y∈((P).activities.forced j).support ∧
      ∃z,z∈((P).activities.forced j).inventory ∧ z∈flags (P).p.threshold U :=by
  obtain ⟨point,owners,-⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course started live
  have eq : (W).eval=(P).eval:=(QuadraticLocal.Advent.later R π Γ Ψ course started live).view
  obtain ⟨_,_,split,flags⟩:=WilsonMeasuredOnlyHard.original h P W point eq owners S R.family.params y κ M fmt bill
  have form:=WilsonMeasuredCoefficientTransport.formats h P W point owners fmt
  have paid:=WilsonMeasuredCoefficientTransport.rent h P W point owners bill
  refine ⟨?_,fun U=>sub_eq_iff_eq_add.mpr ((split U).trans (add_comm ..)),flags⟩
  have same :
      (fun U=>actual U/((W).eval U:ℂ)-filed U-account h W U/((W).eval U:ℂ))=
        h.exponentialEntry y S P :=by
    funext U
    have whole:=split U
    rw [represented U,density,eq] at whole
    have nz : ((P).eval U:ℂ)≠0:=by exact_mod_cast (RG02.Actual.eval_pos R.makes.wilson live U).ne'
    rw [eq]
    field_simp [nz]
    linear_combination whole
  rw [same]
  exact WilsonMeasuredScalarRegular.original R simple live h y form paid

end YM.Integration.WilsonMeasuredSignedScalar
