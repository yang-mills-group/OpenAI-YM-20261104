import YM.Integration.WilsonMeasuredOnlyHard
import YM.Integration.WilsonThermometerCompulsoryReturn
import YM.RG12.Canonical.Low

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredScalarRegular
open Function Filter MeasureTheory Lattice Wilson RG Labels Source Next.Foundations
open RG12 RG16 Extra.Histories PhysicalNext.Repeat.Legato
open WilsonPhysicalMarkedDefect.RegularProjection
open scoped Classical BigOperators
open private earlier from YM.Integration.WilsonThermometerCompulsoryReturn

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0

include simple

/-- The scalar section has only the unit. The whole signed regular field
therefore costs its one measured coordinate and its original remainder. -/
theorem point {n : Side} (P : Rep G n) (h : Coefficient F n) (y : Site n) {κ M : ℝ}
    (paid : h.remBound y P κ M) (U : Config G n) :
    ‖h.exponentialEntry y S P U‖ ≤ ‖h.x 0‖+M := by
  have core : (F).core h.x = 0 := by
    obtain ⟨z,hz⟩ := RG12.unit_spans simple C 0 0 (by decide) h.x
    have none : (F).core (unitVec F (C).path 0)=0 := by
      funext j
      by_cases hj : j=0 <;> simp [Labels.Frame.core,unitVec,Labels.Frame.e0,Function.update,hj]
    rw [hz,map_smul,none,smul_zero]
  have zero : masked P.p.threshold ((S).footprint y)
      ((S).places ((F).scaled P.p.threshold⁻¹ ((F).core h.x)) y) U=0 := by
    by_cases good : Healthy P.p.threshold ((S).footprint y) U
    · rw [masked_eq _ _ _ _ good,core,map_zero]
      change (S).evaluate 0 (expandAt y U)=0
      exact congr_fun (S).eval_linear.map_zero _
    · exact masked_ne _ _ _ _ good
  simpa only [Coefficient.exponentialEntry,zero,add_zero] using
    (norm_add_le (h.x 0) (∑'i,h.maskedTerm P i U)).trans
      (add_le_add le_rfl (ordinary h y P paid U))

/-- Every older conditional and its integrable cofactor on the actual
Wilson prior hear the full regular entry at the same price. -/
theorem original {N per i : ℕ} (live : i≤N) (h : Coefficient F ((C).side i per))
    (y : Site ((C).side i per)) {κ M : ℝ} (fit : h.Format y (hol G) ((C).path.rep N per i))
    (paid : h.remBound y ((C).path.rep N per i) κ M) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=N) (h.exponentialEntry y S ((C).path.rep N per i)) (‖h.x 0‖+M) := by
  let P := (C).path.rep N per i
  have law := (R.makes.wilson.represents N per i live).good
  have num := (Coefficient.envelope S law (bill h y P paid) (format h y P (hol G) fit)).meas
  have den := Complex.continuous_ofReal.measurable.comp (P.envelope law).meas
  have value : h.exponentialEntry y S P = fun U => (soft h).density y S P U/(P.eval U:ℂ) := by
    funext U
    have nz : (P.eval U:ℂ)≠0 := by exact_mod_cast (RG02.Actual.eval_pos R.makes.wilson live U).ne'
    rw [density,mul_div_cancel_left₀ _ nz]
  apply earlier R live
  · rw [show h.exponentialEntry y S ((C).path.rep N per i) = _ from value]
    exact num.div den
  · exact point R simple P h y paid

end YM.Integration.WilsonMeasuredScalarRegular
