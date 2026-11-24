import YM.Integration.WilsonPhysicalMarkedDefectStoredGallery
import YM.Integration.WilsonMasterCoordinatePrice
import YM.RG02.Actual.Selected

/-! On the selected degree-h reporting coefficient at its actual interior
scale, expose the regulated, dressed primary at the measured coupling. The
old regular table and the whole original compatible forced sum remain on
their actual addresses and physical vacuum. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.StoredInterior

open Function Finset Lattice Wilson RG Push Source Labels
open Extra.Histories Pert.Asymptotics RG16 RG16.Literal Trace.Physical.GermGraph
open scoped Classical BigOperators

variable {G : Gauge} (C : Family G) (N p h b : ℕ)
local notation "F" => (C.labels.level h)
local notation "A" => (C.path.rep N p b)
local notation "Qh" => (store C h p b)
local notation "g" => regulatorRun C N p b

def amplitude (Q : Qh) (j : (F).Index) : ℂ := (gMap C N p h b ((F).core Q.x)) j

def basis (j : (F).Index) (U : Config G (C.side b p)) : ℂ :=
  (g^((F).grades j).2 : ℝ)⁻¹ • (C.localSection h).places (Pi.single j 1) 0 U

def fitted (Q : Qh) (U : Config G (C.side b p)) : ℂ :=
  ∑ j : (F).Index, amplitude C N p h b Q j * basis C N p h b j U

def failed (Q : Qh) (U : Config G (C.side b p)) : ℂ :=
  if Healthy (A).p.threshold ((C.localSection h).footprint 0) U then 0 else -fitted C N p h b Q U

/-- This is the physically divided *complete* original forced invoice; a
pointwise division of the individually priced activities is not required. -/
def hard (Q : Qh) (U : Config G (C.side b p)) : ℂ :=
  ((Real.exp ((A).exponent U) : ℝ) : ℂ) * (∑' z, Q.marked A z U) / ((A).eval U : ℂ)

theorem core_le (v : (F).Coeff) : (F).coeffSize ((F).core v) ≤ (F).coeffSize v := by
  apply sum_le_sum
  intro j _
  by_cases hj : j = 0
  · subst j
    simp [Labels.Frame.core]
  · simp [Labels.Frame.core,Function.update_of_ne hj]

theorem price (law : C.Makes) (hb : b ≤ N) (Q : Qh) {fee : ℝ} (paid : (F).coeffSize Q.x ≤ fee) :
    ∑ j : (F).Index, ‖amplitude C N p h b Q j‖ ≤
      (2:ℝ)^(Finset.univ.sup (fun j : (F).Index => ((F).grades j).2))*fee :=
  (WilsonMasterCoordinatePrice.positive_grade law N p h b hb ((F).core Q.x)).trans
    (mul_le_mul_of_nonneg_left ((core_le C h _).trans paid) (by positivity))

theorem primary (law : C.Makes) (hb : b ≤ N) (Q : Qh) (U : Config G (C.side b p)) :
    (C.localSection h).places ((F).scaled (A).p.threshold⁻¹ ((F).core Q.x)) 0 U =
      fitted C N p h b Q U := by
  let v := (F).scaled (A).p.threshold⁻¹ ((F).core Q.x)
  let ev : (F).Coeff →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (entry (S:=(C.localSection h).stencil) (expandAt 0 U))).toLinearMap.comp
      (C.localSection h).evalC
  have expand : (∑ j, v j • Pi.single j (1:ℂ)) = v := by
    ext j
    simp [Pi.smul_apply,Pi.single_apply]
  have ng : g ≠ 0 := (g_pos law hb).ne'
  change ev v = _
  nth_rw 1 [← expand]
  simp only [map_sum,map_smul,smul_eq_mul,fitted]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((((A).p.threshold⁻¹)^(((F).grades j).2) : ℝ) : ℂ) * ((F).core Q.x) j *
      (C.localSection h).places (Pi.single j 1) 0 U = _
  rw [amplitude,gMap,Labels.Frame.scaled_apply,basis,Complex.real_smul]
  push_cast
  rw [div_pow,inv_pow]
  have gc : (g : ℂ) ≠ 0 := by exact_mod_cast ng
  have tc : (((A).p.threshold : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (A).p.threshold_pos.ne'
  field_simp [gc,tc]

/-- This equality keeps every field, every incoming complex phase, the
literal masked receiving supports and the entire original hard gas. -/
theorem resolved (law : C.Makes) (hb : b ≤ N) (Q : Qh) (U : Config G (C.side b p)) :
    Q.density 0 (C.localSection h) A U / ((A).eval U : ℂ) =
      Q.x 0 + fitted C N p h b Q U + failed C N p h b Q U +
        (∑' i, Q.maskedTerm A i U) + hard C N p h b Q U := by
  have nz : ((A).eval U : ℂ) ≠ 0 := by
    exact_mod_cast (RG02.Actual.eval_pos law.wilson hb U).ne'
  have masked_primary : masked (A).p.threshold ((C.localSection h).footprint 0)
      ((C.localSection h).places ((F).scaled (A).p.threshold⁻¹ ((F).core Q.x)) 0) U =
        fitted C N p h b Q U + failed C N p h b Q U := by
    by_cases ok : Healthy (A).p.threshold ((C.localSection h).footprint 0) U
    · rw [masked_eq _ _ _ _ ok,failed,if_pos ok,add_zero,primary C N p h b law hb]
    · rw [masked_ne _ _ _ _ ok,failed,if_neg ok,add_neg_cancel]
  unfold Coefficient.density Coefficient.exponentialEntry hard
  rw [masked_primary,add_div,mul_div_cancel_left₀ _ nz]
  ring

/-- The actual `Q` therefore has both the current calibrated primary price
and the complete original regular and divided forced allowance at its
existing fee. The forced allowance below applies to its original slots,
not to a pointwise quotient at a rough field. -/
theorem recorded (law : C.Makes) (hb : b ≤ N) (Q : Qh) {fee : ℝ}
    (admitted : reads h N p b Q fee) (paid : (F).coeffSize Q.x ≤ fee) :
    Q.Format 0 C.params A ∧ Q.remBound 0 A (safety C b) fee ∧
    (∑ j : (F).Index, ‖amplitude C N p h b Q j‖ ≤
      (2:ℝ)^(Finset.univ.sup (fun j : (F).Index => ((F).grades j).2))*fee) ∧
    ∀ U, Q.density 0 (C.localSection h) A U / ((A).eval U : ℂ) =
      Q.x 0 + fitted C N p h b Q U + failed C N p h b Q U +
        (∑' i, Q.maskedTerm A i U) + hard C N p h b Q U :=
  ⟨admitted.1,admitted.2,price C N p h b law hb Q paid,resolved C N p h b law hb Q⟩

end YM.Integration.WilsonPhysicalMarkedDefect.StoredInterior

