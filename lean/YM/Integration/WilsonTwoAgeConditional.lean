import YM.Integration.WilsonTwoAgePath

/-! The connected reading is the difference of three marked integrals on
the same finite Wilson history, divided by the same positive vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTwoAgeConditional
open Lattice RG Tree Wilson MeasureTheory RGComparison.Core16 RGComparison.Core16.Descent
open WilsonTwoAgePath
open scoped BigOperators Classical
variable {G : Gauge} {n c f : Side} (S : StepData c f) (T : Forest S.ratio) (D : Descent n f)
local notation "P" => Descent.push S T D

def average (β : ℕ → ℝ) (F : Config G f → ℝ) (V : Config G c) : ℝ :=
  ((P).vacuum β V)⁻¹ * S.push (β 1) (fun U => D.vacuum (upβ β) U * F U) V

def reading (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ) (V : Config G c) : ℝ :=
  (∑ t, ∫ x, WilsonTwoAgePath.integrand S T D β t A B V x ∂(P).measure G) /
    (∑ t, ∫ x, WilsonTwoAgePath.integrand S T D β t 1 1 V x ∂(P).measure G)

private theorem vacancy (β : ℕ → ℝ) (V : Config G c) :
    joint S D β (1 : Config G n → ℝ) 1 V = (P).vacuum β V := by
  unfold joint
  simp only [Pi.one_apply, one_mul, weighted_unit]
  rfl

theorem normalized (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (ha : Continuous A) (ga : GaugeInvariant A) (hb : Continuous B) (gb : GaugeInvariant B)
    (V : Config G c) :
    reading S T D β A B V = ((P).vacuum β V)⁻¹ * joint S D β A B V := by
  have a := WilsonTwoAgePath.original S T D h β A B ha ga hb gb V
  have d := WilsonTwoAgePath.original S T D h β 1 1 continuous_const (fun _ _=>rfl)
    continuous_const (fun _ _=>rfl) V
  rw [vacancy S T D β V] at d
  rw [a,d,mul_comm _ ((P).scalar G β * _),←div_eq_mul_inv,mul_div_mul_left _ _ (scalar_pos G (P) β).ne']
  rfl

theorem measured (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (ha : Continuous A) (ga : GaugeInvariant A) (hb : Continuous B) (gb : GaugeInvariant B)
    (V : Config G c) :
    average S T D β (fun U=>B U * D.conditioned (upβ β) A U) V = reading S T D β A B V := by
  rw [normalized S T D h β A B ha ga hb gb V]
  unfold average joint
  have swap (U : Config G f) : D.vacuum (upβ β) U * (B U * D.conditioned (upβ β) A U) =
      B U * D.weighted (upβ β) A U := by
    rw [mul_left_comm]
    exact congrArg (B U * ·) (uncondition (upβ β) h.2 U A)
  simp_rw [swap]

theorem connected (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (ha : Continuous A) (ga : GaugeInvariant A) (hb : Continuous B) (gb : GaugeInvariant B)
    (V : Config G c) :
    average S T D β (fun U=>B U * D.conditioned (upβ β) A U) V -
        average S T D β (D.conditioned (upβ β) A) V * average S T D β B V =
      reading S T D β A B V - reading S T D β A 1 V * reading S T D β 1 B V := by
  have left := measured S T D h β A 1 ha ga continuous_const (fun _ _=>rfl) V
  simp only [Pi.one_apply,one_mul] at left
  have unit (U : Config G f) : D.conditioned (upβ β) (1 : Config G n → ℝ) U = 1 := by
    rw [conditioned,weighted_unit,smul_eq_mul,inv_mul_cancel₀ (positive _ h.2 U).ne']
  have right := measured S T D h β 1 B continuous_const (fun _ _=>rfl) hb gb V
  simp_rw [unit,mul_one] at right
  rw [measured S T D h β A B ha ga hb gb V,left,right]

end YM.Integration.WilsonTwoAgeConditional
end
