import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Three distinct retained letters, with one original quiet normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatResponseDerivative

def term (z d:ℂ)(t:ℂ):ℂ:=z+t*d

private theorem row (z d:ℂ):HasDerivAt (term z d) d 0:=by
  have h:HasDerivAt (fun t:ℂ=>z+t*d) (0+1*d) (0:ℂ):=
    (hasDerivAt_const (0:ℂ) z).add ((hasDerivAt_id (0:ℂ)).mul_const d)
  rw [zero_add,one_mul] at h
  exact h

private theorem ratio (n dn z dz:ℂ)(hz:z≠0):
    HasDerivAt (fun t:ℂ=>term n dn t/term z dz t) ((dn*z-n*dz)/z^2) 0:=by
  have h:term z dz 0≠0:=by simpa [term] using hz
  have d:HasDerivAt (fun t:ℂ=>term n dn t/term z dz t)
      ((dn*term z dz 0-term n dn 0*dz)/(term z dz 0)^2) 0:=
    (row n dn).div (row z dz) h
  simp only [term,zero_mul,add_zero] at d
  exact d

/-- The actual two-source logarithmic derivative has the stated division
at the sole quiet coefficient even for complex signed marks. -/
theorem two (z a b ab:ℂ)(hz:z≠0):
    HasDerivAt (fun t:ℂ=>term a ab t/term z b t) (ab/z-a*b/z^2) 0:=by
  convert ratio a ab z b hz using 1
  field_simp

/-- Differentiate the normalized two-source response with respect to the
coefficient of one distinguished prior occurrence. The two singleton
subtractions and their compensating quiet term are retained. -/
theorem signed (z a b ab dz da db dab:ℂ)(hz:z≠0):
    HasDerivAt (fun t:ℂ=>
      term ab dab t/term z dz t-
        (term a da t/term z dz t)*(term b db t/term z dz t))
      (dab/z-(dz*ab+da*b+db*a)/z^2+2*dz*a*b/z^3) 0:=by
  have h:HasDerivAt (fun t:ℂ=>term ab dab t/term z dz t-
      (term a da t/term z dz t)*(term b db t/term z dz t))
      ((dab*z-ab*dz)/z^2-((da*z-a*dz)/z^2*(term b db 0/term z dz 0)+
        (term a da 0/term z dz 0)*((db*z-b*dz)/z^2))) 0:=
    (ratio ab dab z dz hz).sub ((ratio a da z dz hz).mul (ratio b db z dz hz))
  have e:dab/z-(dz*ab+da*b+db*a)/z^2+2*dz*a*b/z^3=
      (dab*z-ab*dz)/z^2-((da*z-a*dz)/z^2*(term b db 0/term z dz 0)+
        (term a da 0/term z dz 0)*((db*z-b*dz)/z^2)):=by
    simp only [term,zero_mul,add_zero]
    field_simp
    ring
  rw [e]
  exact h

end YM.Integration.WilsonRootedNonflatResponseDerivative
