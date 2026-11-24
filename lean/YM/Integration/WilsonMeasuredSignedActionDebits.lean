import YM.Integration.WilsonMeasuredSignedActionWindow
import YM.Integration.WilsonMeasuredSignedActionFitted
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionDebits
open Function Filter Finset Labels Extra.Histories
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage WilsonMeasuredSignedActionWindow
open scoped Classical BigOperators
variable {G:Gauge}(F:Frame G 4)
theorem relative (x e p:F.Coeff){o E:ℝ}(op:0≤o)(up:o<1)
    (station:F.coeffSize (e-p)≤E)(germ:F.coeffSize (x-e)≤o*F.coeffSize x):
    F.coeffSize (x-p)≤(E+o*F.coeffSize p)/(1-o):=by
  have one:F.coeffSize (x-p)≤F.coeffSize (x-e)+F.coeffSize (e-p):=by
    simpa only [sub_add_sub_cancel] using Size.add F (x-e) (e-p)
  have two:F.coeffSize x≤F.coeffSize (x-p)+F.coeffSize p:=by
    simpa only [sub_add_cancel] using Size.add F (x-p) p
  have three:=mul_le_mul_of_nonneg_left two op
  apply (le_div_iff₀ (sub_pos.mpr up)).mpr
  linarith only [one,station,germ,three]
def total:ℝ:=2*(Fintype.card Signed:ℝ)
theorem total_pos:0<total:=by unfold total;positivity
theorem inspected (simple:G.Simple)(A:F.Coeff≃ₗ[ℂ]F.Coeff)
    (moved:∀y w,Motion.patch F y (A w)=A (Motion.patch F y w))
    (signed:∀v,fixed F v→positive F v→positive F (A v)) (invariant:fixed F (axis F))
    {v:F.Coeff}{s:ℝ}(sp:0<s)
    (heard:cost F*F.coeffSize ((s:ℂ) • F.core (A v)-axis F)<total*F.coeffSize (axis F)):
    ∃c:ℝ,0≤c ∧ F.core (pool F v)=(c:ℂ) • axis F:=by
  have use:((total:ℂ)*((s/total:ℝ):ℂ))=(s:ℂ):=by
    push_cast
    field_simp [(Complex.ofReal_ne_zero.mpr total_pos.ne')]
  have same:pool F ((s:ℂ) • F.core (A v)-axis F)=
      (total:ℂ) • (((s/total:ℝ):ℂ) • F.core (pool F (A v))-axis F):=by
    rw [WilsonMeasuredSignedActionAverage.sub,scale,←WilsonMeasuredSignedActionAverage.core,
      count F _ invariant,smul_sub,smul_smul,use]
    rfl
  have paid:=lt_of_le_of_lt (costs F ((s:ℂ) • F.core (A v)-axis F)) heard
  rw [same,WilsonMeasuredSignedActionCone.size,abs_of_pos total_pos] at paid
  exact pulled F simple A moved signed (div_pos sp total_pos)
    ((mul_lt_mul_iff_of_pos_left total_pos).mp paid)
end YM.Integration.WilsonMeasuredSignedActionDebits
end
