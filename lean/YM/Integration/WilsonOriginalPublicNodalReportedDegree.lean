import YM.Integration.WilsonOriginalPublicNodalTestedCoefficient
import YM.Integration.WilsonOriginalPublicNodalEnrolledMerStop

/-! Removing a deposited primitive degree commutes with the independently appointed reporting scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalReportedDegree
open PowerSeries RegulatorIR RegulatorIR.Clocks RegulatorIR.Profiles
open WilsonIndependentPublicReportClock (factor inverse units)
open WilsonIndependentPublicReportComplex (apply)
open WilsonCoeffUV.Blue

def lift (P:Cost):ℂ⟦X⟧:=PowerSeries.map (algebraMap ℝ ℂ) P

theorem suspend (K:Feeds)(D h:ℕ)(u:ℂ)(Y:ℂ⟦X⟧):
    apply K (D+h) (C u*PowerSeries.X^h*Y)=C u*PowerSeries.X^h*apply K D Y:=by
  let m:=PowerSeries.map (algebraMap ℝ ℂ)
  let b:=m (inverse K)
  let a:=m (factor K)
  have cancel:b*a=PowerSeries.X:=by rw [show b*a=m (inverse K*factor K) from (map_mul m _ _).symm,units,map_X]
  have at0:constantCoeff b=0:=by
    dsimp [b,m]
    rw [WilsonIndependentPublicReportBias.backward,map_mul,map_X,map_mul,constantCoeff_X,mul_zero]
  let sub:ℂ⟦X⟧→+*ℂ⟦X⟧:=(substAlgHom (R:=ℂ) (HasSubst.of_constantCoeff_zero' at0)).toRingHom
  have same (f:ℂ⟦X⟧):sub f=f.subst b:=by change substAlgHom _ _=_;rw [coe_substAlgHom]
  have sx:sub PowerSeries.X=b:=substAlgHom_X _
  have sc:sub (C u)=C u:=by change substAlgHom _ _=_;rw [coe_substAlgHom];exact subst_C u
  change a^(D+h)*(C u*PowerSeries.X^h*Y).subst b=C u*PowerSeries.X^h*(a^D*Y.subst b)
  rw [←same,←same, map_mul sub,map_mul sub,map_pow sub,sx,sc,pow_add]
  calc _ = C u*((b*a)^h)*(a^D*sub Y) := by rw [mul_pow]; ring
       _ = _ := by rw [cancel]

theorem received (K:Feeds)(D h q:ℕ)(u:ℂ)(Y:ℂ⟦X⟧):
    coeff (q+h) (apply K (D+h) (C u*PowerSeries.X^h*Y))=u*coeff q (apply K D Y):=by
  rw [suspend,mul_assoc,coeff_C_mul]
  simp [coeff_X_pow_mul']

theorem original (K:Feeds)(D h q:ℕ)(t:ℝ)(B E:Cost):
    coeff (q+h) (apply K (D+h) (lift (C t*(B*PowerSeries.X)^h*E)))=
      (t:ℂ)*coeff q (apply K D (lift (B^h*E))):=by
  rw [show C t*(B*PowerSeries.X)^h*E=C t*PowerSeries.X^h*(B^h*E) by rw [mul_pow];ring]
  simp only [lift,map_mul,map_pow,PowerSeries.map_C,PowerSeries.map_X]
  exact received K D h q (t:ℂ) _

end YM.Integration.WilsonOriginalPublicNodalReportedDegree
end
