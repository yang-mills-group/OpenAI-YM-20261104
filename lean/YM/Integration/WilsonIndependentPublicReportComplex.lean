import YM.Integration.WilsonIndependentPublicClockWindow

/-! Complex observations use the very same real report on both components
and at every occurrence in the ordinary product. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportComplex
open RegulatorIR RegulatorIR.Binding RegulatorIR.Profiles RegulatorIR.Clocks
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank PowerSeries
open WilsonIndependentPublicReportBias WilsonIndependentPublicReportClock
open scoped Classical BigOperators PowerSeries

def row (K:Feeds)(D q j:ℕ):ℝ:=coeff q (cleared K D (X^j))

theorem row_at (K:Feeds)(D q j:ℕ)(hj:j ≤ q):
    row K D q j=coeff (q-j) ((back (beta K))^j*((back (beta K))⁻¹)^D):=by
  rw [row,WilsonIndependentPublicClockTransfer.coefficients]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))]
  · rw [coeff_X_pow,if_pos rfl,one_mul]
  · intro l hl ne
    rw [coeff_X_pow,if_neg (by omega),zero_mul]

def apply (K:Feeds)(D:ℕ)(A:ℂ⟦X⟧):ℂ⟦X⟧:=
    (PowerSeries.map (algebraMap ℝ ℂ) (factor K))^D*
      A.subst (PowerSeries.map (algebraMap ℝ ℂ) (inverse K))

theorem coefficients (K:Feeds)(D q:ℕ)(A:ℂ⟦X⟧):
    coeff q (apply K D A)=∑ j∈Finset.range (q+1),coeff j A*(row K D q j:ℂ):=by
  let B:=back (beta K)
  let m:=PowerSeries.map (algebraMap ℝ ℂ)
  let b:=m B
  let u:=m ((B⁻¹)^D)
  have axis:m (inverse K)= b*X:=by
    rw [WilsonIndependentPublicReportBias.backward,map_mul];rw [show m X=X from map_X _]
  have paid:(m (factor K))^D=u:=by rw [restoring,←map_pow]
  let sub:ℂ⟦X⟧→+*ℂ⟦X⟧:=
    (substAlgHom (R:=ℂ) (HasSubst.of_constantCoeff_zero' (by simp : constantCoeff (b*X)=0))).toRingHom
  have sx:sub X=b*X:=substAlgHom_X _
  have sc (t:ℂ):sub (C t)=C t:=by change substAlgHom _ _=_;rw [coe_substAlgHom];exact subst_C t
  change coeff q ((m (factor K))^D*A.subst (m (inverse K)))=_
  rw [axis,paid,mul_comm]
  have sa:sub A=PowerSeries.subst (b*X) A:=by
    change substAlgHom _ _=_
    rw [coe_substAlgHom]
  rw [←sa]
  rw [(Equal.mul (filtered (show constantCoeff (sub X)=0 by rw [sx];simp)
    (shave A (q+1))) (Equal.refl u _)) q q.lt_succ_self,map_sum,Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have leq:j ≤ q:=Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [row_at K D q j leq,map_mul sub,map_pow sub,sx,sc,mul_pow,
    show C (coeff j A)*(b^j*X^j)*u=(C (coeff j A)*(b^j*u))*X^j by ring,
    coeff_mul_X_pow',if_pos leq,coeff_C_mul]
  change _*(coeff (q-j)) ((m B)^j*m ((B⁻¹)^D))=_
  rw [←map_pow,←map_mul]
  rfl

theorem difference (K:Feeds)(D q:ℕ)(A B:ℂ⟦X⟧):
    coeff q (apply K D A)-coeff q (apply K D B)=
      ∑ j∈Finset.range (q+1),(coeff j A-coeff j B)*(row K D q j:ℂ):=by
  rw [coefficients,coefficients,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_mul]

end YM.Integration.WilsonIndependentPublicReportComplex
