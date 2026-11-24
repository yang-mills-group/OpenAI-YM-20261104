import YM.Integration.WilsonReceivedDepositedOrbitalFixedMoments
import YM.Integration.WilsonIndependentCollarLowerMass

/-! The actual paint used on each previously deposited connected block and its
one outer page. All the rows of that block have already entered its prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitalPeg
open Finset WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Flooring
open WilsonReceivedCanonicalSocketSeed (sheet contact)
open WilsonReceivedDepositedOrbitalFixedMoments (point reading charge)
open scoped Classical BigOperators ContDiff

theorem page_cap (d:ℕ) : ‖page d (sheet d)‖ ≤ 1 := by
  apply pledge _ zero_le_one
  intro i _ a x
  cases i with
  | zero => simp [crease,sheet,iteratedFDeriv_zero_apply]
  | succ i => simp [crease,sheet,iteratedFDeriv_succ_const]

theorem point_cap : ‖point‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa only [point,claim_take,one_mul] using registry a (contact 1) zeroC

theorem point_norm : ‖point‖ = 1 := by
  apply le_antisymm point_cap
  have h := point.le_opNorm (reading ())
  rw [charge,norm_one] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (page_cap 1) (norm_nonneg point)).trans_eq (mul_one _))

theorem peg_norm {I:Type} (i:I) : ‖reading i‖ = 1 := by
  apply le_antisymm (page_cap 1)
  have h := point.le_opNorm (reading i)
  simp only [charge,norm_one,point_norm,one_mul] at h
  exact h

def ink {V:Type}[DecidableEq V]{D:V→ℕ}(t:Case D)(J:Finset V) :
    Pen D J →L[ℝ] Vote 1 := (touch t J).smulRight point

theorem inner {V:Type}[DecidableEq V][Fintype V]{D:V→ℕ}(t:Case D)(J:Finset V) :
    ‖ink t J‖ = ‖touch t J‖ ∧ ‖ink t J‖ ≤ ∏v∈J,‖t v‖ := by
  have h : ‖ink t J‖ = ‖touch t J‖ := by rw [ink,ContinuousLinearMap.norm_smulRight_apply,point_norm,mul_one]
  exact ⟨h,h.le.trans (shelled D t J)⟩

def outer {I:Type}[DecidableEq I](J:Finset I) :
    Pen (fun _:I=>1) J →L[ℝ] ℂ := Complex.ofRealCLM.comp (touch reading J)

theorem outer_cap {I:Type}[DecidableEq I][Fintype I](J:Finset I) : ‖outer J‖ ≤ 1 := by
  have h := ContinuousLinearMap.opNorm_comp_le Complex.ofRealCLM (touch reading J)
  rw [Complex.ofRealCLM_norm,one_mul] at h
  exact h.trans ((shelled _ reading J).trans_eq (Finset.prod_eq_one fun i _=>peg_norm i))

theorem charges {V I:Type}[DecidableEq V][DecidableEq I][Fintype V][Fintype I]{D:V→ℕ}(t:Case D)(J:I→Finset V)(s:Finset I) :
    ‖outer s‖ ≤ 1 ∧ ∀i, ‖ink t (J i)‖ ≤ ∏v∈J i,‖t v‖ :=
  ⟨outer_cap s,fun i=>(inner t (J i)).2⟩

end YM.Integration.WilsonIndependentCollarOrbitalPeg
end
