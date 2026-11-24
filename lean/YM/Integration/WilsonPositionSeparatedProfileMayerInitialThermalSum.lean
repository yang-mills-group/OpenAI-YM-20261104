import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalFiling

/-! Absolute perturbation order in the nominated Gaussian row agrees with the regraded
sum of the actual compact Wilson words; there is no high-degree remainder in this step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSum
open PertExtension PertExtension.Series WilsonPositionSeparatedProfileMayerInitialThermalSeries
open scoped Classical BigOperators

theorem coefficient (c:ℂ) (d:ℕ) (a:ℕ→ℂ) (k:ℕ):
    deposited c d a k=if d≤k then c*a (k-d) else 0:=by
  have one:PowerSeries.mk (fun n=>if n=d then c else 0)=PowerSeries.C c * PowerSeries.X^d:=by
    ext n
    simp
  rw [deposited,Tested.conv,Tested.term,one,mul_assoc,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem printed (c:ℂ) (d:ℕ) (a:ℕ→ℂ) {n:ℕ} (present:d≤n) (g:ℝ):
    Tested.peval (deposited c d a) n g=c*(g:ℂ)^d*Tested.peval a (n-d) g:=by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le present
  have first:∑i∈Finset.range d,g^i • deposited c d a i=0:=by
    apply Finset.sum_eq_zero
    intro i hi
    rw [coefficient,if_neg (Nat.not_le.mpr (Finset.mem_range.mp hi)),smul_zero]
  simp only [Tested.peval,Zone.eval,Nat.add_sub_cancel_left,add_assoc d k 1]
  rw [Finset.sum_range_add _ d (k+1),first,zero_add,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  simp [coefficient,pow_add,Complex.real_smul]
  ring

theorem total {I:Type*} [Fintype I] (c:I→ℂ) (d:I→ℕ) (a:I→ℕ→ℂ) {n:ℕ}
    (present:∀i,d i≤n) (g:ℝ):
    Tested.peval (fun j=>∑i,deposited (c i) (d i) (a i) j) n g=
       ∑i,c i*(g:ℂ)^(d i)*Tested.peval (a i) (n-d i) g:=by
  calc
    _ = ∑i,Tested.peval (deposited (c i) (d i) (a i)) n g:=by
      simp only [Tested.peval,Zone.eval,Finset.smul_sum]
      exact Finset.sum_comm
    _ = _:= Finset.sum_congr rfl fun i _=>printed (c i) (d i) (a i) (present i) g

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSum
