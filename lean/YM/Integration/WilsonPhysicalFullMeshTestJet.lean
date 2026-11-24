import YM.Integration.WilsonSmoothUnitFiniteGrid

/-! Signed extraction of a test jet against a nonconstant measured field.
The inverse permutations move its actual site on the complete planting grid. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalFullMeshTestJet
open Set Finset LocalLTE.Weft WilsonPosteriorProjectionStencil
open scoped Classical BigOperators
theorem tested (k:ℕ)(j:J k)(a:J k → ℝ)(t:ℝ)(p:J k → ℝ)(E:ℝ)
    (error:∀l:J k,|∑i:J k,a i*(t*probe k l)^i.val-p l|≤E):
    |a j*t^j.val-∑l:J k,weight k l j*p l|≤cost k j*E:=by
  have dual (i:J k):(∑l,weight k l j*(probe k l)^i.val)=if i=j then 1 else 0:=by
    rw [←tally k i j]
    apply sum_congr rfl
    intro l _
    unfold weight mark
    ring
  have col (i:J k):(∑l,weight k l j*(a i*(t*probe k l)^i.val))=
      a i*t^i.val*(if i=j then 1 else 0):=by
    rw [←dual]
    simp_rw [mul_sum,mul_pow]
    apply sum_congr rfl
    intro _ _
    ring
  have value:(∑l,weight k l j*∑i:J k,a i*(t*probe k l)^i.val)=a j*t^j.val:=by
    simp_rw [mul_sum]
    rw [sum_comm]
    simp_rw [col]
    simp
  rw [←value,←sum_sub_distrib]
  calc
    _ ≤ ∑l:J k,|weight k l j*(∑i:J k,a i*(t*probe k l)^i.val-p l)|:=by
      simpa only [mul_sub] using Finset.abs_sum_le_sum_abs
        (fun l:J k=>weight k l j*(∑i:J k,a i*(t*probe k l)^i.val)-weight k l j*p l) univ
    _ ≤ ∑l:J k,|weight k l j| *E:=by
      apply sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (error l) (abs_nonneg _)
    _=_:=by rw [cost,sum_mul]

theorem projected {A:Type*}[Fintype A](k:ℕ)(j:J k)(a:A → J k → ℝ)(t:ℝ)
    (change:J k → A ≃ A)(P:A → ℝ)(F:A → ℂ)(E:A → ℝ)
    (error:∀z l,|∑i:J k,a z i*(t*probe k l)^i.val-P (change l z)|≤E z):
    ‖(∑z,(↑(a z j*t^j.val):ℂ)*F z)-
      ∑z,(P z:ℂ)*∑l:J k,(weight k l j:ℂ)*F ((change l).symm z)‖ ≤
      cost k j*∑z,E z*‖F z‖:=by
  have move (l:J k):
      (∑z,(P z:ℂ)*((weight k l j:ℂ)*F ((change l).symm z)))=
      ∑z,(weight k l j:ℂ)*(P (change l z):ℂ)*F z:=by
    have rotate:=Equiv.sum_comp (change l)
      (fun z=>(P z:ℂ)*((weight k l j:ℂ)*F ((change l).symm z)))
    calc
      _=_:=rotate.symm
      _=_:=by simp only [Equiv.symm_apply_apply];apply sum_congr rfl;intro _ _;ring
  have actual:(∑z,(P z:ℂ)*∑l:J k,(weight k l j:ℂ)*F ((change l).symm z))=
      ∑z,(↑(∑l,weight k l j*P (change l z)):ℂ)*F z:=by
    simp_rw [mul_sum]
    rw [sum_comm]
    simp_rw [move]
    rw [sum_comm]
    simp only [Complex.ofReal_sum,Complex.ofReal_mul,sum_mul]
  rw [actual,←sum_sub_distrib]
  calc
    _ ≤ ∑z,‖(↑(a z j*t^j.val):ℂ)*F z-(↑(∑l,weight k l j*P (change l z)):ℂ)*F z‖:=
      norm_sum_le _ _
    _ ≤ ∑z,cost k j*E z*‖F z‖:=by
      apply sum_le_sum
      intro z _
      rw [←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (tested k j (a z) t _ (E z) (error z)) (norm_nonneg _)
    _=_:=by simp only [mul_assoc,mul_sum]
end YM.Integration.WilsonPhysicalFullMeshTestJet
