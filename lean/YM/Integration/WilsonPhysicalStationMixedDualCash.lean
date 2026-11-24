import YM.Integration.WilsonPhysicalStationMixedBilledPort
/-! Coefficientwise dual thermal weights cancel all the signed unequal-rank fees before
the final Kirchhoff-Wick row is tested in the physical lower quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedDualCash
open Finset
open scoped BigOperators Classical
variable {ι:Type*}[Fintype ι]

theorem weighted (q Q:ℕ)(qj:ι→ℕ){T:ℝ}(tp:0≤T)(c u:ι→ℂ)(cap fee:ι→ℝ)
    (cp:∀j,0≤cap j)
    (dual:∀j,‖c j‖*T^Q≤cap j*T^(qj j))(paid:∀j,‖u j‖*T^(qj j)≤fee j*T^q):
    ‖∑j,c j*u j‖*T^Q≤(∑j,cap j*fee j)*T^q:=by
  calc _≤(∑j,‖c j*u j‖)*T^Q:=mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg tp _)
       _=∑j,‖c j*u j‖*T^Q:=Finset.sum_mul ..
       _≤∑j,(cap j*fee j)*T^q:=by
         apply Finset.sum_le_sum
         intro j _
         calc _=(‖c j‖*T^Q)*‖u j‖:=by rw [norm_mul];ring
              _≤(cap j*T^(qj j))*‖u j‖:=mul_le_mul_of_nonneg_right (dual j) (norm_nonneg _)
              _=cap j*(‖u j‖*T^(qj j)):=by ring
              _≤cap j*(fee j*T^q):=mul_le_mul_of_nonneg_left (paid j) (cp j)
              _=_:=by ring
       _=_:=(Finset.sum_mul ..).symm

theorem signed (q Q:ℕ)(qj:ι→ℕ){T:ℝ}(tp:0≤T)(c u y:ι→ℂ)(χ:ℂ)(cap fee:ι→ℝ)
    (cp:∀j,0≤cap j)
    (dual:∀j,‖c j‖*T^Q≤cap j*T^(qj j))(paid:∀j,‖u j-χ*y j‖*T^(qj j)≤fee j*T^q):
    ‖(∑j,c j*u j)-χ*∑j,c j*y j‖*T^Q≤(∑j,cap j*fee j)*T^q:=by
  have eq:(∑j,c j*u j)-χ*∑j,c j*y j=∑j,c j*(u j-χ*y j):=by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _=>by ring)
  rw [eq]
  exact weighted q Q qj tp c _ cap fee cp dual paid

end YM.Integration.WilsonPhysicalStationMixedDualCash
end
