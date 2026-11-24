import YM.Integration.WilsonIndependentFittedPivotCash
import YM.Integration.WilsonSeparatedPrefixMovingHighGrades

set_option autoImplicit false
namespace YM.Integration.WilsonMovingForkSharpThermalSplit
noncomputable section
open Finset
open WilsonIndependentFittedPivotCash (measured)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonSeparatedPrefixMovingHighGrades (above)
open scoped BigOperators
theorem evaluated (e:ℕ)(g:ℝ)(f:ℕ→ℝ):
    measured e g (PowerSeries.mk f)=((∑q∈range (e+1),g^q*f q:ℝ):ℂ):=by
  simp [measured,cash,embed,PowerSeries.coeff_map]
theorem multiple (e:ℕ)(g a:ℝ)(f:ℕ→ℝ):
    measured e g (PowerSeries.mk (fun q=>a*f q))=(a:ℂ)*measured e g (PowerSeries.mk f):=by
  rw [evaluated,evaluated,←Complex.ofReal_mul,Finset.mul_sum]
  apply congrArg (Complex.ofReal)
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem original (e J:ℕ)(g:ℝ)(f:ℕ→ℝ)(low high:ℝ)(pos:0≤g)(small:g≤1)
    (head:∀q,q≤e → q≤J → ‖f q‖≤low)(tail:‖above J e g f‖ ≤ high):
    ‖measured e g (PowerSeries.mk f)‖ ≤ ((J+1:ℕ):ℝ)*low+high:=by
  rw [evaluated,Complex.norm_real]
  let fine:=(range (e+1)).filter (fun q=>q≤J)
  have join:(∑q∈range (e+1),g^q*f q)=(∑q∈fine,g^q*f q)+above J e g f:=by
    simpa only [fine,above,not_le] using (sum_filter_add_sum_filter_not (range (e+1)) (fun q=>q≤J) (fun q=>g^q*f q)).symm
  rw [join]
  apply (norm_add_le ..).trans
  apply add_le_add _ tail
  have hl:0≤low:=(norm_nonneg _).trans (head 0 (Nat.zero_le _) (Nat.zero_le _))
  have subset:fine⊆range (J+1):=fun i h=>mem_range.mpr (by have b: i≤J:=(mem_filter.mp h).2;omega)
  calc
    _ ≤ ∑q∈fine,low:=(norm_sum_le ..).trans (sum_le_sum fun i hi=>by
      obtain ⟨he,hj⟩:=mem_filter.mp hi
      have h:=head i (by simpa using he) hj
      rw [norm_mul,Real.norm_of_nonneg (pow_nonneg pos _)]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ pos small) (norm_nonneg _)).trans (by simpa using h))
    _ ≤ ∑_i∈range (J+1),low:=sum_le_sum_of_subset_of_nonneg subset (fun _ _ _=>hl)
    _ = _:=by simp
end
end YM.Integration.WilsonMovingForkSharpThermalSplit
