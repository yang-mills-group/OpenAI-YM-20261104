import YM.Integration.WilsonIndependentFittedRosterCash
import YM.Integration.WilsonIndependentFittedMixedCash

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedRosterWindow
open WilsonCoeffUV Blue Finset PowerSeries
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Classical
variable {I:Type}[Fintype I]{J:I→Type}[∀i,Fintype (J i)]

open WilsonIndependentFittedRosterCash (roster numerical reserve)

theorem tail (Q J:ℕ)(order:J ≤ Q)(g:ℝ)(small:|g| ≤ 1)(Z:PowerSeries ℂ):
    ‖cash Q g Z-cash J g Z‖ ≤ |g|^(J+1)*belt Q Z:=by
  let u:=fun i:ℕ=>(g:ℂ)^i*coeff i Z
  change ‖(∑i∈range (Q+1),u i)-(∑i∈range (J+1),u i)‖ ≤ _
  rw [←sum_Ico_eq_sub _ (Nat.succ_le_succ order)]
  calc
    _ ≤ ∑i∈Ico (J+1) (Q+1),‖u i‖:=norm_sum_le _ _
    _ ≤ ∑i∈Ico (J+1) (Q+1),|g|^(J+1)*‖coeff i Z‖:=by
      apply sum_le_sum
      intro i hi
      rw [show ‖u i‖=|g|^i*‖coeff i Z‖ by simp [u,norm_pow]]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg g) small (mem_Ico.mp hi).1) (norm_nonneg _)
    _ ≤ ∑i∈range (Q+1),|g|^(J+1)*‖coeff i Z‖:=sum_le_sum_of_subset_of_nonneg
      (fun i hi=>mem_range.mpr (mem_Ico.mp hi).2) (fun i _ _=>mul_nonneg (pow_nonneg (abs_nonneg g) _) (norm_nonneg _))
    _=_:=by unfold belt;rw [mul_sum]

theorem original (Q low:ℕ)(order:low ≤ Q)(g:ℝ)(small:|g| ≤ 1)
    (A:(i:I) → J i → Cost)(B:((i:I) → J i) → Cost)(M:ℝ)(price:∀w,belt Q (embed (B w)) ≤ M):
    ‖cash Q g (embed (roster A B))-
        ∑w,(∏i,cash Q g (embed (A i (w i))))*cash low g (embed (B w))‖ ≤
      ((Fintype.card I:ℝ)+1)*|g|^(Q+1)*reserve Q A*M+numerical Q g A*|g|^(low+1)*M:=by
  let row:=fun (b:ℕ) => ∑w:(i:I) → J i,(∏i,cash Q g (embed (A i (w i))))*cash b g (embed (B w))
  have high:=WilsonIndependentFittedRosterCash.measured Q g small A B M price
  have mid:‖row Q-row low‖ ≤ numerical Q g A*(|g|^(low+1)*M):=by
    unfold row
    rw [←sum_sub_distrib]
    calc
      _ ≤ _:=norm_sum_le _ _
      _ ≤ ∑w:(i:I) → J i,(∏i,‖cash Q g (embed (A i (w i)))‖)*(|g|^(low+1)*M):=by
        apply sum_le_sum
        intro w hw
        rw [←mul_sub,norm_mul,norm_prod]
        exact mul_le_mul_of_nonneg_left ((tail Q low order g small (embed (B w))).trans
          (mul_le_mul_of_nonneg_left (price w) (pow_nonneg (abs_nonneg _) _))) (prod_nonneg (fun _ _=>norm_nonneg _))
      _=_:=by rw [←sum_mul];congr 1;unfold numerical;rw [Fintype.prod_sum]
  exact (norm_sub_le_norm_sub_add_norm_sub (cash Q g (embed (roster A B))) (row Q) (row low)).trans
    (by simpa [mul_assoc] using add_le_add high mid)

end YM.Integration.WilsonIndependentFittedRosterWindow
