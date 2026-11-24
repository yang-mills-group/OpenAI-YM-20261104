import YM.Integration.WilsonPositionProgramFiniteGaussianReturn
import YM.Integration.WilsonPositionProgramFiledOccupiedDriver

/-! A finite price on the filed grade roster, with no sum over source positions or torus images. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiniteRootEnvelope
open Finset Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise Lattice RG
open Comparison.RG02 Push Push.AbsoluteSums
open scoped BigOperators Classical
variable {I:Type}[Fintype I]

def budget (f:I→ℝ):ℝ:=∑i,max 0 (f i)
def degree (d:I→ℕ):ℕ:=∑i,d i

theorem budgeted (f:I→ℝ)(i:I): f i ≤ budget f :=
  (le_max_right _ _).trans (single_le_sum (f:=fun u=>max 0 (f u)) (fun _ _=>le_max_left _ _) (mem_univ i))

theorem nonneg (f:I→ℝ):0≤budget f:=sum_nonneg (fun _ _=>le_max_left _ _)

theorem entered (f:I→ℝ)(d:I→ℕ)(i:I){a δ H y z:ℝ}(hd:0≤δ)(hy:0≤y)(hz:1≤z)
    (moved:y≤H*z)(afforded:a≤δ*f i*y^(d i)):
    a ≤ (δ*(budget f*(max 1 H)^(degree d)))*z^(degree d):=by
  have h0:1≤ max 1 H:=le_max_left _ _
  have up:y≤ max 1 H*z:=moved.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hz))
  have key:d i≤degree d:=single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ i)
  calc
    a ≤ (δ*budget f)*y^(d i) :=afforded.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (budgeted f i) hd) (pow_nonneg hy _))
    _ ≤ (δ*budget f)*(max 1 H*z)^(degree d) :=mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ hy up _).trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le h0 hz) key))
      (mul_nonneg hd (nonneg f))
    _ = _:=by rw [mul_pow];ring

variable {V X ι:Type}[DecidableEq V][Fintype V]{G:Gauge}{n:Side}{P:Passport n V}{R:Census V}

theorem credit (M:ι→Row P R G X)(w:V→ℝ)(grades:V→ℕ){σ cost:ℝ}{order count shelf:ℕ}
    (estate:Scene.Armada M w grades σ cost order count shelf)(c0:cost≤1)(s:R.Mode):
    |(s.val.image P.origin).card*cost|≤Fintype.card V:=by
  have low:0≤cost:=by simpa using budget_sum (estate.suggests 0) ∅
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) low)]
  have row:(s.val.image P.origin).card≤Fintype.card V:=card_image_le.trans (card_le_univ _)
  exact (mul_le_mul_of_nonneg_left c0 (Nat.cast_nonneg _)).trans
    (by rw [mul_one];exact_mod_cast row)

end YM.Integration.WilsonPositionProgramFiniteRootEnvelope
end
