import YM.Integration.WilsonLocalCompactHistory

/-! Summing two extra powers of the true running coupling over a
logarithmic reporting window recovers the prescribed physical order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactRate
open Finset
open scoped BigOperators
theorem summed {B ε:ℝ} (bp:0<B) (ep:0<ε) (q:ℕ):
    ∃η:ℝ,0<η ∧ ∀j b:ℕ,∀g:ℕ→ℝ,∀β C:ℝ,0≤C→0≤g b→
    ((b-j:ℕ):ℝ)≤B*β→β*g b^2≤2→
    (∀i∈Ico j b,0≤g (i+1) ∧ g (i+1)≤1 ∧ g (i+1)≤3*g b)→
    let δ:=fun i=>η*g (i+1)^(q+2)
    ∑i∈Ico j b,2*(δ i*(1+δ i))*C≤ε*g b^q*C:=by
  let M:=8*B*(3:ℝ)^(q+2)
  let η:=min 1 (ε/M)
  have mp:0<M:=by dsimp [M];positivity
  have hp:0<η:=lt_min zero_lt_one (div_pos ep mp)
  have h1:η≤1:=min_le_left _ _
  have rate:η*M≤ε:=(le_div_iff₀ mp).mp (min_le_right _ _)
  refine ⟨η,hp,fun j b g β C cp gp len warm clock=>?_⟩
  let δ:=fun i=>η*g (i+1)^(q+2)
  have cash (i) (hi:i∈Ico j b):2*(δ i*(1+δ i))*C≤4*η*(3*g b)^(q+2)*C:=by
    obtain ⟨pos,one,three⟩:=clock i hi
    have small:δ i≤1:=calc
      δ i≤η*1:=mul_le_mul_of_nonneg_left (pow_le_one₀ pos one) hp.le
      _≤1:=by simpa only [mul_one] using h1
    have dp:0≤δ i:=mul_nonneg hp.le (pow_nonneg pos _)
    have t:δ i≤η*(3*g b)^(q+2):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ pos three _) hp.le
    exact mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg dp (sub_nonneg.mpr small),t]) cp
  calc ∑i∈Ico j b,2*(δ i*(1+δ i))*C
      ≤∑_i∈Ico j b,4*η*(3*g b)^(q+2)*C:=Finset.sum_le_sum cash
    _ = ((b-j:ℕ):ℝ)*(4*η*(3*g b)^(q+2)*C):=by simp
    _ ≤ (B*β)*(4*η*(3*g b)^(q+2)*C):=mul_le_mul_of_nonneg_right len (by positivity)
    _ = (β*g b^2)*(4*B*η*(3:ℝ)^(q+2)*g b^q*C):=by rw [mul_pow,pow_add (g b) q 2];ring
    _ ≤ 2*(4*B*η*(3:ℝ)^(q+2)*g b^q*C):=mul_le_mul_of_nonneg_right warm (by positivity)
    _ = η*M*(g b^q*C):=by dsimp [M];ring
    _ ≤ ε*g b^q*C:=by rw [mul_assoc ε];exact mul_le_mul_of_nonneg_right rate (by positivity)

end YM.Integration.WilsonLocalCompactRate
