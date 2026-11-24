import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogBill

/-! Coupling reserve spent on the full connected coefficient. Its exponent depends on the
number of occupied physical sites and the unchanged incoming amplitude exponent. -/
set_option autoImplicit false
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogReserve
open Finset
open Comparison.RG02.Order
open scoped BigOperators

theorem spend {q E n r i:ℕ} {g A:ℝ} (hg:0<g) (small:g≤1) (fund:1≤A)
    (reserve:q+E*n≤r) (hi:i≤n):
    g^(r+1)*(A/g^E)^i≤g^(q+1)*A^n:=by
  have exp:E*i+(q+1)≤r+1:=by have:=Nat.mul_le_mul_left E hi;omega
  calc
    _≤g^(E*i+(q+1))*(A/g^E)^i:=
      mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hg.le small exp)
        (pow_nonneg (div_nonneg (by linarith) (pow_nonneg hg.le _)) _)
    _=g^(q+1)*A^i:=by rw [pow_add,div_pow,←pow_mul];field_simp
    _≤g^(q+1)*A^n:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ fund hi) (pow_nonneg hg.le _)

theorem budget {q E n r:ℕ} {g A:ℝ} (hg:0<g) (small:g≤1) (fund:1≤A)
    (reserve:q+E*n≤r):
    g^(r+1)*repeats n (A/g^E)≤g^(q+1)*(n*A^n) ∧
    g^(r+1)*(∑i∈range n,(A/g^E)^(i+1))≤g^(q+1)*(n*A^n):=by
  constructor
  · rw [repeats,mul_sum]
    calc
      _≤∑_i∈range n,g^(q+1)*A^n:=Finset.sum_le_sum fun i hi=>
        spend hg small fund reserve (Finset.mem_range.mp hi).le
      _=g^(q+1)*(n*A^n):=by simp;ring
  · rw [mul_sum]
    calc
      _≤∑_i∈range n,g^(q+1)*A^n:=Finset.sum_le_sum fun i hi=>
        spend hg small fund reserve (Finset.mem_range.mp hi)
      _=g^(q+1)*(n*A^n):=by simp;ring

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogReserve
