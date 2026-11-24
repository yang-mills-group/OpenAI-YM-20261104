import YM.Integration.WilsonPositionRawFiling

/-! Evaluation of the independently published raw Wilson coefficient on
every cutoff after the original real detector becomes invertible. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawPolynomial
open Finset Function Set Filter XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register
open WilsonPositionRawMesh WilsonPositionRawFiling
open scoped BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh) (q : ℕ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)

private theorem list (A : PowerSeries ℂ) :
    PowerSeries.trunc (q+1) A = ∑ k : Fin (q+1), Polynomial.C (PowerSeries.coeff k A)*Polynomial.X^(k:ℕ) := by
  rw [PowerSeries.trunc_apply,Nat.Ico_zero_eq_range,←Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Polynomial.monomial k (PowerSeries.coeff k A)) (q+1)]
  simp only [Polynomial.C_mul_X_pow_eq_monomial]

private theorem expand (s : ℕ) :
    (∑ k : Fin (q+1), Polynomial.C (detector Z m q k : ℂ)*Polynomial.X^(k:ℕ))^s =
      ∑ j : Fin s → Fin (q+1), Polynomial.C (word Z m q j : ℂ)*Polynomial.X^(order q j) := by
  calc
    _ = ∏ _ : Fin s, ∑ k : Fin (q+1), Polynomial.C (detector Z m q k : ℂ)*Polynomial.X^(k:ℕ) := by simp
    _ = ∑ j : Fin s → Fin (q+1), ∏ i, Polynomial.C (detector Z m q (j i) : ℂ)*Polynomial.X^(j i:ℕ) := Fintype.prod_sum _
    _ = _ := by simp [word,order,prod_mul_distrib,prod_pow_eq_pow_sum]

private def cut (x : ℝ) : ℂ[X] →+ ℂ where
  toFun P := (PowerSeries.trunc (q+1) (P : PowerSeries ℂ)).eval (x:ℂ)
  map_zero' := by simp
  map_add' _ _ := by simp

private theorem head (x : ℝ) (j : ℕ) (c : ℂ) :
    cut q x (Polynomial.C c*Polynomial.X^j) = if j ≤ q then c*(x:ℂ)^j else 0 := by
  have projected : PowerSeries.trunc (q+1) (↑(Polynomial.C c*Polynomial.X^j : ℂ[X]) : PowerSeries ℂ) =
      if j ≤ q then Polynomial.C c*Polynomial.X^j else 0 := by
    ext k
    rw [PowerSeries.coeff_trunc,Polynomial.coeff_coe,Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j ≤ q
    · rw [if_pos hj,Polynomial.coeff_C_mul_X_pow]
      by_cases hk : k < q+1
      · rw [if_pos hk]
      · rw [if_neg hk,if_neg (by omega : k ≠ j)]
    · rw [if_neg hj,Polynomial.coeff_zero]
      by_cases hk : k < q+1
      · rw [if_pos hk,if_neg (by omega : k ≠ j)]
      · rw [if_neg hk]
  change (PowerSeries.trunc (q+1) (↑(Polynomial.C c*Polynomial.X^j : ℂ[X]) : PowerSeries ℂ)).eval (x:ℂ) = _
  rw [projected]
  split_ifs <;> simp

theorem issued (use : Rose.Use Z.scheme Z.criterion m) (x : ℝ) :
    raw Z m q d φ v x = (PowerSeries.trunc (q+1) (said (published Z m d) φ v)).eval (x:ℂ) := by
  let X := said (Scale.System.positions Z.scheme Z.criterion d m) φ v
  let D := Rose.chosen Z.scheme Z.criterion m
  let P := (PowerSeries.trunc (q+1) X).comp (PowerSeries.trunc (q+1) D)
  have coeD (k : Fin (q+1)) : (detector Z m q k : ℂ) = PowerSeries.coeff k D := (key Z m).real.native _
  have congruent := WilsonIndependentSchemeTruncation.composed q X D (Rose.zero_choice ..)
  have trunc : PowerSeries.trunc (q+1) (P : PowerSeries ℂ) = PowerSeries.trunc (q+1) (PowerSeries.subst D X) := by
    ext j
    rw [PowerSeries.coeff_trunc,PowerSeries.coeff_trunc]
    split_ifs with hj
    · have h := Polynomial.X_pow_dvd_iff.mp congruent j hj
      change (P-PowerSeries.trunc (q+1) (PowerSeries.subst D X)).coeff j = 0 at h
      rw [Polynomial.coeff_sub,sub_eq_zero,PowerSeries.coeff_trunc,if_pos hj] at h
      exact (Polynomial.coeff_coe P j).trans h
    · rfl
  have words : P = ∑ s : Fin (q+1), ∑ j : Fin (s:ℕ) → Fin (q+1),
      Polynomial.C (source Z m q d φ v s*(word Z m q j : ℂ))*Polynomial.X^(order q j) := by
    rw [show P = (PowerSeries.trunc (q+1) X).comp (PowerSeries.trunc (q+1) D) from rfl,
      list,list,Polynomial.sum_comp]
    simp_rw [←coeD,Polynomial.mul_comp,Polynomial.C_comp,Polynomial.pow_comp,Polynomial.X_comp,expand,mul_sum]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro j _
    rw [←mul_assoc,←map_mul]
    simp [source,X,said]
  have eval : cut q x P = raw Z m q d φ v x := by
    rw [words]
    simp only [map_sum, head,raw,retained,Complex.ofReal_sum,mul_sum]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro j _
    split_ifs <;> push_cast <;> ring
  rw [←fieldwise Z m use d φ v]
  change raw Z m q d φ v x = (PowerSeries.trunc (q+1) (PowerSeries.subst D X)).eval (x:ℂ)
  rw [←trunc]
  exact eval.symm

end YM.Integration.WilsonPositionRawPolynomial
