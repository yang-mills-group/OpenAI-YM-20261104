import YM.Integration.WilsonMarkedKineticGerm

/-! The physical and independently prescribed inverse coupling solve the
same finite scalar equation, with their own actual incoming kinetic coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedScalarEquation
open Finset PowerSeries FormalBulk08 Wine Comparison.RG02 Adjacent
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open scoped BigOperators Classical

def table {S : Type*} [CommSemiring S] (cap : ℕ) (fee : ℕ → S) (A : PowerSeries S) :=
  ∑ j ∈ range (cap+1), C (fee j) * (X*A)^j

theorem term {S : Type*} [CommSemiring S] (a : S) (A B : PowerSeries S)
    (j e : ℕ) :
    coeff e (C a * (X*A)^j * B) =
      (if j ≤ e then coeff (e-j) (A^j*B) else 0) * a := by
  rw [show C a*(X*A)^j*B = (C a*(A^j*B))*X^j by rw [mul_pow]; ring,
    coeff_mul_X_pow']
  by_cases hj : j ≤ e
  · simp only [if_pos hj,coeff_C_mul,mul_comm a]
  · simp only [if_neg hj,zero_mul]

/-- No equality to any independent fee occurs in this identity. It is the
physical normalized kinetic Hessian read in the actual inverse coordinate. -/
theorem physical (c : Caliber) (cap : ℕ) :
    let A := rate (c.back cap)
    A^2 = table cap (fun j => (c.measure j : ℂ)) A := by
  intro A
  let U := reciprocal (c.back cap)
  have hz : table cap (fun j => (c.measure j : ℂ)) A * U^2 = 1 := by
    ext e
    rw [table,Finset.sum_mul,map_sum,coeff_one,←c.horizon cap e]
    apply sum_congr rfl
    intro j _
    rw [term]
    by_cases hj : j ≤ e
    · rw [if_pos hj,←analytic c cap e j 2 hj]
      rfl
    · rw [if_neg hj]
      have H := (above c cap (1:Pence) (Nat.lt_of_not_ge hj) 2).1
      change 0 * _ = (physicalWeight c cap e j 2) * _
      rw [H]
  have hunit : A*U = 1 := unit (c.back cap)
  calc
    A^2 = 1*A^2 := (one_mul _).symm
    _ = (table cap (fun j => (c.measure j : ℂ)) A * U^2) * A^2 := by rw [hz]
    _ = table cap (fun j => (c.measure j : ℂ)) A * (A*U)^2 := by ring
    _ = _ := by rw [hunit,one_pow,mul_one]

private theorem quadratic (H : Pence) (hH : Wine.Fresh H) :
    (Wine.bookH H)^2 = H.subst (X*Wine.bookH H) := by
  let A := Wine.bookH H
  let U := Wine.bookU H
  have u : A*U=1 := Wine.book_equal H
  have eq : H.subst (X*A) * U^2 = 1 := by
    rw [show X*A=Wine.runic H from Wine.forward_green H]
    exact Wine.correction_read H hH
  change A^2 = H.subst (X*A)
  calc
    A^2 = 1*A^2 := (one_mul _).symm
    _ = (H.subst (X*A)*U^2)*A^2 := by rw [eq]
    _ = H.subst (X*A) * (A*U)^2 := by ring
    _ = _ := by rw [u,one_pow,mul_one]

/-- The same equation, through the genuine requested order, for the
independent formal kinetic scalar and its genuine formal change of variable. -/
theorem formal (H : Pence) (hH : Wine.Fresh H) (cap : ℕ) :
    let A := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
    Series.Through cap (A^2) (table cap (fun j => ((coeff j H : ℝ) : ℂ)) A) := by
  intro A
  have real : Series.Through cap ((Wine.bookH H)^2) (table cap (fun j => coeff j H) (Wine.bookH H)) := by
    intro e he
    have h0 : coeff 0 (X*Wine.bookH H)=0 := by
      rw [Wine.forward_green]; exact Wine.runic_phi H
    rw [quadratic H hH,Series.subst_coeff h0 H cap e he,table,map_sum]
    simp only [coeff_C_mul]
  have lift : PowerSeries.map Complex.ofRealHom
      (table cap (fun j => coeff j H) (Wine.bookH H)) = table cap (fun j => ((coeff j H : ℝ) : ℂ)) A := by
    simp [table,A]
  intro e he
  change coeff e ((PowerSeries.map Complex.ofRealHom (Wine.bookH H))^2) = _
  rw [←map_pow,←lift,coeff_map,coeff_map,real e he]

end YM.Integration.WilsonMarkedScalarEquation
