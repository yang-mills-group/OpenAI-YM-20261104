import YM.Integration.WilsonMarkedScalarEquation

/-! Exact signed response to an unbooked kinetic discrepancy. The scalar
divisor is a formal unit with constant two, independent of any lattice size. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedScalarResponse
open Function Finset PowerSeries FormalBulk08 Wine Comparison.RG02 Adjacent Moving.Path
open WilsonMarkedKineticGerm WilsonMarkedScalarEquation
open scoped BigOperators Classical

def difference (A B : PowerSeries ℂ) : ℕ → PowerSeries ℂ
  | 0 => 0
  | j+1 => A^j + B*difference A B j

private theorem powers (A B : PowerSeries ℂ) (j : ℕ) :
    (A-B)*difference A B j = A^j-B^j := by
  induction j with
  | zero => simp [difference]
  | succ j ih =>
    rw [difference,pow_succ,pow_succ]
    calc
      _ = (A-B)*A^j + B*((A-B)*difference A B j) := by ring
      _ = _ := by rw [ih]; ring

def slope (cap : ℕ) (b : ℕ → ℂ) (A B : PowerSeries ℂ) :=
  ∑ j ∈ range (cap+1), C (b j) * X^j * difference A B j

private theorem split (cap : ℕ) (a b : ℕ → ℂ) (A B : PowerSeries ℂ) :
    table cap a A - table cap b B =
      table cap (fun j => a j-b j) A + (A-B)*slope cap b A B := by
  unfold table slope
  rw [←sum_sub_distrib,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [map_sub,mul_pow,mul_pow]
  calc
    _ = (C (a j) - C (b j))*(X^j*A^j) + C (b j)*X^j*(A^j-B^j) := by ring
    _ = _ := by rw [←powers]; ring

def pivot (cap : ℕ) (b : ℕ → ℂ) (A B : PowerSeries ℂ) := A+B-slope cap b A B

theorem initial (cap : ℕ) (b : ℕ → ℂ) (A B : PowerSeries ℂ)
    (ha : coeff 0 A=1) (hb : coeff 0 B=1) : constantCoeff (pivot cap b A B)=2 := by
  have hzero : constantCoeff (slope cap b A B)=0 := by
    unfold slope
    rw [map_sum]
    apply sum_eq_zero
    intro j _
    cases j with
    | zero => simp [difference]
    | succ j => simp
  rw [pivot,map_sub,map_add,←coeff_zero_eq_constantCoeff_apply,ha,
    ←coeff_zero_eq_constantCoeff_apply,hb,hzero,sub_zero,one_add_one_eq_two]

/-- An actual inverse of the finite scalar response divisor. -/
def resolver (cap : ℕ) (b : ℕ → ℂ) (A B : PowerSeries ℂ) : PowerSeries ℂ :=
  invOfUnit (pivot cap b A B) (Units.mk0 2 (by norm_num))

/-- For arbitrary, possibly different primitive vacuum coefficients,
the inverse-coupling error is their signed sum times the original
finite scalar response kernel. No matching hypothesis is made. -/
theorem signed (c : Caliber) (cap : ℕ) (H : Pence) (hH : Wine.Fresh H) :
    let a := fun j => (c.measure j : ℂ)
    let b := fun j => ((coeff j H : ℝ) : ℂ)
    let A := rate (c.back cap)
    let B := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
    Series.Through cap (A-B)
      (table cap (fun j => a j-b j) A * resolver cap b A B) := by
  intro a b A B
  have hA : A^2=table cap a A := WilsonMarkedScalarEquation.physical c cap
  have hB : Series.Through cap (B^2) (table cap b B) := WilsonMarkedScalarEquation.formal H hH cap
  have pcap : Series.Through cap ((A-B)*pivot cap b A B) (table cap (fun j => a j-b j) A) := by
    intro n hn
    rw [show (A-B)*pivot cap b A B = (A^2-B^2) - (A-B)*slope cap b A B by unfold pivot; ring]
    calc
      _ = coeff n ((table cap a A - table cap b B) - (A-B)*slope cap b A B) := by
        simp only [map_sub,hA,hB n hn]
      _ = _ := by rw [split,add_sub_cancel_right]
  have ha : coeff 0 A=1 := by
    dsimp only [A,rate,germ]
    rw [coeff_mk,Moving.Shift.mzero,(c.back cap).origin,Complex.ofReal_one]
  have hb : coeff 0 B=1 := by
    change coeff 0 (PowerSeries.map Complex.ofRealHom (Wine.bookH H))=1
    rw [coeff_map,Wine.book_fresh]
    rfl
  have paid : pivot cap b A B * resolver cap b A B = 1 :=
    mul_invOfUnit _ _ (initial cap b A B ha hb)
  have prod := pcap.mul (Series.Through.exact_eq (resolver cap b A B) cap)
  rwa [mul_assoc,paid,mul_one] at prod

end YM.Integration.WilsonMarkedScalarResponse
