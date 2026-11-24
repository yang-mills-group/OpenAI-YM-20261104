import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Quantitative normalization of a finite signed exponential expansion.
Its scalar and tested coefficients may come from the same physical posterior.
The vacuum is calibrated only by the constructed finite coefficient payment. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.FibreMeasure
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def tiltCoeff (j : ℕ) : ℝ := ((j+1).factorial:ℝ)⁻¹

def vacuumJet (m : ℕ) (a : ℕ → ℝ) : ℝ := 1+∑ j ∈ Finset.range m, tiltCoeff j*a j
def readerJet (m : ℕ) (base : E) (b : ℕ → E) : E := base+∑ j ∈ Finset.range m, tiltCoeff j • b j
def jetBudget (m : ℕ) (r : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range m, tiltCoeff j*r j

theorem finite_residual_tilt (m : ℕ) (a r : ℕ → ℝ) (b : ℕ → E) (base : E)
    (vacuum : ∀ j < m, |a j| ≤ r j) (reader : ∀ j < m, ‖b j‖ ≤ r j)
    (unit : ‖base‖ ≤ 1) (paid : jetBudget m r ≤ 1/2) :
    |vacuumJet m a-1| ≤ jetBudget m r ∧ 1/2 ≤ vacuumJet m a ∧
      ‖(vacuumJet m a)⁻¹ • readerJet m base b-base‖ ≤ 4*jetBudget m r := by
  let A := ∑ j ∈ Finset.range m,tiltCoeff j*a j
  let B := ∑ j ∈ Finset.range m,tiltCoeff j • b j
  let d := jetBudget m r
  let Z := vacuumJet m a
  have cn (j : ℕ) : 0 ≤ tiltCoeff j := by unfold tiltCoeff;positivity
  have sale : |A|≤d := calc
    |A| ≤ ∑ j ∈ Finset.range m, |tiltCoeff j*a j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ d := Finset.sum_le_sum (fun j hj => by rw [abs_mul,abs_of_nonneg (cn j)];exact mul_le_mul_of_nonneg_left (vacuum j (Finset.mem_range.mp hj)) (cn j))
  have test : ‖B‖≤d := calc
    ‖B‖ ≤ ∑ j ∈ Finset.range m, ‖tiltCoeff j • b j‖ := norm_sum_le ..
    _ ≤ d := Finset.sum_le_sum (fun j hj => by rw [norm_smul,Real.norm_of_nonneg (cn j)];exact mul_le_mul_of_nonneg_left (reader j (Finset.mem_range.mp hj)) (cn j))
  have floor : 1/2 ≤ Z := by
    change 1/2 ≤ 1+A
    linarith only [(abs_le.mp sale).1,show d≤1/2 from paid]
  have pos : 0<Z := by linarith only [floor]
  have id : Z⁻¹ • readerJet m base b - base = Z⁻¹ • (B-A • base) := by
    have z : Z • base = base+A • base := by change (1+A) • base=_;rw [add_smul,one_smul]
    calc
      _ = Z⁻¹ • readerJet m base b - Z⁻¹ • (Z • base) := by rw [inv_smul_smul₀ pos.ne']
      _ = Z⁻¹ • ((base+B)-(base+A • base)) := by rw [←smul_sub,z];rfl
      _ = _ := by congr 1;abel
  refine ⟨?_,floor,?_⟩
  · simpa only [vacuumJet,add_sub_cancel_left] using! sale
  change ‖Z⁻¹ • readerJet m base b-base‖≤4*d
  rw [id,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr pos.le)]
  have centered : ‖B-A • base‖≤d+d := calc
    ‖B-A • base‖ ≤ ‖B‖+‖A • base‖ := norm_sub_le ..
    _ ≤ d+d := add_le_add test (by rw [norm_smul,Real.norm_eq_abs];exact ((mul_le_mul_of_nonneg_left unit (abs_nonneg A)).trans_eq (mul_one _)).trans sale)
  have inverse : Z⁻¹ ≤ 2 := by rw [inv_le_comm₀ pos (by norm_num)];norm_num;exact floor
  calc
    _ ≤ 2*(d+d) := mul_le_mul inverse centered (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end YM.Integration.FVA1Physical.FibreMeasure
