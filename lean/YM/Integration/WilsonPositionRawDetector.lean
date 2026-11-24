import YM.Integration.WilsonPositionRawMesh

/-! Set the auxiliary bare Wilson variable from its finite measured position
detector. The admissible interval uses its actual coefficients and its
original eventually nonzero linear term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawDetector
open Finset Function Filter Set XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register
open WilsonPositionRawMesh
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh) (q : ℕ)

def linear : ℝ := (PowerSeries.coeff 1 (Rose.chosen Z.scheme Z.criterion m)).re

theorem ready (hG : G.Simple) : ∀ᶠ i : ℕ in atTop, 1/2 ≤ linear Z (Z.run.step i) := by
  have h := (Rose.xc Z.scheme Z.criterion hG).comp (goesFront (Expense.Stretched.runs Z.run))
  have k : Tendsto (fun i : ℕ => linear Z (Z.run.step i)) atTop (𝓝 1) :=
    Complex.continuous_re.continuousAt.tendsto.comp h
  exact (k.eventually_const_lt (by norm_num)).mono fun _ e=>e.le

theorem remainder (hq : 1 ≤ q) (x : ℝ) (unit : |x| ≤ 1) :
    |forward Z m q x-linear Z m*x| ≤ mass Z m q*|x|^2 := by
  let one : Fin (q+1) := ⟨1,by omega⟩
  let terms (k : Fin (q+1)) := detector Z m q k*x^(k:ℕ)
  have remove : forward Z m q x-linear Z m*x = ∑ k ∈ univ.erase one, terms k := by
    have sum_all := sum_erase_add _ terms (mem_univ one)
    change (∑ k,terms k)-linear Z m*x = _
    rw [←sum_all]
    simp [terms,one,detector,linear]
  rw [remove,mass,sum_mul]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ k ∈ univ.erase one, |detector Z m q k| * |x|^2 := by
      apply sum_le_sum
      intro k hk
      dsimp only [terms]
      rw [abs_mul,abs_pow]
      by_cases zero : (k:ℕ)=0
      · simp [detector,zero,PowerSeries.coeff_zero_eq_constantCoeff_apply,Rose.zero_choice]
      · have h : (k:ℕ) ≠ 1 := fun eq => (mem_erase.mp hk).1 (Fin.ext eq)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg _) unit (by omega)) (abs_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset ..) fun k _ _=>mul_nonneg (abs_nonneg _) (sq_nonneg _)

def bare (t : ℝ) : ℝ := if h : ∃ x : ℝ, |x| ≤ 4*|t| ∧ forward Z m q x = t then Classical.choose h else 0

theorem set (hq : 1 ≤ q) (first : 1/2 ≤ linear Z m) (t : ℝ) (small : 4*|t| ≤ 1)
    (rent : 16*mass Z m q*|t| ≤ 1) :
    |bare Z m q t| ≤ 4*|t| ∧ forward Z m q (bare Z m q t) = t := by
  let radius := 4*|t|
  have rp : 0 ≤ radius := by dsimp [radius]; positivity
  have high := remainder Z m q hq radius (by rw [abs_of_nonneg rp]; exact small)
  have low := remainder Z m q hq (-radius) (by rw [abs_neg,abs_of_nonneg rp];exact small)
  rw [abs_of_nonneg rp] at high
  rw [abs_neg,abs_of_nonneg rp] at low
  have paid := mul_le_mul_of_nonneg_right rent (abs_nonneg t)
  have firstPaid := mul_le_mul_of_nonneg_right first (abs_nonneg t)
  have span : t ∈ Icc (forward Z m q (-radius)) (forward Z m q radius) := by
    constructor
    · dsimp [radius] at low
      nlinarith only [(abs_le.mp low).2,firstPaid,paid, neg_abs_le t]
    · dsimp [radius] at high
      nlinarith only [(abs_le.mp high).1,firstPaid,paid, le_abs_self t]
  have smooth : Continuous (forward Z m q) := by unfold WilsonPositionRawMesh.forward;fun_prop
  obtain ⟨x,hx,eq⟩ := intermediate_value_Icc (neg_le_self rp) smooth.continuousOn span
  have choices : ∃ x : ℝ, |x| ≤ 4*|t| ∧ forward Z m q x = t :=
    ⟨x,abs_le.mpr hx,eq⟩
  rw [bare,dif_pos choices]
  exact Classical.choose_spec choices

end YM.Integration.WilsonPositionRawDetector
