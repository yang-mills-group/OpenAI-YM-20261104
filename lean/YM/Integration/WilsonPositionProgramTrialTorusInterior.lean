import YM.Integration.WilsonPositionProgramTrialTorusEnergy
import YM.Lattice.Support

/-! One interior step in the original scalar four-torus. Its energy estimate
has no volume factor, so it can be iterated after fixing the finite side. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialTorusInterior
open Finset Lattice Pert.Orb
open scoped BigOperators Classical
variable {n : Side}

def masked (s : Finset (Site n)) (u : Site n → ℝ) (x : Site n) : ℝ := if x ∈ s then u x else 0
def stock (s : Finset (Site n)) (u : Site n → ℝ) : ℝ := ∑ x, (masked s u x)^2

theorem axis (χ u : Site n → ℝ) (B : Finset (Site n)) (w : ℝ) (i : Axis)
    (pace : ∀ x, |ahead i χ x| ≤ w)
    (live : ∀ x, ahead i χ x ≠ 0 → x ∈ B ∧ x+step i ∈ B) :
    (∑ x, (ahead i χ x)^2*u x*u (x+step i)) ≤ w^2 * stock B u := by
  let f := masked B u
  have shifted : (∑ x, (f (x+step i))^2) = ∑ x, (f x)^2 :=
    Equiv.sum_comp (Equiv.addRight (step i)) (fun x => (f x)^2)
  calc
    _ ≤ ∑ x, w^2/2 * ((f x)^2 + (f (x+step i))^2) := by
      apply sum_le_sum
      intro x _
      by_cases zero : ahead i χ x = 0
      · simp only [zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_mul]
        positivity
      obtain ⟨one,two⟩ := live x zero
      simp only [f,masked,if_pos one,if_pos two]
      have scale : (ahead i χ x)^2 ≤ w^2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (pace x))).mpr (pace x) |>.trans_eq' (sq_abs _)
      have both := mul_le_mul_of_nonneg_right scale
        (add_nonneg (sq_nonneg (u x)) (sq_nonneg (u (x+step i))))
      nlinarith only [both, mul_nonneg (sq_nonneg (ahead i χ x)) (sq_nonneg (u x-u (x+step i)))]
    _ = _ := by
      rw [←mul_sum,sum_add_distrib,shifted]
      change _ = w^2 * ∑ x, (f x)^2
      ring

theorem original (χ u : Site n → ℝ) (A B : Finset (Site n)) (w : ℝ)
    (valid : ∀ x, χ x ≠ 0 → lap u x = 0)
    (pace : ∀ i x, |ahead i χ x| ≤ w)
    (live : ∀ i x, ahead i χ x ≠ 0 → x ∈ B ∧ x+step i ∈ B)
    (inside : ∀ i x, x ∈ A → χ x = 1 ∧ χ (x+step i) = 1) (a : Axis) :
    stock A (ahead a u) ≤ 4*w^2*stock B u := by
  have inner : stock A (ahead a u) ≤ ∑ x, (ahead a (χ*u) x)^2 := by
    apply sum_le_sum
    intro x _
    by_cases h : x ∈ A
    · obtain ⟨hx,hy⟩:=inside a x h
      simp only [masked,if_pos h,ahead,Pi.mul_apply,hx,hy,one_mul,le_rfl]
    · simp only [masked,if_neg h,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
      positivity
  apply inner.trans
  calc
    _ ≤ ∑ i : Axis, ∑ x, (ahead i (χ*u) x)^2 :=
      single_le_sum (f:=fun i : Axis => ∑ x, (ahead i (χ*u) x)^2)
        (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_univ a)
    _ = _ := WilsonPositionProgramTrialTorusEnergy.harmonic u χ valid
    _ ≤ ∑ _i : Axis, w^2*stock B u := sum_le_sum (fun i _ => axis χ u B w i (pace i) (live i))
    _ = _ := by simp [Axis, mul_assoc]

end YM.Integration.WilsonPositionProgramTrialTorusInterior
