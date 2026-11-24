import YM.FormalOPE.RG10.StationaryMarks.Emboss
import Mathlib.Analysis.SpecialFunctions.Exponential
/-!
 # decoupling multiple deformation estimates from a choice of global regulator state
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open Series.Tested PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
namespace Shed
open Survey
-- use genuine exp series for all bounded real f(y), not charging Taylor radius; costs via index.
lemma expJuice (x:ℝ) (n:ℕ): ‖Real.exp x-referenceCharge n x‖ ≤ ‖x‖^(n+1) * Real.exp ‖x‖:= by
 let f (v:ℝ) (n:ℕ):= v^n/n.factorial
 have hf (v:ℝ):HasSum (f v) (Real.exp v):= by rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
 let k:= n+1
 let r (i:ℕ):= f x (i+k)
 have hr: Summable r:=(summable_nat_add_iff k).mpr (hf x).summable
 have he: (∑' i,r i)=Real.exp x-referenceCharge n x:= by
   apply eq_sub_of_add_eq; rw [add_comm]; exact ((hf x).summable.sum_add_tsum_nat_add k).trans (hf x).tsum_eq
 have hi (i:ℕ): ‖r i‖≤ ‖x‖^k*f ‖x‖ i:= by
  have ha: (i.factorial:ℝ) ≤ ↑(i+k).factorial := by exact_mod_cast Nat.factorial_le (Nat.le_add_right ..)
  have hp : 0 < (i.factorial:ℝ):= by positivity
  unfold r f; rw [norm_div,norm_pow,Real.norm_of_nonneg (by positivity:0≤((i+k).factorial:ℝ)), pow_add,mul_comm (‖x‖^i), ← mul_div_assoc]; gcongr
 rw [← he, ←(hf ‖x‖).tsum_eq,← _root_.tsum_mul_left]; exact (norm_tsum_le_tsum_norm hr.norm).trans (hr.norm.tsum_le_tsum hi ((hf ‖x‖).summable.mul_left _)) -- method deprecated check

lemma tuck (n:ℕ):∃ R:ℝ, 0≤R ∧ ∀ y:ℝ,0≤y → y^n * Real.exp (-y/2) ≤ R*Real.exp (-y/4):= by
 obtain ⟨R,hr,H⟩:= bounded_exp (show (0:ℝ)<1/4 by norm_num) (2*n)
 refine ⟨R,hr,fun y hy=>?_⟩
 apply le_of_mul_le_mul_right (a:=Real.exp (y/4)) _ (Real.exp_pos _); rw [mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add,show -y/2+y/4= - y/4 by ring,show -y/4+y/4=0 by ring,Real.exp_zero,mul_one]
 specialize H (Real.sqrt y) (by positivity); rw [Real.sq_sqrt hy, show -(1/4)*y = -y/4 by ring] at H
 apply le_trans _ H
 apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
 conv_lhs=> rw [← Real.sq_sqrt hy,← pow_mul];
 exact pow_le_pow_left₀ (by positivity) (by linarith) _

lemma seedling (n:ℕ):∃ R:ℝ, 0≤R ∧ ∀ x y a:ℝ, 0≤a → 0≤y → ‖x‖≤a*y → a≤1/2 →
 ‖Real.exp (-y)* (Real.exp x-referenceCharge n x)‖≤ R*a^(n+1)*Real.exp (-y/4):= by
 obtain ⟨R,hr,H⟩:= tuck (n+1); refine ⟨R,hr,fun x y a ha hy hh hk=>?_⟩
 rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
 calc
     _ ≤ Real.exp (-y)* ((a*y)^(n+1) * Real.exp (y/2)) := by
        refine mul_le_mul_of_nonneg_left ((expJuice ..).trans (mul_le_mul (by gcongr) (Real.exp_le_exp.mpr (by nlinarith only [hh, mul_le_mul_of_nonneg_right hk hy])) (Real.exp_pos _).le (by positivity))) (Real.exp_pos _).le
     _ = a^(n+1) * (y^(n+1)*Real.exp (-y/2)) := by rw [show -y/2= -y+y/2 by ring,Real.exp_add,mul_pow]; ring
     _ ≤ _ := by rw [mul_comm R _,mul_assoc]; exact mul_le_mul_of_nonneg_left (H _ hy) (pow_nonneg ha _)
end Shed
end YM.FormalOPE.RG10.StationaryMarks
