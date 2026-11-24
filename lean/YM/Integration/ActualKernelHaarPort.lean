import YM.Integration.ActualKernelHaarPrice
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Every-port normalized Haar coefficient bill

Analytic derivative symmetry moves the fixed coordinate to any prescribed
port through the literal cycleRange/insertNth identity. The tail tuple is
unchanged. Factorial normalization can only decrease its norm.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualKernelHaarPort
open Filter Function Finset Lattice RG Precision Tree
open Push.Uniform Comparison.RG02
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {q : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S q P O) (F : Forest S.ratio)

include K in
private theorem kernel_log_smooth :
    ContDiffAt ℝ ω (fun z : Positions (Push.Uniform.Joint F G) =>
      Real.log (∏ b : F.Free, O.J ((paint F G z).2 b))) 0 := by
  have hsum : ContDiffAt ℝ ω
      (ActualKernelHaarPrice.sumLog (G := G) F) 0 := by
    change ContDiffAt ℝ ω (fun z : Positions (Push.Uniform.Joint F G) =>
      ∑ b : F.Free, Real.log (LocalH.spin G ((paint F G z).2 b))) 0
    apply ContDiffAt.sum
    intro b _
    have hp : ContDiffAt ℝ ω
        (fun z : Positions (Push.Uniform.Joint F G) => (paint F G z).2 b) 0 := by
      fun_prop
    have hs := (LocalH.spin_deriv G
      ((paint F G (0 : Positions (Push.Uniform.Joint F G))).2 b)).comp 0 hp
    exact hs.log (by simp [LocalH.spin_zero])
  exact hsum.congr_of_eventuallyEq (ActualKernelHaarPrice.kernel_log_germ K F)

include K in
/-- The complete original kernel log is analytic at the origin in these coordinates. -/
theorem kernel_log_contDiffAt :
    ContDiffAt ℝ ω (fun z : Positions (Push.Uniform.Joint F G) =>
      Real.log (∏ b : F.Free, O.J ((paint F G z).2 b))) 0 :=
  kernel_log_smooth K F

include K in
private theorem entry_insert (k : ℕ) (j : Fin (k + 1))
    (a : Push.Uniform.Joint F G) (v : Fin k → Push.Uniform.Joint F G) :
    entry (fun z => Real.log (∏ b : F.Free, O.J ((paint F G z).2 b)))
      0 (Fin.insertNth j a v) =
    entry (fun z => Real.log (∏ b : F.Free, O.J ((paint F G z).2 b)))
      0 (Fin.cons a v) := by
  unfold entry
  simpa only [Function.comp_def, Fin.cons_apply_cycleRange] using
    (kernel_log_smooth K F).iteratedFDeriv_comp_perm
      (fun t => bolt ((Fin.cons a v : Fin (k + 1) → Push.Uniform.Joint F G) t))
      j.cycleRange

include K in
/-- Every prescribed positive-order port has the same full normalized bill.
All remaining physical/free coordinates are summed, with no site factor. -/
theorem kernel_normalized_port_l1 (k : ℕ) (j : Fin (k + 1))
    (a : Push.Uniform.Joint F G) :
    (∑ v : Fin k → Push.Uniform.Joint F G,
      ‖(((k + 1).factorial : ℝ)⁻¹) •
        entry (fun z => Real.log (∏ b : F.Free, O.J ((paint F G z).2 b)))
          0 (Fin.insertNth j a v)‖) ≤ ActualKernelHaarPrice.onePortCost G k := by
  have hfac : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
  have hinv : ‖(((k + 1).factorial : ℝ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact inv_le_one_of_one_le₀ hfac
  calc
    _ ≤ ∑ v : Fin k → Push.Uniform.Joint F G,
        ‖entry (fun z => Real.log (∏ b : F.Free, O.J ((paint F G z).2 b)))
          0 (Fin.cons a v)‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [entry_insert K F k j a v, norm_smul]
      exact (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ActualKernelHaarPrice.onePortCost G k :=
      ActualKernelHaarPrice.kernel_one_port_l1 K F k a

end YM.Integration.ActualKernelHaarPort
end
