import YangMills.WilsonProof.NativeSupport.IssuedBank.PhysicalColourChart
import YangMills.WilsonProof.NativeSupport.IssuedBank.OriginalOneLoop

set_option autoImplicit false

namespace IssuedBank.WilsonSlope

open YangMills YangMills.Wilson IssuedBank.PhysicalColourChart
open scoped BigOperators InnerProductSpace
noncomputable section

variable {g : GaugeGroup} (B : Maxwell.Reference g)

private abbrev unit (i : Fin B.m) : Maxwell.Color B.m := EuclideanSpace.single i 1

private def raw (i j : Fin B.m) := B.matrix (unit B i) * B.matrix (unit B j) -
  B.matrix (unit B j) * B.matrix (unit B i)

private def charge (i j : Fin B.m) : ℝ := -((raw B i j * raw B i j).trace).re

private theorem matrixBracket (i j : Fin B.m) :
    g.core.colorMat (g.core.ad (frame B i) (frame B j)) = raw B i j := by
  rw [g.core.colorMat_ad, frame_apply, frame_apply, represented, represented]
  rfl

private theorem contribution (i j : Fin B.m) : charge B i j =
    ((g.n+1 : ℕ) : ℝ) * ‖g.core.ad (frame B i) (frame B j)‖ ^ 2 := by
  unfold charge
  rw [← matrixBracket B i j]
  exact (g.core.trace_color _ _).trans (congrArg (((g.n+1 : ℕ) : ℝ) * ·) (real_inner_self_eq_norm_sq _))

/-- Sum over the actual independently supplied frame, with its original index. -/
private theorem killSum (x : g.core.Color) :
    g.core.minusKilling x x = ∑ i, ‖g.core.ad x (frame B i)‖ ^ 2 := by
  let b := frame B
  simp only [YM.Gauge.minusKilling, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, b.coe_toBasis_repr_apply,
    Module.End.mul_apply, b.repr_apply_apply, b.coe_toBasis]
  rw [← YM.Gauge.ad_skew]
  exact real_inner_self_eq_norm_sq _

theorem row (hg : g.IsSimple) (i : Fin B.m) :
    ∑ j, charge B i j = ((g.n+1 : ℕ) : ℝ) * g.core.casimir := by
  simp_rw [contribution]
  rw [← Finset.mul_sum, ← killSum]
  congr 1
  calc
    _ = g.core.casimir * inner ℝ (frame B i) (frame B i) :=
      YM.Gauge.trace_adjoint (g.coreSimple hg) _ _
    _ = g.core.casimir := by rw [real_inner_self_eq_norm_sq, (frame B).norm_eq_one i]; ring

theorem original (hg : g.IsSimple) :
    2 * wilsonOneLoop B = g.core.slopeConstant := by
  obtain ⟨i, _, _⟩ := IssuedBank.OriginalOneLoop.occupied B hg
  have count : (B.m : ℝ) ≠ 0 := (show 0 < (B.m : ℝ) by exact_mod_cast (Nat.zero_le i.val).trans_lt i.isLt).ne'
  have dim : ((g.n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  change 2 * (11 * ((∑ i, ∑ j, charge B i j) / (((g.n+1 : ℕ) : ℝ) * (B.m : ℝ))) / (48 * Real.pi ^ 2)) =
    11 * g.core.casimir / (24 * Real.pi ^ 2)
  simp_rw [row B hg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [count, dim, Real.pi_ne_zero]
  ring


end
end IssuedBank.WilsonSlope
