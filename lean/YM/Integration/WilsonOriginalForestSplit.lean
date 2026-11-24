import YM.Integration.PhysicalForestFullMoment
import YM.Comparison.RG02.Order.Vacancy

/-! Split the complete vacuum exponential at the same measured Gaussian sample before integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalForestSplit
open Marker Multi Function PertExtension.Series Comparison.RG02 Assembly Order Cumulants
open Extra.Trajectories (pass_add)
open scoped Classical
variable {T:Type} [DecidableEq T] [Fintype T] {J:Census T} {r:ℕ}
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (l:Hot J→ℕ) (M:Hot J→E→ℂ) (A:E→ℝ) (v:E)

theorem occupied :
    series J r (affine l M A v) = bottom J r (series J r (affine l M A v)) +
      series J r (curve l M v) := by
  apply Join.both_parts
  intro t u
  rw [Poly.part_plus,bottom_value]
  by_cases ht:t=J.quiet
  · subst t
    have zero:(series J r (curve l M v)).part (Join.pair J.quiet u)=0 := by
      rw [polarization,mark_curve_quiet,mul_zero]
    rw [if_pos rfl,zero,add_zero]
  · rw [if_neg ht,zero_add,polarization,polarization,affine,map_add,Poly.part_plus,
        realCoeff,beads,if_neg ht,zero_add]

variable {I:Type} [Fintype I] [DecidableEq I]
variable (w:E) (move:(I→ℝ)→ₗ[ℝ]E) (z:I→ℝ)

theorem exponential :
    let L := lit (Board J r) (fun i=> Cloud.paint z (generator w move l M A r i))
    L.pass = bottom J r L.pass * (series J r (curve l M (translate w move z))).pass := by
  intro L
  have hi: L = series J r (affine l M A (translate w move z)) := colors ..
  have parts: L = bottom J r L + series J r (curve l M (translate w move z)) := by
    rw [hi]
    exact occupied l M A _
  have quiet:(bottom J r L).part (Board J r).quiet=0 :=by
    rw [← Join.pair_quiet,bottom_value,if_pos rfl,Join.pair_quiet]
    exact part_lit_quiet _
  have full: (bottom J r L).pass = bottom J r L.pass := by
    simp only [Poly.pass,map_sum,map_smul,map_pow]
  calc
    L.pass = (bottom J r L + series J r (curve l M (translate w move z))).pass := congrArg Poly.pass parts
    _ = _ := by rw [pass_add quiet (mark_books l M _ r),full]

end YM.Integration.WilsonOriginalForestSplit
