import YM.Integration.FVA1Physical.Round2.ChartSubsets
import YM.MSbar.CrossH.Stout

/-! A genuine derivative of the unrestricted physical reading is recovered
from the affine slice containing exactly the coordinates in its test word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice Push.Uniform MSbar MSbar.CrossH MSbar.Lis
open scoped Classical Topology ContDiff
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem coordinate_word_bound (f : Positions σ → ℝ) (Z : Positions σ) (l : List σ)
    (smooth : ContDiffAt ℝ l.length f Z) {M : ℝ}
    (est : ‖iteratedFDeriv ℝ l.length (fun y=>f (Z+coordinateProjection l.toFinset y)) 0‖≤M) :
    |buoy f Z l|≤M := by
  let K:=l.toFinset
  let P:=coordinateProjection K
  let F:=f ∘ coordinateSlice K Z
  have center : coordinateSlice K Z Z=Z := by funext i; simp [coordinateSlice]
  have idn (y:Positions σ) : coordinateSlice K Z (Z+y)=Z+P y := by
    funext i
    by_cases h:i∈K <;> simp [P,coordinateSlice,coordinateProjection,h]
  have full : ContDiffAt ℝ l.length f (coordinateSlice K Z Z) := center.symm ▸ smooth
  have part : ContDiffAt ℝ l.length F Z := by
    apply full.comp
    rw [show coordinateSlice K Z = fun x=>coordinateSlice K Z 0+P x from funext (coordinateSlice_affine K Z)]
    exact contDiffAt_const.add P.contDiff.contDiffAt
  have same:=coordinateSlice_buoy K Z f l Z l.length full le_rfl
  rw [if_pos (show ∀ i∈l,i∈K from fun i hi=>List.mem_toFinset.mpr hi),center] at same
  have eqn : (fun y=>F (Z+y))=fun y=>f (Z+P y) := funext fun y=>congrArg f (idn y)
  have fee : ‖iteratedFDeriv ℝ l.length F Z‖≤M := by
    rw [←eqn,iteratedFDeriv_comp_add_left,add_zero] at est
    exact est
  rw [←same,CrossH.chain F l l.length Z part le_rfl,←Real.norm_eq_abs]
  exact (ContinuousMultilinearMap.le_opNorm ..).trans (by simpa only [norm_bolt,prod_const_one,mul_one] using fee)

end YM.Integration.FVA1Physical.Round2.Curvature
