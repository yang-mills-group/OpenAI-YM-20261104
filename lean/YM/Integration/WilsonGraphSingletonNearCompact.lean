import YM.Integration.WilsonGraphSingletonNearReanchoring
import YM.GradedFar.Round.Geometry

/-! One compact separated far set contains all reanchored singleton placements on a growing window. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Filter Function Real Set Growth Continuation Continuation.Window
open O O.Enh
open scoped Topology Classical

theorem singletonExterior (s : ℝ) (x y : Points 1) :
    exterior s x y = y - Real.exp (-s) • x := by
  ext1 i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rfl

/-- The compact set and the event are uniform over all the original near and far placements. -/
theorem compactExterior {K S : Set (Points 1)} (near : IsCompact K) (far : IsCompact S)
    (safe : S ⊆ Outside 1) (W : Set Window) :
    ∃ T : Set (Points 1), IsCompact T ∧ T ⊆ Outside 1 ∧
      ∀ᶠ w in windows W, ∀ x ∈ K, ∀ y ∈ S, exterior w.2 x y ∈ T := by
  have opened : IsOpen (Outside 1) := (YM.conf_open 2).preimage (continual continuous_const continuous_id)
  obtain ⟨T,hT,inside,_,c,hc,balls⟩ := Physical.Round.enlarge_knob far opened safe
  obtain ⟨B,hB,bound⟩ := near.isBounded.exists_pos_norm_le
  have vanishes : Tendsto (fun w : Window => Real.exp (-w.2)*B) (windows W) (𝓝 0) := by
    simpa only [Function.comp_apply,Window.sep,zero_mul] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp (windows_separation W)).mul_const B
  refine ⟨T,hT,inside,?_⟩
  filter_upwards [vanishes.eventually (gt_mem_nhds hc)] with w small
  intro x hx y hy
  apply balls y hy
  rw [Metric.mem_closedBall,dist_eq_norm,singletonExterior]
  have diff : y - Real.exp (-w.2) • x - y = -(Real.exp (-w.2) • x) := by abel
  rw [diff,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (bound x hx) (Real.exp_pos _).le).trans small.le

end YM.FVA2.GradedFar.AppointedOneNear
end

