import YM.XSpace.Layout

/-! # These regulator choices admit every fixed geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Run
open Filter Function Set MeasureTheory
open scoped ContDiff Topology
variable (V : Run)
lemma width_end : Tendsto (fun k=>(V.step k).size) atTop atTop:=by
  simp_rw [Mesh.run_size]
  have hh:Tendsto (fun n:ℕ=>V.reserve*n*n) atTop atTop:= by
    apply tendsto_atTop_mono' _ _ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with i hi
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos V.spare hi)
  exact Tendsto.const_mul_atTop (by exact_mod_cast V.finalSide.side.pos) ((tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < V.ratio by have ht:=V.large; exact_mod_cast (show 1<V.ratio by omega))).comp hh)
lemma fit_end {p : ℕ} {K : Set (Points p)} (h : IsCompact K) : ∀ᶠ n in atTop, (V.step n).Fits K :=by
  obtain ⟨y,hy⟩ := (h.image continuous_norm).bddAbove
  filter_upwards [V.width_end.eventually_ge_atTop (16*y)] with n hn x hx i j
  exact (PiLp.norm_apply_le (x i) j).trans ((PiLp.norm_apply_le x i).trans ((hy (Set.mem_image_of_mem _ hx)).trans (by linarith)))
lemma spacing_end : Tendsto (fun n=>(V.step n).spacing) atTop (𝓝 0) :=by
  apply tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<V.ratio by have h:=V.large; omega))) -- ℕ semiring?
end YM.XSpace.Run
