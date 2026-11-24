import YM.UVExt.LoopRestraint
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Laurent Lattice RG Wilson Precision Exterior Bid Matrix Set
open scoped Classical Topology ContDiff BigOperators
variable {G : Gauge} {n : Side} (v : fieldDir G n 1)

def loopprice (G : Gauge) (s Λ : ℝ) := 2*(K G)^2*Λ*s⁻¹*16^2
set_option maxHeartbeats 160000 in
lemma twin_zero {Z : PathData G} {q σ C Λ} (h : Z.Bounds q σ C Λ) (j) (hj : j<2) : tag j (spiral (wick Z) v)=0 := by
   rw [tag_spiral v (shadow_pay _ h) h.width]
   suffices ∀ a : Signed, ∀ x : Site n, tag j (song (pulled v a) x (wick Z |>.loop))=0 by
       simp_rw [this]; simp
   intro a x; unfold tag; rw [← (song_sum (pulled v a) (shadow_pay _ h).coeffTwo h.width _ _ _).tsum_eq]
   suffices (∑' i, ((wick Z).loop i) * (0:ℝ))=0 by
      convert this using 1; apply tsum_congr; intro d; exact congr_arg ((wick Z).loop d * ·) ((coil_rates (pulled v a) x d).1 j hj)
   simp
lemma spiral_price {Z : PathData G}{q σ C Λ} (h : Z.Bounds q σ C Λ) : |tag 2 (spiral (wick Z) v)| ≤ (Fintype.card (Site n):ℝ)* loopprice G σ Λ*gradD v*‖dColor G n 1 v‖ := by
   rw [tag_spiral v (shadow_pay _ h) h.width]
   let D:=gradD v; let T:= ‖Exterior.dColor G n 1 v‖
   have hD : 0≤D := norm_nonneg _
   have hp (i : Signed) (x : Site n) : |tag 2 (song (pulled v i) x (wick Z).loop)| ≤ loopprice G σ Λ * D * T := by
       have ht : 0≤ 2*(K G)^2*Λ*σ⁻¹ := by positivity [h.width,show 0≤Λ from (tsum_nonneg h.two.1).trans h.two.2.2]
       apply (twin_frame (pulled v i) h _).trans
       convert (mul_le_mul (mul_le_mul_of_nonneg_left (grad_pull v i) ht) (paid_curl v i).2 (norm_nonneg _) (mul_nonneg ht (by positivity : 0≤16*D))) using 1 <;> first|rfl|unfold loopprice; ring
   rw [abs_mul,abs_of_nonneg (by positivity:_ ≤ (Fintype.card Signed:ℝ)⁻¹)]
   calc
      _ ≤ (Fintype.card Signed:ℝ)⁻¹ * ∑ _i:Signed,∑ _x:Site n, loopprice G σ Λ *D*T := mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun x _=>hp i x))) (by positivity)
      _ = _ := by simp; unfold loopprice D T; field_simp <;> ring
lemma twin_near {M : ℕ→PathData G} {Z : Shadow G} {q σ C Λ} (h : Passing M Z σ C Λ q) :
     (∀ j<2,tag j (spiral Z v)=0) ∧ |tag 2 (spiral Z v)| ≤ (Fintype.card (Site n):ℝ)*loopprice G σ Λ * gradD v * ‖Exterior.dColor G n 1 v‖ := by
    have ht j := h.flow_loop (q:=j) (v:=v)
    exact ⟨fun j hj=>(tendsto_nhds_unique (ht j) (tendsto_const_nhds.congr' (h.mask.mono fun i hi=> (twin_zero v hi j hj).symm))), le_of_tendsto (Tendsto.abs (ht 2)) (h.mask.mono fun i hi=>spiral_price v hi)⟩

end YM.UVExt.Paths
