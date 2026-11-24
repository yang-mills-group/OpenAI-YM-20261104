import YM.Frontier6.Exact.Track

/-! The recenterable dual estimate. Shape parameters needn't be continuous
for this step. (Verify continuity separately on the collar.) -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory Org
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(s:StateIndex K) {e d n:ℕ}
variable {X:Type*}(D:ℝ → Set X)(f:X → Reader K)(σ:ℝ)(p:X→E4)

def shiftedReader (p:E4) (f:Reader K):Reader K:= fun s n y v=> f s n (Points.across (-p) y) v
lemma DualEstimate.recenters (h:DualEstimate K D f σ)(hL: Grill C F)(hp:∀ᶠ r in 𝓝[>] 0, ∀ x∈D r, ‖p x‖ ≤ r):
    DualEstimate K D (fun x => shiftedReader K (p x) (f x)) σ :=by
  intro I inst n v d L hK hc ε hε B hB
  obtain ⟨a,ha,hy⟩:= family_gap hK hc
  let U:= Metric.closedBall (0:E4) (a/2)
  let W (i:I)(x:E4 × Seen n):= Points.across (-x.1) (x.2 i)
  let P(i:I):= W i '' (U ×ˢ L)
  have hU(x:E4):x∈U↔ ‖x‖ ≤ a/2:= mem_closedBall_zero_iff
  have hW(i:I):IsCompact (P i):= ((isCompact_closedBall ..).prod hK).image (show Continuous (W i) by unfold W Points.across points; fun_prop)
  have hP (i:I):∀ y∈P i, Points.cons 0 y∈conf _:=by
     rintro y ⟨⟨x,z⟩,hx,rfl⟩
     have he:= clear_move (-x) (clear_translation ((hU x).mp hx.1) (hy z hx.2 i)); rw [across_cons,add_neg_cancel] at he; exact gap_conf (half_pos ha).le he
  let H:=hand K d
  let T x:= handPoint K (f x) d H
  let J:=Fin (d+1)
  let w (j:J):j.val ≤ d:=by unfold J at j; omega
  let X'(x:X)(j:J):= weight K j (projectBelow K (w j) (T x))
  choose A hA hq using fun i:I=> h.hand_residue K D f σ hL H (v i) (L:=P i) (hW _) (hP _) ε hε
  choose G' hG hg using fun j:J=> kills_order K hL v (w j) ha hB
  choose M hM hm using fun j:J=> h.hand_grade K D f σ H (w j) ε hε
  let B':= ∑ i:I, B * A i; let B'':= ∑ j:J, G' j * M j
  have ht:0 ≤ B':= Finset.sum_nonneg fun i _=> mul_nonneg hB (hA i)
  refine ⟨B'+B'',add_nonneg ht (Finset.sum_nonneg fun j _=> mul_nonneg (hG j) (hM j)),?_⟩
  filter_upwards [self_mem_nhdsWithin, hp,eventually_all.mpr hq,eventually_all.mpr hm, mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (half_pos ha)),mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (zero_lt_one))] with r hr hp hq hm hr₁ hr₂ x hx y hy' u c hc' hu
  have hr:0 < r:= mem_Ioi.mp hr
  let x':=p x; have hU':x'∈U:= (hU x').mpr ((hp x hx).trans hr₁)
  let z(i:I):= W i (x',y)
  let L'(i:I):= f x (u i) (n i) (z i) (v i)
  let V'(i:I):= reading K (u i) x' (y i) (v i) d (T x)
  let Q:= survey K v d y u c x'; let Y:= r^((d:ℝ)-σ-ε)
  have ht'(i:I): V' i=reading K (u i) 0 (z i) (v i) d (T x):=by
     have he:= readings_shift K (u i) x' (y i) (v i) (T x) (gap_conf (half_pos ha).le (clear_translation ((hU _).mp hU') (hy y hy' i))) (-x'); rw [add_neg_cancel] at he; exact he.symm
  have hx' : r^((d:ℝ)+1-σ-ε) ≤ Y:= Real.rpow_le_rpow_of_exponent_ge hr hr₂ (by linarith)
  have hx''(i:I): ‖c i*(L' i-V' i)‖ ≤ (B*A i)*Y:=by
     rw [ht',norm_mul,mul_assoc]; exact mul_le_mul (hc' i) ((hq i x hx (z i) (mem_image_of_mem _ (show (x',y)∈ U ×ˢ L from ⟨hU',hy'⟩)) (u i)).trans (mul_le_mul_of_nonneg_left hx' (hA i))) (norm_nonneg _) hB
  have hxH(i:I):=hc' i
  have he:Q (T x)= ∑ i:I,c i*V' i:= survey_at ..
  have heq (j:J):Q (higher K (w j) (X' x j))=survey K v j y u c x' (X' x j):= by
     unfold Q; rw [survey_at,survey_at]; refine Finset.sum_congr rfl fun i _=> congr_arg (c i * ·) (?_)
     rw [reads_at,reads_at]; apply (inception K (u i)).kernels (w j) _ ?_; exact gap_conf (half_pos ha).le (clear_translation ((hp x hx).trans hr₁) (hy y hy' i))
  have hv(j:J): ‖Q (higher K (w j) (X' x j))‖ ≤ (G' j * M j)*Y:=by
     rw [heq]; apply ((survey K v j y u c x').le_opNorm _).trans
     refine (mul_le_mul (hg j r hr.le hr₁ (p x) (hp x hx) y (hy y hy') u c hc' hu) (hm j x hx) (norm_nonneg _) (mul_nonneg (hG j) (pow_nonneg hr.le _))).trans_eq ?_
     rw [mul_mul_mul_comm,← Real.rpow_natCast,← Real.rpow_add hr, Nat.cast_sub (w j)]
     unfold Y; congr 2; ring
  have hV:‖Q (T x)‖ ≤ B''*Y:= by
     rw [← weights_span K (T x),map_sum]; unfold B''; rw [Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>hv i))
  change ‖∑ i:I, c i * L' i‖ ≤ (B'+B'')*Y
  rw [show ∑ i:I,c i * L' i=(∑ i:I,c i * (L' i-V' i))+ Q (T x) by simp only [he,mul_sub,Finset.sum_sub_distrib, sub_add_cancel],add_mul]
  apply (norm_add_le ..).trans; unfold B'; rw [Finset.sum_mul]; exact add_le_add ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> hx'' i))) hV
end YM.Frontier6
