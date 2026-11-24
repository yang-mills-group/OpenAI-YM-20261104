import YM.Frontier6.Exact.Collar

/-! Power estimates over given collar. Uniform exterior compacts and phases.
Lets us fix s before testing. All rows exact through one common slope, not a
fit per s. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory Org
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) {d e b w n:ℕ}
private lemma point_power {X:Type*} (J:Set X)(f:E4 → X → ℝ)(a p:ℝ){B:ℝ}(hB:0 ≤ B) (ht:∀ (L:Set E4),IsCompact L → L ⊆ Collar a →∃ B:ℝ,0 ≤ B∧∀ x∈L,∀ y∈J,f x y ≤ B)
  (he:∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈ Collar a, ‖x‖=r→ ∀ y∈J, f x y ≤ B * r^p):
  ∃ A:ℝ, 0 ≤ A ∧ ∀ x∈ Collar a, ∀ y∈J, f x y ≤ A*‖x‖^p:=by
  obtain ⟨c,hc,hh⟩:= mem_nhdsGT_iff_exists_Ioo_subset.mp he
  let L:=Metric.closedBall (0:E4) (a/2) \ Metric.ball 0 c
  have hL:IsCompact L:=(isCompact_closedBall ..).diff Metric.isOpen_ball
  have hl{x}:x∈ L↔ ‖x‖ ≤ a/2 ∧ c ≤ ‖x‖:= by simp [L]
  have hp:L ⊆ Collar a:=fun x hx=> ⟨lt_of_lt_of_le hc ((hl.mp hx).2), (hl.mp hx).1⟩
  have hz:∃ c:ℝ,0 < c ∧ ∀ x∈ L,c ≤ ‖x‖^p:=by
     rcases L.eq_empty_or_nonempty with h|h; · exact ⟨1,one_pos,fun x hx=> by simp_all⟩
     obtain ⟨x,hx,H⟩:= hL.exists_isMinOn h (continuous_norm.continuousOn.rpow_const (fun x hx=> Or.inl (hp hx).1.ne'))
     exact ⟨‖x‖^p,Real.rpow_pos_of_pos (hp hx).1 p,fun x hx=> H hx⟩
  obtain ⟨C,hC,h'⟩:=ht L hL hp; obtain ⟨T,hT,H⟩:=hz
  refine ⟨B + C/T,add_nonneg hB (div_nonneg hC hT.le),fun x hx y hy=>?_⟩
  have hr:0 ≤ ‖x‖^p:= Real.rpow_nonneg (norm_nonneg _) _
  rw [add_mul]; by_cases e: ‖x‖ < c
  · exact (show _ ≤ B*‖x‖^p from hh (⟨hx.1,e⟩: ‖x‖∈ Ioo 0 c) x hx rfl y hy).trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hC hT.le) hr))
  have hX:= hl.mpr ⟨hx.2,le_of_not_gt e⟩
  refine (h' x hX y hy).trans (le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hB hr))); nth_rw 1 [← div_mul_cancel₀ C hT.ne']; exact mul_le_mul_of_nonneg_left (H x hX) (div_nonneg hC hT.le)
private lemma bound_comp {X Y:Type*}[TopologicalSpace X][NormedAddCommGroup Y]{L:Set X}(h:IsCompact L){f:X→ Y}(ht:ContinuousOn f L):∃ B:ℝ,0 ≤ B ∧ ∀ x∈ L, ‖f x‖≤ B:=by
  rcases L.eq_empty_or_nonempty with r|r; · exact ⟨1,by norm_num,by simp [r]⟩
  obtain ⟨x,hx,H⟩:= h.exists_isMaxOn r ht.norm; exact ⟨_,norm_nonneg (f x),fun x hx=> H hx⟩
variable (B:S.Field b)(D:S.Field d)
variable {r:ℝ}{L:Set (Points n)} (hL: IsCompact L)(hc:∀ y∈L,clearC r y)(he:Safe K e r)(hr:0 < r)
include hL hc
lemma rough_pair_compact (hG:Grill C F) (v:Fin n→ S.Tag)(T:Set E4)(ht:IsCompact T)(he:T⊆ Collar r):
    ∃ B':ℝ,0 ≤ B'∧ ∀ s:StateIndex K, ∀ x∈T, ∀ y∈L, ‖pair K B D x s n y v‖ ≤ B':=by
  let p(z:E4 × Points n):=beam z.1 z.2; let Q:= p '' (T ×ˢ L)
  have hQ:Q ⊆ conf (n+2):= by rintro z ⟨⟨x,y⟩,hx,rfl⟩; exact beam_clear (he hx.1) (hc _ hx.2)
  obtain ⟨a,ha,H⟩:=gap_compact ((ht.prod hL).image beam_cont) hQ
  obtain ⟨b,hb,hB⟩:= fields_rough K hG (Fin.cons (α:=fun _=> S.Tag) ⟨d,D⟩ (Fin.cons ⟨b,B⟩ v)) a ha
  refine ⟨b,hb,fun s x hx y hy=> ?_⟩; rw [pair_at]; exact hB _ _ (H (p (x,y)) (mem_image_of_mem p (show (x,y)∈ T ×ˢ L from ⟨hx,hy⟩)))

open Bid Canvas Platform MergeProof MergeProof.Ribbons Next.UVStress Cells Extraction.Around Next.Extract Dash PhysicalNext.Repeat.Legato
variable (H:DualEstimate K pointOf (pair K B D) ((b:ℝ)+d))(hg: Grill C F)(ε:ℝ)(hε:0<ε)
include hr H hg hε
lemma pair_cost (v:Fin n→ S.Tag):
   ∃ B':ℝ,0 ≤ B'∧ ∀ x∈ Collar r,∀ y∈ L,∀ s:StateIndex K, ‖pair K B D x s n y v‖ ≤ B'*‖x‖^(-(b+d:ℝ)-ε):=by
  let N:Unit→ℕ:=fun _=>n
  let u:Tuple S N:=fun _=> v
  let p(y:Points n): Seen N:=fun _=>y
  have hp:= IsCompact.image hL (show Continuous p from continuous_pi fun _=> continuous_id')
  obtain ⟨A,hA,ht⟩:= H Unit N u 0 _ hp (by rintro y ⟨x,hx,rfl⟩ i; exact gap_conf hr.le (hc x hx)) ε hε 1 zero_le_one
  let J:= L ×ˢ (univ:Set (StateIndex K)); let F(x:E4)(y:Points n × StateIndex K):= ‖pair K B D x y.2 n y.1 v‖
  have hH:∀ (T:Set E4),IsCompact T→ T ⊆ Collar r→∃ B:ℝ,0 ≤ B∧∀ x∈T,∀ y∈J,F x y ≤ B:=by intro T hT hh; obtain ⟨B,hB,h⟩:= rough_pair_compact K B D hL hc hg v T hT hh; exact ⟨B,hB,fun x hx y hy=>h y.2 x hx y.1 hy.1⟩
  obtain ⟨W,hW,H⟩:= point_power J F r (-(b+d:ℝ)-ε) hA hH (ht.mono fun z ht x _ (hx:‖x‖=z) y hy=> (by
     simpa only [N, u, p, F, Fintype.sum_unique,one_mul,Nat.cast_zero, zero_sub] using ht x hx _ (mem_image_of_mem p hy.1) (fun _=> y.2) (fun _=> (1:ℂ)) (by simp) (fun e h=>by omega)))
  exact ⟨W,hW,fun x hx y hy s=> H x hx (y,s) (show (y,s)∈J from ⟨hy,mem_univ s⟩)⟩
include he
lemma pair_leftover (v:Fin n→ S.Tag):
   ∃ B':ℝ,0 ≤ B'∧ ∀ x∈ Collar r,∀ y∈ L,∀ s:StateIndex K,
    ‖pair K B D x s n y v-reading K s 0 y v e (capture K e (pair K B D x))‖≤ B'*‖x‖^((e:ℝ)+1-(b+d:ℝ)-ε):=by
  let J:= L ×ˢ (univ:Set (StateIndex K)); let f:= pair K B D; let C'(x:E4):= capture K e (f x)
  let M(x:E4)(y:Points n × StateIndex K):= ‖f x y.2 n y.1 v-reading K y.2 0 y.1 v e (C' x)‖
  obtain ⟨B',hB,ht⟩:= detector_residue K pointOf f ((b:ℝ)+d) H hg (fun x n y=> pair_multi K none B D x y) ε hε e v hL (fun y hy=>gap_conf hr.le (hc y hy))
  have hu :∀ (T:Set E4),IsCompact T→ T ⊆ Collar r→∃ B:ℝ,0 ≤ B∧∀ x∈T,∀ y∈J,M x y ≤ B:=by
    intro T hT hh; obtain ⟨A,hA,h⟩:= rough_pair_compact K B D hL hc hg v T hT hh; obtain ⟨M',hm,hH⟩:= bound_comp hT ((capture_cont K B D he).mono hh)
    obtain ⟨V,hV,hv⟩:= reading_bounded K hg v r hr e
    exact ⟨A+V*M',add_nonneg hA (mul_nonneg hV hm),fun x hx y hy=> (norm_sub_le ..).trans (add_le_add (h y.2 x hx y.1 hy.1) (((reading K y.2 0 y.1 v e).le_opNorm _).trans (mul_le_mul (hv y.2 _ _ (hc y.1 hy.1)) (hH x hx) (norm_nonneg _) hV)))⟩
  obtain ⟨A,hA,H⟩:= point_power J M r ((e:ℝ)+1-(b+d:ℝ)-ε) hB hu (ht.mono fun z ht x hh hx y hy=> ht x hx (pair_observe K B D he hh) y.1 hy.1 y.2)
  exact ⟨A,hA,fun x hx y hy s=> H x hx (y,s) ⟨hy,mem_univ _⟩⟩
omit hL hc hr in
lemma pair_weight (hw:w ≤ e):
   ∃ B':ℝ,0 ≤ B'∧ ∀ x∈ Collar r,
      ‖weight K w (projectBelow K hw (capture K e (pair K B D x)))‖≤ B'*‖x‖^((w:ℝ)-(b+d:ℝ)-ε):=by
  let f:=pair K B D; let U(x):=weight K w (projectBelow K hw (capture K e (f x)))
  obtain ⟨B',hB,ht⟩:= detector_grade K pointOf f ((b:ℝ)+d) H hg (fun x n y=> pair_multi K none B D x y) ε hε hw
  have hU:ContinuousOn U (Collar r):=(weight K w).continuous.comp_continuousOn ((projectBelow K hw).continuous.comp_continuousOn (capture_cont K B D he))
  have hX(T:Set E4)(hT:IsCompact T)(he':T⊆ Collar r):∃ W:ℝ,0 ≤ W∧∀ x∈T,∀ y∈ (univ:Set Unit), ‖U x‖ ≤ W:=by obtain ⟨A,hA,h⟩:= bound_comp hT (hU.mono he'); exact ⟨A,hA,fun x hx y hy=> h x hx⟩
  obtain ⟨W,hW,H⟩:= point_power (univ:Set Unit) (fun x y=> ‖U x‖) r _ hB hX (ht.mono fun z ht x hx he' y _=> ht x he' (pair_observe K B D he hx))
  exact ⟨W,hW,fun x hx=>H x hx () (mem_univ _)⟩
end YM.Frontier6
