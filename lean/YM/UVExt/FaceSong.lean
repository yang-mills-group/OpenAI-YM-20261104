import YM.UVExt.StreamReceipt

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Real Wilson Precision Lattice Bid Exterior
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {N : Side} (v : Dir G N)
variable {C σ Λ : ℝ} {p : Clip} {R : PathData G}

def ink (R : PathData G) b := pool (fun i=> (R.row b i).1) (fun i=> (R.row b i).2)

def ash (R : PathData G) b := fun i : Slot×Slot => ink R b i.1 * ink R b i.2

def note (R : PathData G) b := fun i : (Slot×Slot)×G.ColorIndex => ash R b i.1

abbrev SlotSize (s : Slot) := (s.length:ℝ)

lemma raw_money (h : R.Bounds p σ C Λ) (b : PlaqAxes) : Carries C σ (fun i=>SlotSize (R.row b i).2) (fun i=>(R.row b i).1) :=
    ⟨fun _=>Nat.cast_nonneg _,fun k=>by simp_rw [mul_comm (Real.exp _), Real.norm_eq_abs]; exact (h.rows b).2.1.sum_le_tsum k (fun i _=>(h.rows b).1 i) |>.trans (h.rows b).2.2⟩
lemma row_money (h : R.Bounds p σ C Λ) (b : PlaqAxes) : Carries C σ SlotSize (ink R b) := pool_money (s:=fun i=>(R.row b i).2) (raw_money h _) h.width (fun _=>le_rfl) (fun _=>Nat.cast_nonneg _)
lemma ash_money (h : R.Bounds p σ C Λ) (b : PlaqAxes) (hC : 0≤C) : Carries (C^2) σ (fun i=>SlotSize i.1+SlotSize i.2) (ash R b)  := by change Carries _ _ _ (fun i : Slot×Slot=> _ * _); simpa [pow_two] using squared_money (row_money h b) (row_money h b) hC

def parallel (p : (Slot×Slot)×G.ColorIndex) : Token G 2 := ⟨![p.1.1,p.1.2],fun _=>p.2⟩
lemma note_money (h : R.Bounds p σ C Λ) (b : PlaqAxes) (hC : 0≤C) : Carries ((Fintype.card G.ColorIndex:ℝ) * C^2) σ (fun i=>breath (parallel i)) (note R b) := by
  have hA := product_money (σ:=σ) (C:=(Fintype.card G.ColorIndex:ℝ)*C^2) (R:=fun i=>fun _:G.ColorIndex=>ash R b i) (fun i=>SlotSize i.1+SlotSize i.2) (fun _=>by positivity) (fun i=> (Fintype.card G.ColorIndex:ℝ)*|ash R b i|) (fun i=>by simp) ?ht
  on_goal 2 =>
    simp_rw [mul_right_comm (Fintype.card G.ColorIndex:ℝ), mul_assoc (Fintype.card G.ColorIndex:ℝ)] -- may fail
    let f i := Real.exp (σ*(SlotSize i.1+SlotSize i.2))*|ash R b i|
    refine ⟨fun _=>by positivity,?_,?_⟩
    · exact (ash_money h b hC).paid.2.1.mul_left (Fintype.card _:ℝ)
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (ash_money h b hC).paid.2.2 (Nat.cast_nonneg _)
  change Carries _ _ _ (fun i : (Slot×Slot)×G.ColorIndex=>ash R b i.1)
  simp only [parallel,breath,Fin.sum_univ_two,Nat.cast_add,Matrix.cons_val_zero,Matrix.cons_val_one]; exact hA

lemma parallel_top : Tendsto (fun i : (Slot×Slot)×G.ColorIndex=> breath (parallel i)) cofinite atTop :=
    (breath_top 2).comp ((show Function.Injective (parallel (G:=G)) from fun i j h=> Prod.ext (Prod.ext (show _ from congr_arg (fun t=>t.1 0) h) (show _ from congr_arg (fun t=> t.1 1) h)) (show _ from congr_arg (fun t=>t.2 0) h)).tendsto_cofinite)

def words (x : Site N) (W : (Slot×Slot)×G.ColorIndex → ℝ) t := ∑' i,W i*stream v x (parallel i) t

lemma words_sum (x) {W : (Slot×Slot)×G.ColorIndex →ℝ} q t (hr : Carries C σ (breath ∘ parallel) W) (he : 0 < σ) : Summable (fun i=> W i*iteratedDeriv q (stream v x (parallel i)) t) :=
    (weigh_terms (K G ^ 2) ((2:ℝ)*driftPrice v) hr he (by positivity) (by positivity [driftPrice_pos v]) (fun i=>stream v x (parallel i)) q (fun i=>stream_cap v q x (parallel i)) (fun i=>stream_ana v x _) t).1 q le_rfl |>.of_norm
lemma words_flow (x) {W : (Slot×Slot)×G.ColorIndex →ℝ} (hr : Carries C σ (breath ∘ parallel) W) (he : 0 < σ) : ContDiff ℝ ∞ (words v x W) :=
    weigh_smooth ((K G)^2) (2*driftPrice v) _ (by positivity) (by positivity [driftPrice_pos v]) (fun i=>stream_ana v _ (parallel i)) (fun _ i=>stream_cap v _ _ (parallel i)) he hr
lemma words_tends {ι : Type*} {F : Filter ι} [F.NeBot] (M : ι → (Slot×Slot)×G.ColorIndex→ℝ) {W} (h : ∀ᶠ i in F,Carries C σ (breath ∘ parallel) (M i)) (ht : Tendsto M F (𝓝 W)) (hs : 0 < σ) x q t :
    Tendsto (fun i=> iteratedDeriv q (words v x (M i)) t) F (𝓝 (iteratedDeriv q (words v x W) t)) :=
  weigh_pass ((K G)^2) (2 * driftPrice v) _ (by positivity) (by positivity [driftPrice_pos v]) (fun i=>stream_ana v _ (parallel i)) (fun _ i=>stream_cap v _ _ (parallel i)) hs M ht h q t parallel_top

lemma ink_total (R : PathData G) (h : R.Bounds p σ C Λ) (b : PlaqAxes) : Summable (fun i=> ‖ink R b i‖) :=
    (row_money h b).paid.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity [h.width])))
private lemma ink_spend (R : PathData G) (h : R.Bounds p σ C Λ) (b : PlaqAxes) (U : Config G N) (x : Site N) :
    Summable (fun i : Slot => ink R b i • i.atSite U x) := by
  apply (ink_total R h b).mul_right 2 |>.of_nonneg_of_le (fun _=>by positivity) _ |>.of_norm
  intro i; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (norm_nonneg _)

lemma row_total (U : Config G N) (x : Site N) b (R : PathData G) (h :R.Bounds p σ C Λ) : R.ell U (x,b)= ∑' i : Slot, ink R b i • i.atSite U x := by
  have hr := (raw_money h b).paid
  have hq := hr.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le ((raw_money h b).1 i))))
  obtain ⟨B,hB,hV⟩ := R.ell_dominated h (x,b)
  exact Eq.symm ((pool_read (fun i=>(R.row b i).1) (fun l : Slot=>l.atSite U x) (fun i=>(R.row b i).2) hq.of_norm (Summable.of_norm_bounded hB (fun i=>hV i U))).tsum_eq)

private lemma part_view (i : G.ColorIndex) (z : G.Color) : part (G:=G) i z=z i := rfl
lemma piece_total (U : Config G N) (x : Site N) b (R : PathData G) (h : R.Bounds p σ C Λ) (i : G.ColorIndex) :
    (R.ell U (x,b)) i = ∑' l : Slot, ink R b l * l.atSite U x i := by
  rw [← part_view (G:=G), row_total _ _ _ _ h,(part (G:=G) i).map_tsum (ink_spend R h b U x)]; simp_rw [map_smul,part_view]; rfl
lemma piece_spend (U : Config G N) (x : Site N) b (R : PathData G) (h : R.Bounds p σ C Λ) (i : G.ColorIndex) :
    Summable (fun l : Slot=> |ink R b l * l.atSite U x i|) := by
  refine Summable.of_nonneg_of_le (fun _=> abs_nonneg _) ?_ ((ink_total R h b).mul_right (‖part (G:=G) i‖ * 2))
  intro l
  rw [abs_mul]
  have hl : |l.atSite U x i| = ‖part i (l.atSite U x)‖ := by rw [part_view,Real.norm_eq_abs]
  rw [hl]
  exact mul_le_mul_of_nonneg_left ((part (G:=G) i).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (norm_nonneg _))) (abs_nonneg _)

lemma row_square (x : Site N) b (R : PathData G) (h : R.Bounds p σ C Λ) (t : ℝ) :
    ‖R.ell (represent (t • v)) (x,b)‖^2 = ∑ i : G.ColorIndex, ∑' j : Slot×Slot, (ash R b j)* stream v x (parallel (j,i)) t := by
  let U := represent (t•v)
  rw [←real_inner_self_eq_norm_sq]
  change inner ℝ (R.ell U (x,b)) _ = _
  rw [Work.F03.inner_color]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [piece_total U x b R h i]; unfold stream; simp_rw [Finset.prod_apply,Fin.prod_univ_two]
  let f (i) (l : Slot) := ink R b l * l.atSite U x i
  calc
    _ = ∑' (a:Slot×Slot), f i a.1 * f i a.2 := tsum_mul_tsum_of_summable_norm (piece_spend U x b R h i) (piece_spend U x b R h i)
    _ = _ := tsum_congr fun (a : Slot×Slot) => by change f _ a.1 * f _ a.2 = _; unfold f U ash parallel; simp only [Matrix.cons_val_zero,Matrix.cons_val_one]; unfold sprout; ring

set_option maxHeartbeats 200000 in
lemma row_word (x : Site N) b (R : PathData G) (h : R.Bounds p σ C Λ) (t : ℝ) :
    ‖R.ell (represent (t • v)) (x,b)‖^2 = words v x (note R b) t := by
  have hC : 0 ≤ C := (tsum_nonneg (h.rows b).1).trans (h.rows b).2.2
  rw [row_square v x b R h]; unfold words
  let f (j : Slot×Slot) (i : G.ColorIndex) := note R b (j,i) * stream v x (parallel (j,i)) t
  have hS : Summable (uncurry f) := words_sum v x 0 t (note_money h b hC) h.width
  change (∑ i:G.ColorIndex,∑' j,f j i)=_
  calc
     _ = ∑' i:G.ColorIndex,∑' j,f j i := Eq.symm <| tsum_fintype _
     _ = ∑' i,(uncurry f) i := hS.tsum_comm.trans hS.tsum_prod.symm
     _ = _ := tsum_congr fun _=>rfl
end YM.UVExt.Paths
