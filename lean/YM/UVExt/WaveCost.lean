import YM.UVExt.FaceSong

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Real Wilson Precision Lattice Bid Exterior
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {N : Side} {C σ : ℝ} (v : Dir G N)

-- first endpoint is new root; no shortening of the relative paths in these evaluation identities.
abbrev Chord (G : Gauge) := (Slot×Slot)×G.ColorIndex

def shell (e : Bool) (f : Chord G) : Token G 2 := ⟨![ground f.1.1,if e then relay f.1.1 f.1.2 else alignSecond f.1.1 f.1.2],fun _=>f.2⟩

def breath' (A B : Slot) := (A.length:ℝ) + (B.length:ℝ)
lemma parallel_breath (i : Chord G) : breath (parallel i) = breath' i.1.1 i.1.2 := by simp [parallel,breath',breath,Fin.sum_univ_two]
lemma shell_breath (i : Chord G) (e) : breath (shell e i) ≤ 2*breath (parallel i) := by
  rw [parallel_breath]; unfold breath'; simp only [shell,breath,Fin.sum_univ_two, Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_add] -- replace
  have hg := align_status i.1.1 i.1.2
  have h : (ground i.1.1).length ≤ i.1.1.length+i.1.2.length := by exact le_trans (Nat.le_add_left 4 i.1.1.walk.length) (Nat.le_add_right i.1.1.length _)
  cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
    exact_mod_cast (by omega)

def Weighted (C σ : ℝ) (R : Chord G → ℝ) := Carries C σ (breath ∘ parallel) R
def liftAir (e : Bool) (x : Site N) (R : Chord G→ℝ) (t : ℝ) := ∑' i,R i*stream v x (shell e i) t
variable {W : Chord G →ℝ} (e : Bool) (x : Site N) (hr : Weighted C σ W) (hs : 0 < σ)
lemma shell_flow (k : ℕ) : cap k ((K G)^2) (4*driftPrice v) (fun i => stream v x (shell e i)) (breath ∘ parallel) := by
  intro i t j he
  let P := parallel i
  have hL : 0≤breath P := breath_pos _
  have : 0≤driftPrice v := driftPrice_pos v
  change _ ≤ K G^2 * ((1+breath P)*_)^j
  exact le_trans (stream_cap v (k:=2) k x _ t j he) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity [breath_pos (shell e i)]) (by linear_combination (2*driftPrice v) * (shell_breath i e) + 2 * this) _) (sq_nonneg _))
include hr hs
lemma air_sum t k : Summable (fun i=> W i*iteratedDeriv k (stream v x (shell e i)) t) ∧
    HasSum (fun i=> W i*iteratedDeriv k (stream v x (shell e i)) t) (iteratedDeriv k (liftAir v e x W) t) := by
  have hv := weigh_terms ((K G)^2) (4*driftPrice v) hr hs (by positivity) (by positivity [driftPrice_pos v]) _ k (shell_flow v e x k) (fun i=>stream_ana v x (shell e i)) t
  exact ⟨hv.1 k le_rfl |>.of_norm,hv.2⟩
lemma air_smooth : ContDiff ℝ ∞ (liftAir v e x W) := weigh_smooth ((K G)^2) (4*driftPrice v) _ (sq_nonneg _) (by positivity [driftPrice_pos v]) (fun i => stream_ana v x _) (shell_flow v _ _) hs hr
omit hr
lemma air_pass {ι : Type*} {F : Filter ι} [F.NeBot] (X : ι→Chord G→ℝ) (hg : ∀ᶠ j in F, Weighted C σ (X j)) (ht : Tendsto X F (𝓝 W)) (t : ℝ) (k : ℕ) :
    Tendsto (fun i=> iteratedDeriv k (liftAir v e x (X i)) t) F (𝓝 (iteratedDeriv k (liftAir v e x W) t)) :=
  weigh_pass ((K G)^2) (4*driftPrice v) _ (sq_nonneg _) (by positivity [driftPrice_pos v]) (fun i=>stream_ana v x _) (shell_flow v e x) hs X ht hg _ _ parallel_top
omit hs
lemma shell_true (i : Chord G) : stream v x (shell true i) = afterPair v x (parallel i) := by rw [stream,Fin.prod_univ_two]; rfl
lemma shell_false (i : Chord G) : stream v x (shell false i) = axisPair v x (parallel i) := by rw [stream,Fin.prod_univ_two]; rfl

include hr hs
-- difference at a fixed `x` only between conjugated second-path terms, evaluated after shifting both fields
lemma air_price {k} (hk : k=3 ∨ k=4) :
    |tag k (liftAir v true x W) - tag k (liftAir v false x W)| ≤ (3:ℝ)^k *levy (σ:=σ) v k * C := by
  let r e := fun i=>stream v x (shell e i)
  have h (e : Bool) i : ContDiff ℝ ω (r e i) := stream_ana _ _ _
  have hv := ((air_sum v true x hr hs 0 k).2.sub (air_sum v false x hr hs 0 k).2).norm
  let D := 6*curveBill G*‖dColor G N 1 v‖; let Y := 2*driftPrice v
  have hZ : 0≤gain D Y k := gain_pos (by unfold D; positivity [curveBill_pos G]) (by unfold Y; positivity [driftPrice_pos v])
  have ht : (3:ℝ)^k*levy (σ:=σ) v k*C=(10*3^k)*allowance k σ*gain D Y k * C := by unfold levy; ring
  refine le_of_tendsto' (b:=(3:ℝ)^k*levy _ _ *_) (hv) ?_
  intro s; rw [ht]
  change |∑ i∈s,(W i*tag k _ - W i*tag k _)| ≤ _
  simp_rw [←mul_sub]
  convert weigh_bill k hr hs (fun i=>(r true i-r false i)) (10*(3:ℝ)^k) (gain D Y k) (by positivity) hZ 0 ?_ s using 1
  · congr 1; congr 1
    exact funext fun i=> by unfold tag; congr 1; exact ((iteratedDeriv_sub (n:=k) (x:=(0:ℝ)) ((h true i).contDiffAt.of_le (by simp)) ((h false i).contDiffAt.of_le (by simp))).symm)
/- unfold tag; congr! <;> simp_rw [show (fun i => r true i - r false i) = r true - r false by rfl, Pi.sub_apply] -- replace -/
  intro i; change |tag k (r true i - r false i)| ≤ _; unfold r; rw [shell_true,shell_false]; exact dispersion v x (parallel i) hk

omit hr hs in
lemma air_given (i : Slot×Slot) :
    ∑ _p : G.ColorIndex, stream v x (parallel (i,_p)) = ∑ b : G.ColorIndex, stream v (stop x i.1.walk) (shell true (i,b)) := by
  funext t; simp_rw [stream,Finset.sum_apply,Finset.prod_apply,Fin.prod_univ_two]
  change (∑ j : G.ColorIndex, i.1.atSite _ x j * i.2.atSite _ x j) = ∑ j : G.ColorIndex, (ground i.1).atSite _ _ j * (relay i.1 i.2).atSite _ _ j
  simp only [←Work.F03.inner_color]; exact sub_at ..

set_option maxHeartbeats 700000 in
omit hr in
lemma words_trans {T : Slot×Slot→ℝ} (hr : Weighted C σ (fun i : Chord G=> T i.1)) :
    ∑ x' : Site N, words v x' (fun i=> T i.1) = ∑ x, liftAir v true x (fun i=> T i.1) := by
  funext t
  let p (e : Bool) (x : Site N) (i : Chord G) := T i.1 * stream v x ((if e then shell true else parallel) i) t
  have hS e x' : Summable (p e x') := by
    cases e
    · exact words_sum v x' (W:=(fun i=> T i.1)) 0 t hr hs
    exact (air_sum v true x' hr hs t 0).1
  have hh e x' : (∑' j, p e x' j)=∑' i : Slot×Slot,∑ b:G.ColorIndex, p e x' (i,b) := by
    rw [(hS _ _).tsum_prod]; simp_rw [tsum_fintype]
  have hl e x' : Summable (fun i=>∑ b:G.ColorIndex, p e x' (i,b)) := by simpa only [tsum_fintype] using (hS e x').prod
  have hd (x' : Site N) (i : Slot×Slot) : (∑ b:G.ColorIndex,p false x' (i,b)) = ∑ b:G.ColorIndex,p true (x'+wrap N i.1.offset) (i,b) := by
    unfold p; norm_num; simp_rw [←Finset.mul_sum]; refine congr_arg (T i * ·) ?_; unfold Slot.offset; rw [← attach_back x' i.1.walk]
    simpa only [Finset.sum_apply] using congr_fun (air_given v x' (G:=G) i) t
  rw [Finset.sum_apply,Finset.sum_apply]
  change ∑ _x, (∑' j,p false _x j)=∑ _x,∑' j,p true _x j
  simp_rw [hh]; rw [← Summable.tsum_finsetSum (fun x' _=> hl false x'),← Summable.tsum_finsetSum (fun x' _=> hl true x')]
  simp_rw [hd]; refine tsum_congr fun i=> (Equiv.sum_comp (Equiv.addRight _) (fun x' =>∑ b : G.ColorIndex,p true x' (i,b)))

end YM.UVExt.Paths
