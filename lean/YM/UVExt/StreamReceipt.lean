import YM.UVExt.StreamPrice

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Real Wilson Precision Lattice Bid Exterior
open scoped BigOperators Classical Topology ContDiff

section envelope
variable {α : Type*} {h : α→ℝ→ℝ} (B P : ℝ) (L : α→ℝ) (hb : 0≤B) (hp : 0≤P) (ha : ∀ i, ContDiff ℝ ω (h i)) (hB : ∀ K : ℕ, cap K B P h L)
      {W : α→ℝ} {C σ : ℝ} (hs : 0 < σ) (hr : Carries C σ L W)
include hb hp ha hB hr hs
set_option maxHeartbeats 100000 in
lemma weigh_smooth : ContDiff ℝ ∞ (fun t=> ∑' i,W i*h i t) := by
  let V (i : α) := W i • h i
  let y (k : ℕ) i := B * P^k * allowance k σ * Real.exp (σ/2 * L i) * ‖W i‖
  have hL := hr.1
  have he i : ContDiff ℝ ω (V i) := ContDiff.const_smul (W i) (@ha i)
  have hs' i t k : iteratedDeriv k (V i) t = W i * iteratedDeriv k (h i) t := iteratedDeriv_const_smul ((ha i|>.of_le (by simp)).contDiffAt) _
  have hx': ∀ k,Summable (y k) := fun k=> (hr.summable_norm hs (B*P^k*allowance k σ) (fun i => show ‖y k i‖≤_ from by rw [Real.norm_of_nonneg (by unfold y; positivity [allowance_pos k hs.le])])).of_norm
  change ContDiff ℝ ∞ (fun t=>∑' i,V i t)
  refine contDiff_tsum (fun i=> (he i).of_le le_top) (fun k _=>hx' k) (fun k i t _ => ?_)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hs',norm_mul]
  unfold y
  rw [mul_comm _ ‖W i‖]
  apply mul_le_mul_of_nonneg_left ((hB k i t k le_rfl).trans _) (norm_nonneg _)
  rw [mul_pow, ←mul_assoc B _ (P^k),mul_right_comm B _ (P^k), mul_assoc (B * P^k) _ (rexp (σ/2*L i))]
  exact mul_le_mul_of_nonneg_left (polynomial_cap k σ (L i) hs (hL i)) (by positivity)

set_option maxHeartbeats 100000 in
private lemma weigh_hasSum e t : HasSum (fun i=> W i * iteratedDeriv e (h i) t) (iteratedDeriv e (fun t=>∑' i,W i*h i t) t) := (weigh_terms B P hr hs hb hp h e (hB e) ha t).2 -- inspect
variable {ι : Type*} (M : ι→α→ℝ) {F : Filter ι} [F.NeBot] (H : Tendsto M F (𝓝 W)) (H' : ∀ᶠ i in F,Carries C σ L (M i))
omit hr
include H H'
lemma eventually_carries : Carries C σ L W := by
  choose i hi using H'.exists
  classical
  let K j := if _h:Carries C σ L (M j) then M j else M i
  have hQ (j) : Carries C σ L (K j) := by by_cases h : Carries C σ L (M j) <;> simp [K,h,hi]
  have ht : M =ᶠ[F] K := H'.mono fun j hj => Eq.symm (dif_pos hj)
  exact Carries.limit hQ (fun x => tendsto_pi_nhds.mp (H.congr' ht) x)

set_option maxHeartbeats 150000 in
lemma weigh_pass (e : ℕ) (t : ℝ) (hL : Tendsto L cofinite atTop) :
   Tendsto (fun i=> iteratedDeriv e (fun t=>∑' j, M i j*h j t) t) F
           (𝓝 (iteratedDeriv e (fun t=>∑' j, W j*h j t) t)) := by
  choose i0 hf using H'.exists
  classical
  let K i := if _h:Carries C σ L (M i) then M i else M i0
  have hQ i : Carries C σ L (K i) := by by_cases h : Carries C σ L (M i) <;> simp_all [K]
  have hs2 := eventually_carries B P L hb hp ha hB hs M H H'
  let g (V : α→ℝ) j := V j*iteratedDeriv (𝕜:=ℝ) e (h j) t
  have hT {V : α→ℝ} (ht : Carries C σ L V) : HasSum (fun j=>g V j) (iteratedDeriv e (fun t=>∑' j, V j*h j t) t) := weigh_hasSum B P L hb hp ha hB hs ht e t
  rw [←(hT hs2).tsum_eq]
  suffices ht' : Tendsto (fun i=>∑' j,g (K i) j) F (𝓝 (∑' j,g W j)) by
    refine ht'.congr' ?_
    filter_upwards [H'] with i hi
    rw [show K i=M i from dif_pos hi]; exact (hT hi).tsum_eq
  apply sumConvergence (fun i=>(hT (hQ i)).summable) ((hT hs2).summable)
  · intro x; have ht : M =ᶠ[F] K := H'.mono fun j hj => Eq.symm (dif_pos hj)
    exact (tendsto_pi_nhds.mp (H.congr' ht) x).mul_const _
  intro ε he
  let A := B * P^e * allowance e σ
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hb (pow_nonneg hp _)) (allowance_pos _ hs.le)
  obtain ⟨S,hS⟩ := Carries.sunk (C:=C) ℝ hs A hA hL he
  refine ⟨S,fun u i hu=> (norm_sum_le ..).trans ((Finset.sum_le_sum fun j _=>?_ ).trans (hS _ (hQ i) u hu))⟩
  unfold g; rw [norm_mul,mul_assoc ‖K i j‖ A _]
  refine mul_le_mul_of_nonneg_left ((hB e _ _ _ le_rfl).trans ?_) (norm_nonneg _)
  have ht := polynomial_cap e σ (L j) hs ((hQ i).1 j)
  unfold A
  rw [mul_pow]
  convert mul_le_mul_of_nonneg_left ht (mul_nonneg hb (pow_nonneg hp e)) using 1 <;> ring
end envelope

variable {G : Gauge} {n : Side} (v : Dir G n) {k : ℕ}

def song (x : Site n) (T : Token G k→ℝ) (t : ℝ) := ∑' i,T i * stream v x i t
variable {C σ : ℝ} {T : Token G k→ℝ}
lemma song_sum (hr : Carries C σ breath T) (hs : 0 < σ) (x : Site n) (e t) : HasSum (fun j=>T j*iteratedDeriv e (stream v x j) t) (iteratedDeriv e (song v x T) t) :=
   weigh_hasSum (K G ^ k) (k * driftPrice v) breath (by positivity [K_pos G]) (by positivity [driftPrice_pos v]) (stream_ana v x) (stream_cap v · x) hs hr e t
lemma song_smooth (hr : Carries C σ breath T) (hs : 0 < σ) (x : Site n) : ContDiff ℝ ∞ (song v x T) :=
   weigh_smooth (K G ^ k) (k*driftPrice v) breath (by positivity [K_pos G]) (by positivity [driftPrice_pos v]) (stream_ana v x) (stream_cap v · x) hs hr

def levy v (K : ℕ) := 10 * allowance K σ * gain (6*curveBill G*‖dColor G n 1 v‖) (2*driftPrice v) K
lemma song_price (hk₀ : k=3 ∨ k=4) (hr : Carries C σ breath T) (hs : 0 < σ) (x : Site n) (q : ℕ) (he : q=3 ∨ q=4) :
    |iteratedDeriv q (song v x T) 0| ≤ levy (σ:=σ) v q * C := by
  have ht := weigh_bill q hr hs (stream v x) 10 (gain (6*curveBill G*‖dColor G n 1 v‖) (2*driftPrice v) q) (by norm_num) (gain_pos (by positivity [curveBill_pos G]) (by positivity [driftPrice_pos v])) 0 (fun i=>?check)
  -- replace
  on_goal 2 => cases hk₀ with
              | inl h3 => subst k; exact stream3 v x i he
              | inr h4 => subst k; exact stream4 v x i he
  unfold levy
  apply le_of_tendsto' (x:=atTop) ((song_sum v hr hs x q 0).norm) (ht)

variable {ι : Type*} {F : Filter ι} [F.NeBot]
lemma song_tends (M : ι → Token G k→ℝ) (h : ∀ᶠ i in F,Carries C σ breath (M i)) (ht : Tendsto M F (𝓝 T)) (hs : 0 < σ) x q t :
    Tendsto (fun i=> iteratedDeriv q (song v x (M i)) t) F (𝓝 (iteratedDeriv q (song v x T) t)) :=
  weigh_pass ((K G)^k) (k * driftPrice v) breath (by positivity [K_pos G]) (by positivity [driftPrice_pos v]) (stream_ana v x) (stream_cap v · x) hs M ht h q t (breath_top k)

set_option maxHeartbeats 700000 in
lemma neck_song {V : ℕ → RG.Atom G k} (h : SumBudget (fun i=> (V i).budget σ) C) (hs : 0 < σ) (x : Site n) t :
    song v x (necklace V) t = ∑' i, (V i).unmasked (represent (t • v)) x := by
  let W (i : ℕ × (Fin k→G.ColorIndex)) := (V i.1).coeff i.2
  let s (i : ℕ × (Fin k→G.ColorIndex)) : Token G k := ⟨(V i.1).leg, i.2⟩
  have hW : Carries C σ (fun i=> (V i.1).length) W := product_money (fun i=> ((V i).length:ℝ)) (fun _=>by positivity) (fun i => (V i).magnitude) (fun _=>rfl) h
  let fm (j : Token G k) := stream v x j t
  have hl (i : Token G k) : |fm i| ≤ K G ^ k := by simpa [cap,iteratedDeriv_zero, pow_zero, mul_one] using stream_cap v (k:=k) 0 x i t 0 le_rfl
  have hM : Summable (fun i=>(V i).magnitude) := Summable.of_nonneg_of_le (fun i=>Finset.sum_nonneg fun _ _=> abs_nonneg _) (fun i=>show _ from RG.Atom.lower_budget (a:=V i) σ hs) h.2.1
  have ha1 : Summable (‖W ·‖) := hW.paid.2.1.of_nonneg_of_le (fun _=> by positivity) (fun i=>le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity)))
  have ha : Summable (fun i=> W i*fm (s i)) := (ha1.mul_right (K G ^ k) |>.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>by rw [norm_mul]; gcongr; exact hl (s i))).of_norm
  have hS := pool_read W fm s ha1.of_norm (show _ from ha)
  have hf i : (∑ j : Fin k→G.ColorIndex, W (i,j)*fm (s (i,j))) = (V i).unmasked (represent (t • v)) x := Finset.sum_congr rfl fun j _ => by dsimp only [fm,s,W,stream]; rw [Finset.prod_apply]; rfl
  change ∑' i, pool W s i * fm i = _
  calc
     _ = ∑' (i:ℕ×(Fin k→G.ColorIndex)), W i*fm (s i) := hS.tsum_eq
     _ = ∑' (i:ℕ), ∑ j : Fin k→G.ColorIndex, W (i,j)*fm (s (i,j)) := by rw [show _ from ha.tsum_prod (γ:=Fin k→G.ColorIndex) (β:=ℕ)]; simp_rw [tsum_fintype]
     _ = _ := by simp_rw [hf]

end YM.UVExt.Paths
