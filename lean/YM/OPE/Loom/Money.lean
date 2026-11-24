import YM.OPE.Sweep.Step
import YM.Work.I01
import YM.MergeProof.Stove
/-! # Set assembly costs for the thinner gate
Adapted from Corona and Work.I01. The second cover price is suitable
for using an OUTPUT root halo at the single final step before grouping,
sized by B* (const log beta) rather than B². -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Loom
open Lattice Filter Function Corona MergeProof Accent Marker
open scoped Topology BigOperators
variable {n : Side} {V : Type} [Fintype V] [DecidableEq V]
lemma assembled {B p : ℕ} (x y : Site n) (h : separation x y ≤ B*p) : coverNumber B ({x,y}:Support n) ≤ p+1:= by
  let f k:= Corona.line x y (B*k)
  let s := (Finset.range (p+1)).image f
  have he k (hk : k ≤ p) : f k∈s:= Finset.mem_image_of_mem f (Finset.mem_range.mpr (by omega))
  have hS : covers B ({x,y}:Support n) s:= by
    constructor
    · refine Finset.insert_subset (halo_subset B _ ?_) (Finset.singleton_subset_iff.mpr (halo_subset B _ ?_))
      · exact (show f 0=x by simp [f]) ▸ (he 0 (by omega))
      exact (show f p=y from line_end x y h) ▸ (he _ le_rfl)
    apply ship_halo
    have hp (k) (hk:k ≤ p) : Relation.ReflTransGen (Touch s (B+B+1)) (f 0) (f k) := by
      apply Corona.line_path _ _ (fun i hi=> he i (hi.trans hk))
      intro i hi; have hh := line_dist x y (B*i) (B*(i+1)) (by gcongr; omega); apply hh.trans; rw [Nat.mul_add]; omega
    intro i hi j hj; obtain ⟨k,hk,rfl⟩:= Finset.mem_image.mp hi; obtain ⟨l,hl,rfl⟩:= Finset.mem_image.mp hj
    exact (Corona.sym (hp k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))|>.trans (hp l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)))
  exact (list_cost B hS).trans (Finset.card_image_le.trans (show (Finset.range _).card ≤ _ from (Finset.card_range _).le))

lemma packing (V : Type) [Fintype V] [DecidableEq V] (f : V→ Site n) (b p : ℕ) (hb : 0 < b) (hp : 0 < p) (F:Finset V)
    (hs:∀ i ∈ F,∀ j∈F,i≠j → b*(p+2) ≤ separation (f i) (f j)) (hc:2≤ F.card)(H:Support n)(hv:F.image f⊆H):
    p* F.card ≤ 12*coverNumber b H:= by
  classical
  obtain ⟨D,hD,hp'⟩:= coverNumber_realized b H; obtain ⟨N,hN,R,hstep,hv'⟩:= ring_path _ (halo_ship b hD.2)
  have ht (i) (hi:i∈F) : ∃ k, k ≤ N ∧ separation (R k) (f i) ≤ b:= by
    obtain ⟨x,hx,hL⟩:= halo_spec.mp (hD.1 (hv (Finset.mem_image_of_mem f hi)))
    obtain ⟨k,hk,he⟩:= hv' _ hx
    exact ⟨k,hk,he.symm ▸ hL⟩
  choose! t ht hnear using ht
  let g:=b*p; have hg:0<g:= Nat.mul_pos hb hp
  have hA (i : V) (hi : i ∈ F) (j : V) (hj : j ∈ F) (hne : i ≠ j) (h : t i ≤ t j) : t i + g ≤ t j := by
    have hv:= path_span hstep _ _ h (ht j hj)
    have h1:= separation_triangle (f i) (R (t i)) (f j)
    have h2 := separation_triangle (R (t i)) (R (t j)) (f j)
    rw [separation_comm (f i) (R (t i))] at h1
    have H := hs i hi j hj hne; rw [Nat.mul_add] at H; have := hnear i hi; have := hnear j hj; omega
  let w (i : V):= t i / g; have ladder (i : V) (hi : i∈F) (j : V) (hj : j∈F) (hne:i≠j) (hl:t i ≤ t j) : w i < w j := by
     have h:=Nat.div_le_div_right (c:=g) (hA i hi j hj hne hl); rw [Nat.add_div_right _ hg] at h; exact h
  have hv' : F.card ≤ N/g +1 := by
    rw [← Finset.card_range (N/g+1)] -- maybe
    apply Finset.card_le_card_of_injOn w
    · exact fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (c:=g) (ht i hi)))
    intro i hi j hj hq; by_contra hne; obtain h|h:= le_total (t i) (t j)
    · exact (ladder i hi j hj hne h).ne hq
    exact (ladder j hj i hi (Ne.symm hne) h).ne hq.symm
  have ha:= (show (F.card-1)*g ≤ N from (Nat.le_div_iff_mul_le hg).mp (by omega))
  have hz : N ≤ D.card*(6*b):= hN.trans (Nat.mul_le_mul_left _ (by omega)); rw [←hp']; apply Nat.le_of_mul_le_mul_left (c:=b) ?_ hb
  calc
     _ = F.card*g:=by unfold g; ring
     _ ≤ (2*(F.card-1))*g:= by gcongr; omega
     _ ≤ 2*(D.card*(6*b)) := by rw [mul_assoc]; exact Nat.mul_le_mul_left 2 (ha.trans hz)
     _ = _ := by ring

lemma buys {K:Census V}{B p : ℕ}{o:V→Site n}(hh:∀ s:K.Mode,2 ≤ s.val.card→∀ i∈s.val,∀ j∈s.val,i≠j→ B*(p+2) ≤ separation (o i) (o j)) (hB : 0 < B) (hp : 0 < p)
    {u v: V→ℝ} (hu:∀ i,0<u i)(hv:∀ i,0<v i)(ht:∀ i,u i≤v i*Real.exp ((p:ℝ)/24)) : Repegs o B v u (1/2) 1 K:=by
   intro i hi X hS; have ht' := packing V o B p hB hp i.val (hh i hi) hi X hS
   rw [one_mul]; unfold Poly.toll; refine (Finset.prod_le_prod (fun i _=>hu i|>.le) (fun i _=>ht i)).trans ?_
   rw [Finset.prod_mul_distrib,Finset.prod_const]; apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _=> hv i|>.le); rw [← Real.exp_nat_mul]; apply Real.exp_monotone;
   have h:(p:ℝ)*i.val.card ≤ 12*coverNumber B X:= by exact_mod_cast ht'; -- newline
   linarith only [h]
end YM.OPE.Loom
