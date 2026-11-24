import YM.OPE.Compatible.Eyrie.Sand
/-! # Pricing unnormalized data. finite volume estimates exact for any s, β. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid
open PathData SectorNext.Vacuum Extra.Histories MergeProof MergeProof.Accent Finset
open scoped Topology Classical BigOperators
variable {G:Gauge}{n:Side}{l k:ℕ}{P:BudgetPoint}{C:Clip}{R:Rep G n} (U:Config G n) {c v b σ d r δ w:ℝ}{X:PathData G} (h:X.Bounds C σ c v)
include h
lemma elves (x:Face (Per n)) : ‖X.ell U x‖≤c*2:=by
      have hh:= h.rows x.2; have hp:= X.ell_dominated h x|>.absolute U; let K i:= |(X.row x.2 i).1| * Real.exp (σ*(X.row x.2 i).2.length); have ha: Summable K:=hh.2.1
      apply (norm_tsum_le_tsum_norm hp).trans; refine (hp.tsum_le_tsum (g:=fun i=> K i*2) (fun i=> ?_) (ha.mul_right 2)).trans (le_trans (le_of_eq (tsum_mul_right)) (mul_le_mul_of_nonneg_right hh.2.2 (by norm_num)))
      rw [ellTerms,norm_smul,Real.norm_eq_abs]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg _)))) (Slot.eval_norm ..) (norm_nonneg _) (hh.1 _)
omit h
lemma peak (P:BudgetPoint) : ∃ p:Face (Per n)→ℝ, ∀ x: Face (Per n),∀ X:PathData G,X.Bounds C σ c v→∀ U:Config G n, ‖X.baseTerm C P U x‖≤p x:=by
      choose z hz using fun x:Face (Per n)=> (clip_env (G:=G) (c:=C) P x).cost; refine ⟨fun x=> z x+(c*2)^2/2,fun x X h U=>?_⟩; unfold PathData.baseTerm; apply (norm_add_le ..).trans; apply add_le_add (hz x U)
      split; rename_i hb; swap;· rw[norm_zero]; positivity
      have hp:=elves U h x; rw [Real.norm_of_nonneg (by positivity)]; gcongr
lemma oar (x:Site n) (a:ℕ→Atom G l) (hs:0<σ)(hh:SumBudget (fun i=> (a i).budget σ) c)(p:BudgetPoint): ‖atomSeries a p U x‖ ≤ c*2^l:=by
      have hp:= atom_dominated a p x hs hh|>.absolute U; apply (norm_tsum_le_tsum_norm hp).trans; let f i:=(a i).budget σ; apply le_trans (hp.tsum_le_tsum (g:=fun i=> f i*2^l) (fun i=> by rw [Real.norm_eq_abs]; exact ((a i).placed_bound ..).trans (mul_le_mul_of_nonneg_right ((a i).lower_budget σ hs) (by positivity))) (hh.2.1.mul_right _)); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hh.2.2 (by positivity)
lemma faces (p:BudgetPoint)(b:ℝ):∃ t:ℝ, ∀ X:PathData G,X.Bounds C σ c v→∀ a:ℝ, ‖a‖ ≤ b→∀ U:Config G n, ‖X.principal C p a U‖≤t:=by
       obtain ⟨z,hz⟩:= peak (c:=c) (C:=C) (v:=v) (σ:=σ) (G:=G) (n:=n) p; let B:= Fintype.card (Site n); refine ⟨b*((∑ i,z i)+ B*(c*2^3+c*2^4))+B*(v*2^2),fun X h a ht U=>?_⟩; refine (norm_add_le ..).trans ?_; apply add_le_add
       · rw[norm_mul]; apply mul_le_mul ht _ (norm_nonneg _) ((norm_nonneg _).trans ht); refine (norm_add_le ..).trans (add_le_add ((norm_sum_le ..).trans (sum_le_sum (fun i _=>hz i X h U))) ?_); apply (norm_sum_le ..).trans; refine le_trans (sum_le_sum (g:=fun _=> c*2^3+c*2^4) ?_) (by simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_rfl)
         intro i _; exact (norm_add_le ..).trans (add_le_add (oar U i _ h.width h.three p) (oar U i _ h.width h.four p))
       apply (norm_sum_le ..).trans; simpa only [sum_const,card_univ,nsmul_eq_mul] using (sum_le_sum (s:=Finset.univ) fun i _=>oar U i _ h.width h.two p)
lemma labor (p:BudgetPoint)(b:ℝ):∃ t:ℝ,∀ X:PathData G,X.Bounds C σ c v→∀ a:ℝ, ‖a‖ ≤ b→∀ U:Config G n, ‖X.inChannels C p a U‖ ≤ t:=by
       obtain ⟨t,h⟩:=faces (c:=c) (C:=C) (v:=v) (σ:=σ) (G:=G) (n:=n) p b; refine ⟨‖((↑(Fintype.card Signed):ℝ)⁻¹)‖*((↑(Fintype.card Signed):ℝ)*t),fun X hX a hA U=>?_⟩; unfold PathData.inChannels; rw [norm_mul]; have ht:= norm_nonneg ((↑(Fintype.card Signed):ℝ)⁻¹); let f:=X.principal C p a (n:=n); have hx: ‖∑ s:Signed,f (pull s 0 U)‖≤↑(Fintype.card Signed)*t:= (norm_sum_le ..).trans ((sum_le_sum (fun i _=>h X hX a hA (pull i 0 U))).trans (by rw[sum_const,card_univ,nsmul_eq_mul])); exact mul_le_mul_of_nonneg_left hx ht
lemma Blinds (h:R.activities.EBound R.p δ) (U:Config G n):‖R.activities.additive R.p U‖≤↑(Fintype.card (Site n))*δ:=by -- n implicit R
       let P:=R.p; let A:= R.activities; obtain ⟨z,hz,H⟩:=h; let V(i:Site n)(j):= if (A.reg j).site=i then P.mass (A.reg j).support (z j) else 0
       have h(i):Summable (V i):=(H i).2.1; have hz'(i):z i≤∑ x:Site n,V x i:=by unfold V; rw [sum_ite_eq,if_pos (mem_univ _)]; exact P.loMass _ _ (hz i).1
       have hS: Summable (fun i=>∑ x:Site n,V x i):=summable_sum (fun i _=> h i); have hσ:Summable z:=hS.of_nonneg_of_le (fun i=>(hz i).1) hz'
       let Y(i:ℕ):=A.regularOccurrence P i U; have hx(i): ‖Y i‖≤z i:=by unfold Y Activities.regularOccurrence; by_cases hi:Healthy P.threshold (A.reg i).support U; rw[masked_eq _ _ _ _ hi]; exact (hz i).2 U hi [] (by simp) (by simp); rw[masked_ne _ _ _ _ hi,norm_zero]; exact (hz i).1
       have hr : Summable (fun i=> ‖Y i‖):= hσ.of_nonneg_of_le (fun i=>norm_nonneg _) hx; apply (norm_tsum_le_tsum_norm hr).trans; apply le_trans ((hr.tsum_le_tsum hx hσ).trans (hσ.tsum_le_tsum hz' hS)); rw [Summable.tsum_finsetSum ?_]
       exact (sum_le_sum (fun i _=> (H i).2.2)).trans (by rw[sum_const,card_univ,nsmul_eq_mul]); exact fun i _=> h i
end YM.OPE.Eyrie
