import YM.OPE.Compatible.Lake.Cash
/-! Block matrix primer, distinguish cell topology from component. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter Lattice Wilson ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
abbrev Dock {d:ℕ}(E: Fin (d+1)→Type):= ∀ i,E i
abbrev Train {d:ℕ} (E: Fin (d+1)→Type) [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]:= Dock E→L[ℂ] Dock E
-- matrix. primitives
local notation "I"=> Fin (d+1)
def route (R: Train E)(i j:I) : E j →L[ℂ] E i:= ((ContinuousLinearMap.proj i).comp R).comp (ContinuousLinearMap.single ℂ E j)
def track (p:Dock E→L[ℂ]ℂ)(i:I): E i→L[ℂ]ℂ:= p.comp (ContinuousLinearMap.single ℂ E i)
def team (R: Train E):Prop:= ∀ i j:I,i<j→ route R i j=0
lemma freightCarve (v:Dock E): (∑ i:I, (ContinuousLinearMap.single ℂ E i (v i)))=v:=by ext i; simp --
lemma routed (R:Train E)(v:Dock E)(i:I): R v i = ∑ j:I, route R i j (v j):=by
   nth_rw 1 [← freightCarve v]; rw [_root_.map_sum, Finset.sum_apply]; rfl
lemma tracking (p:Dock E→L[ℂ]ℂ)(v:Dock E): p v=∑ i:I,track p i (v i):=by
   nth_rw 1 [← freightCarve v]; rw [_root_.map_sum]; rfl
lemma routes (p q:Train E)(i j:I): route (p.comp q) i j=∑ k:I,(route p i k).comp (route q k j):=by
   ext1 x; rw [sum_apply]; exact routed p _ _
lemma tracks (u:Dock E→L[ℂ]ℂ)(p:Train E)(j:I): track (u.comp p) j=∑ k:I,(track u k).comp (route p k j):=by ext1 x; rw [sum_apply]; exact tracking u _
lemma tolls (R:Train E)(i j:I): ‖route R i j‖ ≤ ‖R‖:=by
   unfold route; apply (opNorm_comp_le ..).trans; calc
      _ ≤ (‖ContinuousLinearMap.proj (R:=ℂ) (φ:=E) i‖ * ‖R‖)*1:= mul_le_mul (opNorm_comp_le ..) (norm_single_le_one ..) (norm_nonneg _) (by positivity)
      _ ≤ 1*‖R‖:=by rw [mul_one]; exact mul_le_mul_of_nonneg_right (opNorm_le_bound (ContinuousLinearMap.proj (R:=ℂ) (φ:=E) i) zero_le_one fun v=> by rw [one_mul]; exact norm_le_pi_norm v _) (norm_nonneg _)
      _ = _:= one_mul _
lemma tally (p:Dock E→L[ℂ]ℂ)(i:I): ‖track p i‖ ≤ ‖p‖:= (opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_single_le_one ..))
lemma teamTracks (R:Dock E≃L[ℂ]Dock E) (p q : Train E) (he:p=R.toContinuousLinearMap) (hh:q=R.symm.toContinuousLinearMap)
   (hp:team p) (hq:team q) (i:I): (route p i i).comp (route q i i) = ContinuousLinearMap.id ..:=by
   have hs: p.comp q= ContinuousLinearMap.id .. := by subst p q; ext1; simp
   have ht:= routes p q i i; rw [Finset.sum_eq_single i,hs] at ht
   · rw [← ht]; ext1; simp [route]
   · intro j _ hj; rcases lt_or_gt_of_ne hj with h|h
     · rw [hq _ _ h]; simp
     rw [hp _ _ h]; simp
   intro hi; exact (hi (Finset.mem_univ _)).elim
lemma tollDiff (p q:Train E)(i j:I): route (p-q) i j=route p i j-route q i j:=by ext1;rfl
-- l1
abbrev berth (v:Dock E):= ∑ i:I,‖v i‖
abbrev income (p:Dock E→L[ℂ]ℂ):= ∑ i:I,‖track p i‖
lemma board (v:Dock E): ‖v‖ ≤ berth v := by nth_rw 1 [← freightCarve v]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; apply ((ContinuousLinearMap.single ℂ E i).le_opNorm (v i)).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_single_le_one ..))
omit [∀ i,NormedSpace ℂ (E i)] in
lemma boardTicket (v:Dock E): berth v≤ (d+1:ℕ)*‖v‖:=by apply (Finset.sum_le_sum (g:=fun _=> ‖v‖) (fun i _=> norm_le_pi_norm v i)).trans_eq; simp
lemma boardRow (p:Dock E→L[ℂ]ℂ): ‖p‖ ≤ income p:=p.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x=> by
   rw [tracking]; apply (norm_sum_le ..).trans; unfold income; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; apply ((track p i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _))
lemma boardRowTicket (p:Dock E→L[ℂ]ℂ): income p ≤ (d+1:ℕ)*‖p‖:=by apply (Finset.sum_le_sum (g:=fun _=> ‖p‖) (fun i _=> tally p i)).trans_eq; simp
end YM.OPE.Lake
