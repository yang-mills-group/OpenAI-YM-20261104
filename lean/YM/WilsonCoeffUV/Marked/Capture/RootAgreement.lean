import YM.WilsonCoeffUV.Marked.Capture.Profile
/-!
# Capture footprint equality

Fixed physical placements that pass and live are included; earlier
connected curves may hit forbidden sites after capture labels aggregate, so
claim equality only on evaluated profile input and when rolling jointly.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{o:ι}{c:Side}{i j i' j' a e r h N n m b b' l:ℕ}{G:Gauge}{σ τ u g B C x y z ρ:ℝ}{E W V' U':Credit}

section prod
variable [DecidableEq ι]
-- M from top-only-single log (unnormal multiplicative)
lemma firstExp {R:Type}[CommRing R][IsAddTorsionFree R]{p q: Sac ι R}(x:Equation p q)(h:∀ S, S.card≠1→ q S=0) : p=fun S=>∏ i∈S,q {i}:=by
   apply Equation.prod_u _ q _ x; refine ⟨?_,x.2.1,?_⟩
   · exact Finset.prod_empty
   funext S; unfold dial shells
   classical
   let t:Finset (Finset ι):= S.image fun i=>{i}; let f (J: Finset ι): R:= J.card • q J*∏ i∈S\J,q {i}
   have hp:t⊆S.powerset:=by intro i hi; obtain ⟨j,h,rfl⟩:= Finset.mem_image.mp hi; simp [h]
   change S.card • (∏ j∈S, q {j})=∑ J∈ S.powerset,f J
   rw [← Finset.sum_subset hp, show t=S.image fun i=>{i} from rfl,Finset.sum_image (by intros j u' k v H; exact Finset.singleton_inj.mp H)]
   · rw [← Finset.sum_const]; apply Finset.sum_congr rfl; intro i hi; unfold f; rw [Finset.card_singleton,one_smul, Finset.sdiff_singleton_eq_erase]; exact Eq.symm (Finset.mul_prod_erase S (fun i=>q {i}) hi)
   intro i hi hu; have ht:q i=0:=h i (fun hv=>hu (by obtain ⟨k,rfl⟩:=Finset.card_eq_one.mp hv; simpa [t] using hi)); unfold f; rw [ht,smul_zero,zero_mul]
end prod

section Eval
variable [DecidableEq ι][Fintype ι]
abbrev AuthSum (F:Outerm G D): Outerm G D:=fun p=>levelsO (F p)
lemma estimateEq (A:Levels G)(L:ChartRatio G)(p:G.Simple)(q:LocalRatio L)(v:i<N)(z:CellR)(m:ℕ)(F:Garland D)(X:Outerm G D)(h:Wellness k X):
   let y' n:= paceT A.S m n; let Q:= stout A L i N k k X
   verseI A L i N (fullK k) (Finale (y' (i+1)) y z F k (AuthSum X))= Finale (y' i) y z F k (AuthSum Q):=by
   intro Y R; let u:= Y (i+1); let P:= ll A i; let V t:=edV A L i N (X t) k; let f t:= scrollR u y z F (AuthSum X) t; let Q:= boxes u y F
   have hp:X=X:=rfl
   have he : verseI A L i N (fullK k) (Finale u y z F k (AuthSum X))=Finale u y z F k V:=by
       unfold Finale; rw [verse_sum (P:=f) A p v q (d:=fun _=> lyric u k)]; swap
       · exact fun i _=> Auth.tuft (placedO _ (h.level' i) _) _
       apply Finset.sum_congr rfl; intro t _; unfold f scrollR; rw [← ply_verse A v p q (placedO _ (h.level' _) _)]; rfl
   rw [he,gauge_reveal P V F u y z (pace_pos ..) k, show u*P.L.val=Y i from pace_step ..]; apply congr_arg _; funext i; exact oneStep_log A L X p q v h k i
-- common coupling normalized production on all closed windows
lemma portsEq (A:Levels G)(L:ChartRatio G)(p:G.Simple)(q:LocalRatio L)(u:i≤b)(v:b≤ N)(z:CellR)(m:ℕ)(X: Outerm G D)(F:Garland D)(h:Wellness k X):
    Finale (paceT A.S m i) y z F k (AuthSum (Gears A L k k N b i X))=cruises A L N (fullK k) b i (Finale (paceT A.S m b) y z F k (AuthSum X)):=by
    induction u using Nat.decreasingInduction with
    | self=> rw [gearTop,cruises_top]
    | of_succ i he ih=> rw [gearUp _ _ _ he, cruises_sub A L N (fullK k) _ he,← ih]; exact (estimateEq A L p q (he.trans_le v) z m F (Gears A L k k N b (i+1) X) (Cog A L v X h p q he)).symm

omit [DecidableEq ι] in
lemma separation (m:ℕ)(z:CellR)(S: Schedule)(F:Garland D)(x:ι→Cover)(v:∀ i j,i≠j→ClearDay (F i) (F j) (ρ+14))(u:∀ i, lyra 1 y z F x i≠0): cleared S m m ρ x Finset.univ:=by
   intro i _ j _ H; rw [nearR]; dsimp only [id]; let p:=x i; let q:=x j; obtain ⟨a,ha⟩:=featureV (F i) _ _ _ _ (u i); obtain ⟨b,hb⟩:=featureV (F j) _ _ _ _ (u j)
   have ht:= v i j H _ ha _ hb
   have hv: dist (address 1 y z (x i) (a.val)) (address 1 y z (x j) b.val)≤ Bank.terrain.gap (x i) (x j)+2:=by
        unfold address Mer.position; simp only [one_smul]; apply (dist_add_add_le ..).trans; rw [dist_sub_right]; refine add_le_add (actual_dis ..) ((dist_triangle (a.val) 0 b.val).trans ?_); rw [dist_zero_right,dist_zero_left]; linarith only [c_norm a,c_norm b]
   linarith
-- reopening consumes evaluated profile only. all J alternatives recover by taking subarrays.
lemma vicinity (A:Levels G)(X:Outerm G D)(m:ℕ)(q:CellR)(F:Garland D)(h:∀ i j,i≠j→ ClearDay (F i) (F j) (ρ+14)):
    Finale (paceT A.S m m) y q F k (AuthSum (reserveGood A.S m m ρ X)) = Finale (paceT A.S m m) y q F k (AuthSum X):=by
    rw [pace_self]; apply Finset.sum_congr rfl; intro i hi; unfold scrollR AuthSum; by_cases he: ∀ j,lyra 1 y q F i j≠0; · rw [reserveEligible A.S m m ρ X i (separation m q A.S F i h he)]
    simp only [not_forall, ne_eq, not_not] at he; obtain ⟨j,b⟩:=he; rw [testW _ (Finset.mem_univ j) b,testW _ (Finset.mem_univ j) b]
lemma reopening (A:Levels G)(L:ChartRatio G)(F: Garland D)(X:Outerm G D)(m b N:ℕ)(h:Wellness k X)(p:G.Simple)(q:LocalRatio L)(v:b≤m)(t:m≤N)(z:CellR)(x: ∀ i j,i≠j→ ClearDay (F i) (F j) (ρ+14)):
     let Y:= reserveGood A.S m m ρ (Gears A L k k N N m X);
     Finale (paceT A.S m b) y z F k (AuthSum (Gears A L k k N m b Y)) = cruises A L N (fullK k) N b (Finale (paceT A.S m N) y z F k (AuthSum X)):=by
    intro Y; rw [portsEq A L p q v t z m Y F (reserveSpec _ _ _ _ (Cog A L le_rfl X h p q t))]; unfold Y; rw [vicinity A _ m z F x, portsEq A L p q t le_rfl z m X F h, cruisesMore _ _ _ v t]
end Eval
end YM.WilsonCoeffUV.Wheel.Flooring
