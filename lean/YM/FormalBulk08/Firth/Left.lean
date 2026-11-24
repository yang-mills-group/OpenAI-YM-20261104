import YM.FormalBulk08.Firth.Turn
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Firth
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {P Q :Pot G}(a:hue G)
lemma shiftCost (x y: Cover)(T:Pot G): work x (work y T)=work (x+y) T:=by funext i j v; apply congr_arg (T i j); apply funext;intro i; apply Prod.ext; simp [Lotus.tint,add_comm,add_assoc]; rfl
lemma fewer (h:Ritual P l)(e:l≤ i): Ritual P i:= ⟨(fun x y hv=>le_trans (h.young x y hv) (Nat.add_le_add_right e _)),h.committees,h.health,(fun n=>by rw [show Kemp.banner i P n=Kemp.banner l P n from ?_]; exact h.esteem _; obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le e; ext1 j; exact (sail P _ h.young ..).symm)⟩
lemma virtualA (G:Gauge)(l:ℕ): Ritual (0:Pot G) l:= by
   refine ⟨fun i j (h:(0:Tile _ j)≠0)=> False.elim (h rfl),fun i j=> agate_zero _,fun x i j=>⟨1,0,one_pos,Knox_zeros _⟩,fun n=>?_⟩; rw [banner_zero]; intro _ _ _ _ _ _ _ _ _ _ _ _; rw [_root_.map_zero,_root_.map_zero]
lemma coins {T:Pot G}(h:Ritual T m)(c:ℝ): Ritual (c • T) m := by
   refine ⟨fun i j he=> h.young i j (fun hz=> by apply he;rw [Pi.smul_apply,Pi.smul_apply,hz,smul_zero]),fun i j=> (h.committees i j).smul c,fun x i j=>?_,fun n=>?_⟩
   · obtain ⟨s,C,hs,H⟩:=h.health x i j;exact ⟨_,_,hs,H.smul _⟩
   rw [banner_coin];intro I _ A B z e1 e2 e3 e4 e5 e6 e7; rw [_root_.map_mul,_root_.map_mul,h.esteem n I A B z e1 e2 e3 e4 e5 e6 e7,Wine.snow,Wine.snow]
lemma negatives (h:Ritual P m): Ritual (-P) m:= by simpa using coins h (-1)
include a
lemma auditMix (h:Ritual P l)(hp:Ritual Q l): Ritual (P+Q) l:= by rw [←neg_neg Q,←sub_eq_add_neg P (-Q)]; exact Sierra.summit _ a h (negatives hp)
lemma packageA (K:Finset I)(F:I→Pot G)(h:∀ i∈K,Ritual (F i) l): Ritual (∑ i∈K,F i) l:=by
    induction K using Finset.induction with
    | empty=>rw [Finset.sum_empty];exact virtualA ..
    | @insert a S he ih=> rw [Finset.sum_insert he]; exact auditMix ‹_› (h a (Finset.mem_insert_self _ _)) (ih fun i ht=> h i (Finset.mem_insert_of_mem ht)) -- duplicate a
variable (P : Flight j t)(S:Lodge P.patch){R Z W V:Pot G}{K:KernelChoices}{ρ:ChartRatio G}(h:P.patch.Branches K G)(hp:LocalRatio ρ)(ht:Story W (pink K.penalty P.wing))(he:4≤t)
-- U crank. linearity because we divide by the same denominator in each expression. rank-independent operation on eligible inputs. keep in local g here.
include hp ht he a
lemma plusT (hz:Ritual V l)(hk:Ritual Z l) : braise P S W (V+Z) ρ h l= braise P S W V ρ h l + braise P S W Z ρ h l := by
   let T n:= Classical.choice (chooseable n _ (primary P.patch K n)); let x:edgeL G:=(0,Exterior.coord 0,a)
   have hh(V:Pot G)(p:Ritual V l) e r : WavePath (chief P x x.2) (braise P S W V ρ h l e r) (fun n=> rancho (tossed P ρ h S n (T n) (Mesa.stone W _) (Kemp.banner l V _)) e r):= testified x P S W ρ h ht hp he p T e r
   have hs {T:Pot G}(hv:Ritual T l) i j: Summable (T i j):=by obtain ⟨s,c,hv,H⟩:=hv.health x i j; exact (penn_total H hv.le).of_norm
   funext i j
   apply (hh (V+Z) (auditMix a hz hk) i j).agree; have hw n:= banner_add l V Z (n*P.patch.L) (hs hz) (hs hk); simp_rw [hw,tossed_pp,show ∀ (n: Side)(X Y:Pap (wire G n)),rancho (X+Y) i j=rancho X i j+rancho Y i j from (fun n X Y=> by simp only [rancho,_root_.map_add,marble_add])]; exact (hh V hz i j).plus (hh Z hk i j)
lemma dime (hz:Ritual V l)(c:ℝ) : braise P S W (c • V) ρ h l=c • braise P S W V ρ h l:= by
   let T n:= Classical.choice (chooseable n _ (primary P.patch K n));let x:edgeL G:=(0,Exterior.coord 0,a)
   have hh(V:Pot G)(p:Ritual V l) e r : WavePath (chief P x x.2) (braise P S W V ρ h l e r) (fun n=>rancho (tossed P ρ h S n (T n) (Mesa.stone W _) (Kemp.banner l V _)) e r):= testified x P S W ρ h ht hp he p T e r
   have hw (n:Side): worm (wire G n) (PowerSeries.C c)=PowerSeries.C (MvPolynomial.C c):=PowerSeries.map_C ..
   funext i j; apply (hh _ (coins hz c) i j).agree; have hE(n):= hw (n*P.patch.L); simp_rw [banner_coin,←hE, tossed_cash,hw,show ∀ (n: Side)(X:Pap (wire G n)),rancho (PowerSeries.C (MvPolynomial.C c)*X) i j=c • rancho X i j from (fun n X=>by rw [rancho,coeff_C_mul,←MvPolynomial.smul_eq_C_mul,←canyon_eq,map_smul];rfl)]
   exact (hh _ hz i j).money _
lemma inhab (V:Pot G)(hV:Ritual V i)(hx:i≤r) : braise P S W V ρ h i= braise P S W V ρ h r := by
   let T n:= Classical.choice (chooseable n _ (primary P.patch K n));let x:edgeL G:=(0,Exterior.coord 0,a)
   have hh(i)(p:Ritual V i) e r : WavePath (chief P x x.2) (braise P S W V ρ h i e r) (fun n=>rancho (tossed P ρ h S n (T n) (Mesa.stone W _) (Kemp.banner i V _)) e r):= testified x P S W ρ h ht hp he p T e r
   have hx' (n:Side): Kemp.banner r V n=Kemp.banner i V n:=by obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hx; ext1 j; exact (sail V _ hV.young ..).symm
   funext p q; apply (hh i hV p q).agree; specialize hh r (fewer hV hx) p q; simp_rw [hx'] at hh;exact hh
lemma sizes (V:Pot G)(hV:Ritual V i)(hx:i≤r): enterStep P S W a ρ h r V=enterStep P S W a ρ h i V:= congr_arg _ (inhab a P S h hp ht he V hV hx).symm
lemma deposit (hz:Ritual V l)(c:ℝ): enterStep P S W a ρ h l (c • V)=c • enterStep P S W a ρ h l V:= by unfold enterStep; rw [dime a P S h hp ht he hz]; ext i j w; simp only [stamp,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> by ring
lemma vanish : enterStep P S W a ρ h l 0=0:=by simpa using deposit a P S h hp ht he (virtualA G l) 0
lemma assetMix (hv:Ritual V l)(hq:Ritual R l) : enterStep P S W a ρ h l (V+R) = enterStep P S W a ρ h l V+enterStep P S W a ρ h l R:= by unfold enterStep; rw [plusT a P S h hp ht he hv hq,road_add]
lemma assetWind (U:Finset I)(F:I→Pot G)(hv:∀ i∈U,Ritual (F i) l): enterStep P S W a ρ h l (∑ i∈U,F i)=∑ i∈U, enterStep P S W a ρ h l (F i):= by
   induction U using Finset.induction with
   | empty=>rw [Finset.sum_empty,Finset.sum_empty,vanish a P S h hp ht he]
   | @insert i A H ih=> rw [Finset.sum_insert H, Finset.sum_insert H]; have hG j hj:= hv j (Finset.mem_insert_of_mem hj); rw [assetMix a P S h hp ht he (hv i (Finset.mem_insert_self ..)) (packageA a _ F hG),ih hG]
end YM.FormalBulk08.Firth
