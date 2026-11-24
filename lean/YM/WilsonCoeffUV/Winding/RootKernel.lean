import YM.WilsonCoeffUV.Winding.Earnings
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type*}{i j k r:ℕ}{s a A B t q :ℝ}

variable [NormedAddCommGroup V][NormedSpace ℝ V]
-- match dilution API

def pruce {r:ℕ}(P:Ten V (Co n α) r): Ten V (Co n α) r:= if r=0 then (Fintype.card (Site n):ℝ)⁻¹ • P else P
lemma diluted (P:raw α V r)(n:Side): pruce (P n)= dilute P n:=rfl
lemma pruce_down (P:Ten V (Co n α) (r+1)): pruce P=P:=if_neg (by omega)
lemma pruce_plus (P Q:Ten V (Co n α) r): pruce (P+Q)=pruce P+pruce Q:=by unfold pruce; split; exact smul_add ..; rfl
lemma pruce_mu (P:Ten V (Co n α) r)(c:ℝ): pruce (c•P)= c•pruce P:=by unfold pruce; split; exact smul_comm ..; rfl
lemma pruce_none : pruce (0:Ten V (Co n α) r)=0:=by unfold pruce; split; exact smul_zero _; rfl

variable {P Q:Ten V (Co n α) r}{F Z: Ten V (Cloth α) r}
structure Sight (P:Ten V (Co n α) r)(F:Ten V (Cloth α) r)(s A:ℝ):Prop where
   aim : Amber (tor n) s A (pruce P)
   bound : Amber Bank.terrain s A F
   gall : Wound (pruce P) F n (slideC n) (soar Bank.terrain) s A
   strollT : stroll P

lemma Sight.add (h:Sight P F s A)(p:Sight Q Z s B): Sight (P+Q) (F+Z) s (A+B):= ⟨pruce_plus P Q ▸ h.aim.add p.aim,h.bound.add p.bound,pruce_plus P Q ▸ h.gall.add p.gall,fun x i=> by simp only [Pi.add_apply,h.strollT x,p.strollT x]⟩
lemma Sight.μ (h:Sight P F s A)(a:ℝ): Sight (a•P) (a•F) s (‖a‖*A):= ⟨pruce_mu P a ▸ h.aim.smul a,h.bound.smul a,pruce_mu P a ▸ h.gall.μ a,fun x i=>by simp only [Pi.smul_apply,h.strollT x]⟩
lemma Sight.zero : Sight (0: Ten V (Co n α) r) 0 s 0:=⟨by rw [pruce_none]; exact Amber.zero, Amber.zero,by rw [pruce_none]; exact Wound.zero,fun _ _=>rfl⟩
lemma Sight.mono (p:Sight P F s A)(he:t≤s): Sight P F t A:=⟨p.aim.mono he,p.bound.mono he,p.gall.mono he,p.strollT⟩
lemma Sight.more (p:Sight P F s A)(he:A≤B): Sight P F s B:=⟨p.aim.le he,p.bound.le he,p.gall.more he,p.strollT⟩
lemma Sight.neg (h:Sight P F s A): Sight (-P) (-F) s A:= by simpa using h.μ (-1)
lemma Sight.sub (h:Sight P F s A)(p:Sight Q Z s B): Sight (P-Q) (F-Z) s (A+B):= by simp only [sub_eq_add_neg]; exact h.add p.neg
lemma Sight.sum {P:ι→Ten V (Co n α) r}{F:ι→Ten V (Cloth α) r}{A:ι→ℝ}(S:Finset ι)(h:∀ i∈S,Sight (P i) (F i) s (A i)): Sight (∑ i∈ S,P i) (∑ i∈ S,F i) s (∑ i∈ S,A i):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Sight.zero
   | @insert i S hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))

variable {C:canal (Site n) α β V (k+1) r}{D:canal Cover α β V (k+1) r}
omit [NormedSpace ℝ V] in
structure SiteW (C:canal (Site n) α β V (k+1) r)(D:canal Cover α β V (k+1) r)(s A:ℝ): Prop where
    aim : pairCup (tor n) s A C
    bound : pairCup Bank.terrain s A D
    fall : Wound (uncurry C) (uncurry D) n (Prod.map (slideC n) (slideC n)) (uncurry (course Bank.terrain)) s A
    port : mooring C
lemma spliceHit (s:ℝ) (v u:ℕ)(h:v≤2*u)(p:0≤s): catchW s u≤catchW (s/2) v:=by
    unfold catchW; have he:(v:ℝ)≤ 2*u:= by exact_mod_cast h
    apply Real.exp_monotone; nlinarith [mul_le_mul_of_nonneg_left he p]
lemma radiusSmall (d:Bank.Distance U)[Fintype ι]{x:ι→U}{p:U}(h:∃ i,p=x i)(j:ι): d.gap p (x j)≤league d x:= by obtain ⟨i,h⟩:=h; rw [h]; exact leg_le ..
lemma pruce_amber [Fintype α] (h:pairCup (tor n) s A C)(p:mooring C)(v:t<s)(u:0≤t): Amber (tor n) t (A*tiePay α (k+1) (s-t)) (pruce (wear C)):=by
    -- dependent n inset
    classical
    let F: (c:Side)→canal (Site c) α β V (k+1) r:=fun c=> if t:n=c then t ▸ C else 0
    have ht:F n=C:=dif_pos rfl
    rw [← ht]; exact wear_amber (F:=F) (ht ▸ h) (ht ▸ p) u v
lemma pruce_wears [Fintype α] (p:mooring C)(x): pruce (wear C) x=∑ y,tie C x y:=by
    classical
    let F: (c:Side)→canal (Site c) α β V (k+1) r:=fun c=> if t:n=c then t ▸ C else 0
    have ht:F n=C:=dif_pos rfl
    rw [← ht]; exact dilute_wear (F:=F) (ht ▸ p) _
omit [NormedSpace ℝ V] in
lemma SiteW.cross (h:SiteW C D s A)(x:dock Cover β r)(u:dock Cover α (k+1))(g:unfoldAt (bearing x) (slideC n u)=u)(v:4*course Bank.terrain x u<n.val): ‖tie C (slideC n x) (slideC n u)-tie D x u‖ ≤ A*catchW s n:=by
   cases r with
   | succ r=> simp only [Nat.succ_ne_zero,tie,false_and,↓reduceIte]; exact h.fall.local_w (x,u) v
   | zero=>
        have hx : (slideC n u 0).1=0 ↔ (u 0).1=0:=by
            refine ⟨fun t=>?_,fun i=>?_⟩
            · have hp:=congr_arg Prod.fst (congr_fun g 0)
              change _+lift (_-wrap n _)= _ at hp; rw [show bearing x=0 from rfl,t] at hp; simpa using hp.symm
            change wrap n (u 0).1=_; rw [i,map_zero]
        by_cases p:(u 0).1=0
        · simp only [tie,hx,p, ne_eq, not_true, and_false,↓reduceIte]; exact h.fall.local_w (x,u) v
        simp only [tie,hx,p,ne_eq, not_false_eq_true,true_and,↓reduceIte,sub_self,norm_zero]; exact mul_nonneg h.bound.1 (catch_hot ..)
open Classical in
omit [NormedSpace ℝ V] in
lemma SiteW.prices (h:SiteW C D s A)(p:0≤s)(x:dock Cover β r)(hp:4*soar Bank.terrain x<n.val)(y:dock Cover α (k+1)) :
   let T:=if unfoldAt (bearing x) (slideC n y)=y then tie C (slideC n x) (slideC n y) else 0
   T - tie D x y ≠ 0 →
    (∀ i, Bank.terrain.gap (bearing x) (y i).1≤ course Bank.terrain x y)∧ (4*course Bank.terrain x y<n.val→ ‖T-tie D x y‖ ≤ A*catchW s n) ∧
    ‖T-tie D x y‖ ≤ (A+A)*catchW (s/2) (course Bank.terrain x y):=by
    classical
    intro T w
    set v:= course Bank.terrain x y
    let W:=slideC n x; let Y:=slideC n y
    have hu : ¬ (r=0 ∧ (y 0).1≠0):= by
        intro u; apply w; rw [tie,if_pos u]; unfold T; split; swap; · simp
        rename_i g; rw [tie,if_pos]; · simp
        refine ⟨u.1, fun p=>u.2 ?_⟩; have he:bearing x=0:=by rcases u with ⟨e,b⟩; subst r; rfl
        have hx:=congr_arg Prod.fst (congr_fun g 0); change _+lift (_-wrap n _)= _ at hx; rw [he,p] at hx; simpa using hx.symm
    refine ⟨pole_cut hu,fun he=> ?_,?_⟩
    · have hb: unfoldAt (bearing x) (slideC n y)=y:= unfoldReady (n:=n) (p:=bearing x) (fun i=> by have hZ := pole_cut (d:=Bank.terrain) (x:=x) (y:=y) hu i; change 4*v<n.val at he; unfold v at he; omega)
      unfold T; rw [if_pos hb]; exact h.cross x y hb he
    have he := h.bound.2 x y; change ‖D x y‖≤A*catchW s v at he
    have hv: ‖tie D x y‖ ≤ A*catchW (s/2) v:=by rw [tie,if_neg hu]; exact he.trans (mul_le_mul_of_nonneg_left (catch_width (by linarith) _) h.bound.1)
    refine (norm_sub_le T _).trans ((add_le_add ?_ hv).trans_eq (add_mul ..).symm)
    unfold T; split; swap; · rw [norm_zero]; exact mul_nonneg h.bound.1 (catch_hot ..)
    rename_i b; rw [tie]; split; · rw [norm_zero]; exact mul_nonneg h.bound.1 (catch_hot ..)
    rename_i g
    refine (h.aim.2 ..).trans (mul_le_mul_of_nonneg_left (spliceHit s v (course (tor n) W Y) ?_ p) h.bound.1)
    apply league_cash _ (a:=bearing x); intro i; cases i with
    | inr i=>
        have hx:= near_change (bearing x) Y i
        rw [show unfoldAt (bearing x) Y=y from b] at hx; rw [base_change x] at hx
        exact hx.le.trans (pole_cut g i)
    | inl i=>
        have he (i:Fin r) : ∀ (x:dock Cover β r),∃ z:Fin r,bearing x=(x z).1:=fun x=>?_
        swap
        · cases r
          · exact (Fin.elim0 (i:Fin 0))
          exact ⟨0,rfl⟩
        obtain ⟨z,hz⟩:= he i x
        let U:=Prod.fst ∘ W; let F:=Prod.fst ∘ x
        have hh:Bank.terrain.gap (bearing x) (F i) ≤ soar Bank.terrain x:= by rw [hz]; exact leg_le Bank.terrain F z i
        change Bank.terrain.gap (bearing x) (F i)≤_
        rw [exactGap (show 4*Bank.terrain.gap (bearing x) (F i)<n.val from by omega),hz]; exact (show _ ≤ soar (tor n) W from leg_le (tor n) U z i).trans (shelves (tor n) W Y)

variable [CompleteSpace V][Fintype α]
def priceM (α:Type*)[Fintype α](k:ℕ)(s:ℝ):= tiePay α k (s-s/32)+2*boardPay α (Winding.tailC k (s/4))^k
lemma SiteW.worthy (h:SiteW C D s A)(p:0<s): Sight (wear C) (worn D) (s/32) (priceM α (k+1) s*A):=by
    classical
    let u:= tiePay α (k+1) (s-s/32); let z:= (boardPay α (Winding.tailC (k+1) (s/4)))^(k+1)
    have hx:0≤u:= pow_nonneg (boardPay_nn (div_pos (by linarith) (by positivity))) _
    have hv:0 ≤ z:= pow_nonneg (boardPay_nn (tail_good _ (by positivity))) _
    have hp:0≤s/32:=by positivity
    have he:s/32<s:=by linarith
    have hA:= h.bound.1; have hz:0≤A:=hA
    have hh : A*u≤ priceM α (k+1) s*A:=by unfold priceM; change _≤ (u+2*z)*A; nlinarith
    refine ⟨(pruce_amber h.aim h.port he hp).le hh,(worn_amber h.bound hp he).le hh, ⟨(by exact (mul_nonneg hA hx).trans hh),fun x v=>?_⟩,north_stroll h.port⟩
    rw [pruce_wears h.port,worn]; refine (broker (k:=k+1) (bearing x) (tie D x) (tie C (slideC n x)) (course Bank.terrain x) p hA ((tie_cost h.bound he hp x).2.1.of_norm) (h.prices p.le x v)).trans (mul_le_mul_of_nonneg_right ?_ (catch_hot ..))
    unfold priceM; change _≤ (u+2*z)*A; change (A+A)*z≤ _; nlinarith
end YM.WilsonCoeffUV.Winding
