import YM.WilsonCoeffUV.Vacuum.Gain.ChangeToPred
/-!
# Pre length rent. Leading repeated rank arrays keep Width. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power MultiNext.SignedSource
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β V :Type*}{s t t' σ A B C D E:ℝ}{L:Side}

lemma epoch (_i: Fin (r+1))(p:Grazing α (r+1))(x:Cover): soar terrain p ≤ ∑ j, terrain.gap x (p j).1 := by
   apply league_le; intro i k; by_cases hh:i=k
   · subst k; rw [terrain.self]; positivity
   set f:=fun i:Fin (r+1)=> terrain.gap x (p i).1
   apply le_trans (terrain.tri (p i).1 x (p k).1)
   rw [terrain.swap (p i).1 x]; change f i+f k≤∑ j,f j
   apply le_trans _ (Finset.sum_le_sum_of_subset (f:=f) (Finset.subset_univ {i,k})); simp [hh]

def postpaid (s:ℝ)(x:Cover)(y:Grazing α r): ℝ:= ∏ i, Real.exp (-s*terrain.gap x (y i).1)
lemma ticket_spare (i:Fin (r+1))(hp:0≤σ)(hs:σ<s)(y:Grazing β (r+1))(p:Cover): postpaid s p y≤Real.exp (-σ*soar terrain y)*Real.exp (-(s-σ)*terrain.gap (y i).1 p):=by
   unfold postpaid; rw [←Real.exp_sum,←Real.exp_add,← Finset.mul_sum,← Nat.cast_sum]; apply Real.exp_monotone
   set K := ∑ j,terrain.gap p (y j).1
   have h : (soar terrain y:ℝ)≤K:=by exact_mod_cast epoch i y p
   have he : (terrain.gap (y i).1 p:ℝ)≤K:=by rw [terrain.swap (y i).1 p]; exact_mod_cast (Finset.single_le_sum (f:=fun j=>terrain.gap p (y j).1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
   linarith only [mul_le_mul_of_nonneg_left h hp, mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hs.le)]
lemma accountStamp [Fintype α] (i: Fin (r+1))(hp:0≤σ)(hs:σ<s)(x:Grazing β (r+1))(L:Side): SumBudget (fun p: Cloth α=> postpaid s (parentC L p.1) x) (Real.exp (-σ*soar terrain x)*boardPay (Co L α) (s-σ)):= by
   let Q := panel L α
   have hv : SumBudget (fun q:Cloth α=> Real.exp (-(s-σ)*terrain.gap (x i).1 (parentC L q.1))) (boardPay (Co L α) (s-σ)):= by
     apply cap_walk _ _ Q _ (keys_cost (x i).1 (sub_pos.mpr hs)); intro p; rw [parent_pack]; rfl
   exact budget_minor (cap_scale hv (Real.exp_pos _).le) (fun p=>sail_nn ..) (fun p=>ticket_spare i hp hs x _)

def nestTake (L:Side)(R:ropes Cover (Co L α) β)(q i: Fin r)(m:ℕ): Roof α β r:= fun p x=> Newt.tail m (fun y=> spring L R ((p q).1+y,(p i).2) x) ((p i).1-(p q).1)
lemma nest_base (q i: Fin r)(M:ropes Cover (Co L α) β): nestTake L M q i 0=owns L M i:= by ext p x; simp [nestTake,Newt.tail,Newt.take, owns]
lemma nest_take (q i:Fin (r+1))(M:ropes Cover (Co L α) β): nestTake L M q i 1=dropL L M q i:= by ext p x; simp [nestTake,Newt.tail,Newt.take, Newt.piece,dropL,owns,echoL]
lemma notch {k d:ℕ}{M:ropes Cover (Co L α) β}(h:Crank M d s B)(hk:k≤d)(v:0<s)(q i: Fin r)(p:Grazing α r)(x:Cloth β):
  |nestTake L M q i k p x| ≤ B*Real.exp (8*s)/(L.val:ℝ)^(1+k)*Real.exp (-s*terrain.gap (parentC L (p q).1) x.1)*Real.exp ((s/L.val)*soar terrain p)*tollD k p := by
   have he : (terrain.gap (p q).1 (p i).1: ℝ) ≤ soar terrain p:= by exact_mod_cast leg_le terrain (Prod.fst ∘ p) q i
   change (size ((p i).1-(p q).1):ℝ) ≤ _ at he
   apply ((h.mono hk le_rfl).tag v (p q).1 ((p i).1-(p q).1) (p i).2 x).trans
   unfold tollD; have hs:=h.1; gcongr

lemma perDuty (L:Side)(_n:ℕ)(r:ℕ) (p: Grazing α (r+1))(s:ℝ)(x:Grazing β (r+1))(B:ℝ)(k:Fin (r+1)→ℕ)(q:Fin (r+1)) : let y:= (p q).1
   (∏ i, (B*Real.exp (8*s)/(L.val:ℝ)^(1+k i)*Real.exp (-s*terrain.gap (parentC L y) (x i).1)*Real.exp ((s/L.val)*soar terrain p)* tollD (k i) p)) =
      (B*Real.exp (8*s))^(r+1)/(L.val:ℝ)^(r+1+∑ i,k i)*postpaid s (parentC L y) x * Real.exp (((r+1:ℕ):ℝ)*s/L.val*soar terrain p)* tollD (∑ i,k i) p:=by
    intro y; simp_rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,Fintype.card_fin,tollD,Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_add_distrib, show ∑ _ : Fin (r+1),(1:ℕ)=r+1 by simp, ← Real.exp_nat_mul]; unfold postpaid; congr 3; ring

section
variable [Fintype α][NormedAddCommGroup V][NormedSpace ℝ V]

def preB (α:Type*) [Fintype α](r j:ℕ)(t t' s σ B:ℝ): ℝ:= (B*Real.exp (8*s))^(r+1) * ceilPoly j ((t-t')/2)* tiePay α r ((t-t')/2) * boardPay α (s-σ)
lemma preB_nn (hp:t'<t)(h:0≤B)(he:σ<s)(r j:ℕ) : 0 ≤ preB α r j t t' s σ B:=by
    have hv:0<(t-t')/2:= by linarith
    have hb : 0≤ tiePay α r ((t-t')/2) := by
      cases r with
      | zero=> simp only [tiePay, pow_zero]; positivity
      | succ r=> exact pow_nonneg (boardPay_nn (by positivity)) _
    unfold preB; have hw:=ceilPoly_pos j ((t-t')/2); apply mul_nonneg (by positivity) (boardPay_nn (sub_pos.mpr he))

-- any graph with designated tails at each output, incl arbitrary rank counts. absolute Sumbudget.
lemma precision_bill {M:ropes Cover (Co L α) β}{P:Ten V (Cloth α) (r+1)}(p:Fin (r+1))(w:Fin (r+1)→ℕ){d:ℕ}(h:∀ i,w i≤d)(he:Crank M d s B)(g:Amber terrain t C P)(hq:0≤ σ)(hp:σ<s)(hv:t'< t)(hy:((r+1:ℕ):ℝ)*s/L.val ≤ t')(x:Grazing β (r+1)):
   let T:=fun i=>nestTake L M p i (w i)
   let m:=∑ i,w i
   SumBudget (fun y:Grazing α (r+1)=>‖spinJob P T x y‖) ((C*preB α r m t t' s σ B)*(L.val:ℝ)^4/(L.val:ℝ)^(r+1+m)*Real.exp (-σ*soar terrain x)):=by
    intro T m
    let Z:= ((B*Real.exp (8*s))^(r+1)/(L.val:ℝ)^(r+1+m)); let F:=fun b: Cloth α=> postpaid s (parentC L b.1) x
    let H (u:Cloth α)(y:Grazing α r):= let l:= soar terrain (Fin.cons u y);
                                         ((1+l:ℝ)^m*Real.exp (t'*l))*‖P (enlist p u y)‖
    have hs:=lt_of_le_of_lt hq hp
    have ht u (y:Grazing α r): soar terrain (Fin.cons u y)= soar terrain (enlist p u y):=by unfold enlist soar; rw [← Function.comp_assoc, league_equiv]
    have Hb (u): SumBudget (H u) (C*ceilPoly m ((t-t')/2)*tiePay α r ((t-t')/2)):= by
       -- cent requires reordered P not Pure
       let P':=fun v:Grazing α (r+1)=>P (v ∘ reverseK p)
       have hx : Amber terrain t C P' := ⟨g.1,fun x=> (g.2 _).trans_eq (by unfold soar; rw [← Function.comp_assoc, league_equiv])⟩
       exact cent_amber hx hv u m
    let J:= (Equiv.prodComm ..).trans (visitJ (Cloth α) p)
    let W:=Real.exp (-σ*soar terrain x)
    let M₀:= boardPay (Co L α) (s-σ)
    have hy':0≤C*ceilPoly m ((t-t')/2)*tiePay α r ((t-t')/2):= by
       have hG:=g.1; have hm:=ceilPoly_pos m ((t-t')/2)
       apply mul_nonneg (by positivity)
       have hk:0<(t-t')/2:=by linarith
       -- pop need rank r dependent
       by_cases he:r=0; · simp only [he,tiePay,pow_zero]; positivity
       exact pow_nonneg (boardPay_nn (div_pos hk (by positivity : 0<(r:ℝ)))) _
    have hB:= he.1; have hZ:0≤Z:=by unfold Z; positivity
    have HB := prod_cap (cap_scale (accountStamp p hq hp x L (α:=α)) hZ) hy' Hb
    have hg (b:Cloth α)(y:Grazing α r): ‖spinJob P T x (enlist p b y)‖ ≤ (Z*F b)*H b y:=by
       let j:=enlist p b y; let l:= soar terrain j
       have hj: j p=b:=enlist_it ..; have hv := ht b y
       rw [spinJob,norm_smul, Real.norm_eq_abs, Finset.abs_prod]
       have he: (∏ i, |T i j (x i)|) ≤ Z*F b* Real.exp (t'*l)* tollD m j:= by
          apply le_trans (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> notch he (h i) hs p i j (x i)))
          rw [perDuty L 0 r _ _ _ _ _ p]
          rw [hj]
          change Z*F _* _* _ ≤ _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hy (by positivity))) (mul_nonneg hZ (sail_nn ..))) (toll_pos j _).le
       apply (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq; unfold H; rw [hv]; unfold tollD l j; ring
    have hd : (↑(Fintype.card (Site L)):ℝ)=(L.val:ℝ)^4:= by exact_mod_cast site_card L
    have HX : Z*(Real.exp (-σ*soar terrain x)*boardPay (Co L α) (s-σ)) * (C * ceilPoly m ((t-t')/2)*tiePay α r ((t-t')/2))= (C*preB α r m t t' s σ B)*(L.val:ℝ)^4/(L.val:ℝ)^(r+1+m)*Real.exp (-σ*soar terrain x):= by
       unfold Z preB boardPay; rw [Fintype.card_prod, Nat.cast_mul,hd]; ring
    rw [← HX]
    exact cap_walk _ _ J (fun _=>rfl) (budget_minor HB (fun a:Cloth α× Grazing α r=>show 0≤ ‖spinJob P T x (enlist p a.1 a.2)‖ from norm_nonneg _) (fun a=> hg a.1 a.2))

lemma clockOut [CompleteSpace V]{M:ropes Cover (Co L α) β}{P:Ten V (Cloth α) (r+1)}(p: Fin (r+1))(w:Fin (r+1)→ℕ){d:ℕ}(h:∀ i,w i≤d)(he:Crank M d s B)(g:Amber terrain t C P)(hq:0≤σ)(hp:σ<s)(hv:t'< t)(hy:((r+1:ℕ):ℝ)*s/L.val≤ t')(ha:4<r+1+∑ i,w i):
    let T:=fun i=>nestTake L M p i (w i); (∀ x,Summable (spinJob P T x)) ∧ Amber terrain σ ((preB α r (∑ i,w i) t t' s σ B)*C/L.val) (pump P T):=by
    intro T
    have HH x:= precision_bill p w h he g hq hp hv hy x
    let P':= pump P T
    set S:= preB α r (∑ i,w i) t t' s σ B; have hS:=preB_nn (α:=α) hv he.1 hp r (∑ i,w i)
    have hB:= he.1; have hA:=g.1
    refine ⟨fun x=>(HH x).2.1.of_norm,div_nonneg (mul_nonneg hS hA) (by positivity),fun x=>(norm_tsum_le_tsum_norm (HH x).2.1).trans ((HH x).2.2.trans ?_)⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    obtain ⟨a,ha'⟩:= Nat.exists_eq_add_of_le ha
    change C*S*_/_ ≤ _; set x:= (L.val:ℝ); have hx:1≤x:= by unfold x; exact_mod_cast L.property
    have hv:0<x:= by linarith
    rw [ha',pow_add, pow_succ x 4, show (x^4*x)*x^a= x^4*(x*x^a) by ring, div_le_iff₀ (by positivity)]
    calc
      _ = (S*C/x)*(x^4*(x*1)):= by field_simp
      _ ≤ _:= by gcongr; exact one_le_pow₀ hx
end
end YM.WilsonCoeffUV.Bank
