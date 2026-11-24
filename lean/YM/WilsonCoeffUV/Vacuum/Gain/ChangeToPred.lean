import YM.WilsonCoeffUV.Vacuum.Gain.Internal
/-!
# Change inherited rows. Charge ALL such changes on wind bill, not packet.
Includes removing lower-order pure-polynomials on nonanchored legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β V :Type*}{s t t' σ A B C D E:ℝ}{L:Side}

lemma flag_credit {Z: ReaderT L G}(h:dragCup terrain s D Z)(i:Fin (r+1)):
    let U: Talus G (Hooks G) r:= fun _ x j=>spring L Z (well x j); sells L s D (Tolled 0 (apex i U)) := by
    intro U; refine ⟨h.1,fun p x=> ⟨i,?_⟩⟩; unfold Tolled; rw [show tollD 0 p=1 from pow_zero _, div_one]; exact spring_pt h _ _
lemma wind_credit {Z:ReaderT L G}{M Q:ropes Cover (Co L (Hooks G)) (Hooks G)}(h:verdant M Q Z)(i:Fin (r+1)):
    let U: Talus G (Hooks G) r:= fun _ x j=>spring L Z (well x j); owns L Q i-owns L M i=reedG i U:=by
    intro U; funext p x; simp only [reedG,apex,U,Pi.sub_apply,owns]
    obtain ⟨⟨y,b⟩,v,ht⟩:=every_stone (p i)
    rw [← ht,show axisEquiv.symm (stone (y,b) v).2.1=b by simp [stone,← coord_map]]; exact h y b v x

variable [NormedAddCommGroup V][NormedSpace ℝ V]
variable [CompleteSpace V]
private lemma neighbor {r:ℕ}{i:Fin (r+1)}{Z : Roof (Hooks G) (Hooks G) (r+1)}{R:Fin (r+1)→ Roof (Hooks G) (Hooks G) (r+1)}{T: Ten V (YForest G) (r+1)}(k:ℕ)(U:Talus G (Hooks G) r)(h:sells L s D Z)(g:∀ j,sells L s D (R j))(hs:0<s)(htv:0≤ σ)(he:σ<s)(hy:t'< t)(hp:s/L.val≤t')(hζ:Z-R i=reedG i U) (hZ:sells L s E (Tolled k (apex i U)))(ha:∀ j,j≠i→dormant i (R j)) (hm:Smooth T)(hh:Amber terrain t A T)(hv:Draft T t B) :
     Amber terrain σ ((max (D+D) E ^(r+1)*(B*ceilPoly k (t-t')*Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-σ)) (pump T (Function.update R i Z) - pump T R) := by
   rw [spin_sub hh (hp.trans hy.le) hs g h]; apply sling i U _ _ _ hm hh hv k hZ hy hp htv he
   · rw [Function.update_self,hζ]
   · intro j; by_cases b:j=i
     · subst j; rw [Function.update_self]; exact h.sub (g i) hs.le
     rw [Function.update_of_ne b]; exact (g j).cost (le_add_of_nonneg_right h.1)
   intro j hw; rw [Function.update_of_ne hw]; exact ha _ hw

theorem mixWind {r:ℕ}{M Q:ropes Cover (Larvae G L) (Hooks G)}{Z:ReaderT L G}(hh:dragCup terrain s C M)(hk:dragCup terrain s C Q)(h:verdant M Q Z)(e:dragCup terrain s D Z){T: Ten V (YForest G) (r+1)}(hx:Smooth T)(he: Amber terrain t A T)(hg:Draft T t B)(hp:s/L.val≤t')(hs:0≤σ)(hb:σ<s)(hv:t'<t):
    Amber terrain σ ((r+1:ℕ)*((max (C+C) D ^(r+1)*(B*ceilPoly 0 (t-t')*Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-σ))) (pump T (owns L Q)-pump T (owns L M)) := by
   let R i (j : Fin (r+1)):= if j.val< i then owns L Q j else owns L M j
   set S:=max (C+C) D ^ (r+1) *(B*ceilPoly 0 (t-t')*Real.exp (8*s))*tiePay (Co L (Hooks G)) (r+1) (s-σ)
   have hu : ∀ i≤r+1,Amber terrain σ (i*S) (pump T (R i)-pump T (owns L M)) := by
     intro i; induction i with
     | zero=> intro _; rw [show R 0=owns L M from funext fun _=> if_neg (Nat.not_lt_zero _),sub_self, Nat.cast_zero, zero_mul]; exact Amber.zero
     | succ i ih=>
       intro hi
       let v:Fin (r+1):=⟨i,by omega⟩
       have hO:R (i+1)=Function.update (R i) v (owns L Q v):=by
         ext1 b; by_cases H:b=v
         · subst b; rw [Function.update_self]; exact if_pos (Nat.lt_succ_self i)
         have he: b.val≠ i:= fun h=>H (Fin.ext h)
         rw [Function.update_of_ne H]; simp only [R,show b.val< i+1 ↔ b.val< i by omega]
       have ha (b): sells L s C (R i b):= by
          unfold R
          split
          · exact ownS hk b
          exact ownS hh b
       let U:Talus G (Hooks G) r:= fun _ x j=>spring L Z (well x j)
       have hh : owns L Q v-R i v=reedG v U := by rw [show R i v=owns L M v from if_neg (lt_irrefl i)]; exact wind_credit h v
       have H : Amber terrain σ S (pump T (R (i+1))- pump T (R i)):=by
         rw [hO]; apply neighbor 0 U (ownS hk _) ha (lt_of_le_of_lt hs hb) hs hb hv hp hh (flag_credit e v) _ hx he hg
         intro j hg p a b; simp only [R]; split<;> (ext x; unfold owns; rw [remote hg p a b])
       rw [show pump T (R (i+1))-pump T (owns L M)= (pump T (R (i+1))-pump T (R i))+(pump T (R i)-pump T (owns L M)) by abel,Nat.cast_succ,add_mul,one_mul,add_comm ((i:ℝ)*_)]
       exact H.add (ih (by omega))
   specialize hu (r+1) le_rfl; rw [show R (r+1)=owns L Q from funext fun i=> if_pos i.isLt] at hu; exact hu

-- nonanchored positions costs
section peg
variable {T: Ten V (YForest G) (r+1)}
def echoL (L:Side)(M:ropes Cover (Co L α) β)(q i: Fin (r+1)): Roof α β (r+1) := fun p=>spring L M ((p q).1,(p i).2)
def dropL (L:Side)(M:ropes Cover (Co L α) β)(q i:Fin (r+1)): Roof α β (r+1) := owns L M i - echoL L M q i
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma echo_fee {M:ropes Cover (Co L α) β}(h:dragCup terrain s C M)(q i:Fin (r+1)): sells L s C (echoL L M q i) := ⟨h.1,fun _ _=>⟨q,spring_pt h _ _⟩⟩
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma drop_fee {M:ropes Cover (Co L α) β}(h:dragCup terrain s C M)(e:0≤s)(q i: Fin (r+1)): sells L s (C+C) (dropL L M q i):= (ownS h _).sub (echo_fee h q i) e
-- Talus of difference between pivot term and raw term (negative sign)
def projectU (L:Side)(M:ropes Cover (Co L (Hooks G)) (Hooks G))(q i:Fin (r+1)) : Talus G (Hooks G) r:= fun p x a b=>
    let y:= (enlist i (waive x 0 a) p q).1;
    -(∑ v:Axis, spring L M (waive y v a) b * chalk v (x-y))
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma projectU_grad (M:ropes Cover (Co L (Hooks G)) (Hooks G)){q i:Fin (r+1)}(h:q≠i): dropL L M q i-owns L M i = reedG i (projectU L M q i) := by
   funext p x; let a:= (p i).2.2; let y:= (p i).1; let k:= axisEquiv.symm (p i).2.1
   let w:=(p q).1
   let A (z: Cover) (j:G.ColorIndex):= projectU L M q i (aside i p) z j x
   let B v:= spring L M (waive w v a) x
   have he z: A z a= -∑ v:Axis,B v * chalk v (z-w) := by unfold A projectU; rw [remote h _ _ (p i),leaves]
   have hf : A (y+step k) a = A y a- B k:=by
      rw [he,he]; rw [show y+step k-w=y-w+step k by abel]; simp only [chalk_inc, mul_add,mul_ite,mul_one,mul_zero,Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]; abel
   have hg : echoL L M q i p x=B k:= by unfold echoL B; rw [show waive w k a = (w,(p i).2) by simp [waive,stone,k,a,← coord_map]]
   change owns L M i p x-echoL L M q i p x-owns L M i p x= A (y+step k) a-A y a; rw [hg,hf]; abel
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma projectU_fee {M:ropes Cover (Co L (Hooks G)) (Hooks G)}{i q:Fin (r+1)}(h:dragCup terrain s C M)(he:q≠i):
    sells L s (Fintype.card Axis*C) (Tolled 1 (apex i (projectU L M q i))) := by
   have hp:=h.1
   refine ⟨by positivity,fun p x=>⟨q,?_⟩⟩
   let z:=(p i).1; let a:= (p i).2.2; let y:=(p q).1; set w:= tollD 1 p; have hw: 0<w:=toll_pos p 1
   rw [Tolled, abs_div,abs_of_pos hw, div_le_iff₀ hw,apex, projectU,remote he _ _ (p i),leaves, abs_neg]
   set V:= Real.exp (-s*terrain.gap (parentC L y) x.1)
   have hV : 0≤ V:= (Real.exp_pos _).le
   apply le_trans (b:=∑ _ : Axis,(C*V)*w); swap; · simp [V,w,y]; ring_nf; rfl
   apply (Finset.abs_sum_le_sum_abs ..).trans
   apply Finset.sum_le_sum; intro j _
   rw [abs_mul]
   have hh: |spring L M (waive y j a) x|≤ C*V:= spring_pt h _ _
   have he : (size (z-y):ℝ)≤ soar terrain p:= Nat.cast_le.mpr (leg_le terrain (Prod.fst ∘ p) q i)
   have hg : |chalk j (z-y)|≤w:= (chalk_fee ..).trans (he.trans (by simp [w,tollD]))
   exact mul_le_mul hh hg (abs_nonneg _) (by positivity)

def pareDeck (L:Side)(M:ropes Cover (Co L α) β)(p: Fin (r+1))(s: Finset (Fin (r+1))) : Fin (r+1)→ Roof α β (r+1):= fun i=> if i∈s then dropL L M p i else owns L M i
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
lemma pare_fee {p:Fin (r+1)}{M:ropes Cover (Co L α) β}(h:dragCup terrain t D M)(e:0≤t) (s: Finset (Fin (r+1)))(i): sells L t (D+D) (pareDeck L M p s i):=by
   unfold pareDeck; split; exact drop_fee h e p i
   exact (ownS h i).cost (le_add_of_nonneg_right h.1)

theorem pare_delta {M: ropes Cover (Co L (Hooks G)) (Hooks G)}(p:Fin (r+1))(s':Finset (Fin (r+1)))(w:p∉ s')(h: dragCup terrain s D M) (ha: Amber terrain t C T)(hg:Draft T t E)(hf: Smooth T)(hs:0≤σ)(ht:σ<s)(hv:s/L.val≤t')(hp:t'<t) :
   Amber terrain σ ((s'.card:ℝ)*(max (D+D+(D+D)) (Fintype.card Axis*D) ^(r+1)*(E*ceilPoly 1 (t-t')*Real.exp (8*s))*tiePay (Co L (Hooks G)) (r+1) (s-σ))) (pump T (pareDeck L M p s') - pump T (owns L M)) := by
   induction s' using Finset.induction_on with
   | empty=> rw [show pareDeck _ _ _ _=owns L M from funext fun i=> if_neg (Finset.notMem_empty _),sub_self,Finset.card_empty,Nat.cast_zero,zero_mul]; exact Amber.zero
   | @insert i s' e ih=>
     have he : p≠i ∧ p∉s' := by simpa only [Finset.mem_insert,not_or] using w
     specialize ih he.2
     let Q:= pump T (pareDeck L M p s')
     have hv' := lt_of_le_of_lt hs ht
     have hw:∃ c : ℝ, c=max (D+D+(D+D)) (Fintype.card Axis*D) ^ (r+1)*(E*ceilPoly 1 (t-t')*Real.exp (8*s))*tiePay (Co L (Hooks G)) (r+1) (s-σ) ∧ Amber terrain σ c (pump T (pareDeck L M p (insert i s')) - Q):= by
       refine ⟨_,rfl,?_⟩
       have heq : pareDeck L M p (insert i s')=Function.update (pareDeck L M p s') i (dropL L M p i):=by
          ext1 j; by_cases hh:j=i<;> simp [Function.update_of_ne, *, pareDeck]
       have hstill : pareDeck L M p s' i = owns L M i:=if_neg e
       rw [heq]; apply neighbor 1 (projectU L M p i) (drop_fee h hv'.le p i) (pare_fee h hv'.le s') hv' hs ht hp hv _ (projectU_fee h he.1) _ hf ha hg
       · rw [hstill]; exact projectU_grad _ he.1
       intro j H x u v; ext y; unfold pareDeck; split
       · unfold dropL; simp only [Pi.sub_apply,owns,echoL]; rw [remote he.1 x u v, remote H x u v]
       unfold owns; rw [remote H x u v]
     obtain ⟨c,hc,H⟩:=hw; rw [←hc] at ih ⊢; rw [show pump T (pareDeck L M p (insert i s'))-pump T (owns L M)=(pump T (pareDeck L M p (insert i s'))-Q)+(Q-pump T (owns L M)) by abel, Finset.card_insert_of_notMem e, Nat.cast_add,Nat.cast_one,add_mul,one_mul, add_comm (_*c)]; exact H.add ih
end peg
end YM.WilsonCoeffUV.Bank
