import YM.FormalBulk08.Broc.Tomes

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{r t m e E:ℕ}{A B σ η:ℝ}{T:Pot G}

def Pale (T:Pot G)(e:ℕ):=∀ i<e,∀ j,T i j=0
lemma pale_stone (h:Pale T e): ∀ n i, i<e → coeff i (stone T n)=0:= by
   intro n i hi; simp_rw [sow_coeff,sow,h i hi]; simp only [cum_zero,map_zero,Finset.sum_const_zero]
def Sane (T:Pot G)(E:ℕ):=∀ a:hue G,∀ e≤E,0<e → value a (T e 2)=0
lemma hatch_one (hG:G.Simple)(hs:0<σ)(E j:ℕ): ∃ δ K:ℝ,0<δ ∧ 0≤K∧ ∀ e≤E,∀ (T:Pot G),Temper T E →∀ A,Fits T E σ A → Pale T e → (∀ a:hue G,0<e→value a (T e 2)=0) → T e (j+2) ≠ 0 → ∃ p:LeafD G, p.u=e ∧ p.t=j ∧ Honest p E δ (A*K) ∧ T e (j+2)=p.arr e (j+2) := by
   let t:=j+1
   obtain ⟨δ,K,h,h',H⟩:= regimen G hG hs (j+1); obtain ⟨η,D,hx,d,Q⟩:=given_path G h t E
   refine ⟨min δ η,K+K*D,lt_min h hx,add_nonneg h' (mul_nonneg h' d),fun e he T P A F a f nz=>?_⟩
   let hp:=P.valence e he _ nz; have hr:j+2≤e+2:=hp.2.1;let hv:=P.up e he (j+2);let hb:=F.pay e he (j+2);have hA:=F.money
   obtain ⟨R,Hh⟩:= H E e T A hb hv (P.ports e he (j+2)) P.rite he (by omega) (pale_stone a) (0<e) (fun e _ b=>f b e)
   obtain ⟨S,hS,ht⟩:= Q e hr hp.2.2 (issue R) _ Hh.coins
   let p:LeafD G:=⟨e,j,R,S⟩; refine ⟨p,rfl,rfl,⟨he,by change j≤e;omega, hp.2.2,Hh.coins.mono (min_le_left ..) (by gcongr;exact le_add_of_nonneg_right (by positivity)),Hh.bumps,hS,ht.mono (min_le_right ..) (?_)⟩,?_⟩ -- ht.mono η≥...
   · rw [mul_add,mul_assoc]; exact le_add_of_nonneg_left (mul_nonneg hA h')
   exact cum_cmp hv (hS.civil e (t+1)) σ η _ _ hs.le hx.le hb (ht.pay e he _) 0 (fun n=> (Hh.license n).trans (hS.coins n).symm)
structure Sheet (T:Pot G)(e j:ℕ)(P: List (LeafD G))(E:ℕ)(σ A:ℝ): Prop where
   printed:Edition P E σ A
   cap:P.length≤j
   tags:∀ p∈P,p.u=e ∧ p.t<j
   matched:∀ i<j,binding P e (i+2)=T e (i+2)
lemma no_extra {P:List (LeafD G)}(h:Sheet T e m P E σ A)(hp: binding P t r≠0): e≤t ∧ (t=e → ∃ k<m,r=k+2) ∧ (e<t→2<r) := by
   obtain ⟨a,ha,hx⟩:=binding_root hp; have H:= (h.printed.honest a ha).paths.lives t r hx; have he:=h.tags a ha
   exact ⟨by omega,fun ht=>⟨a.t,he.2,by omega⟩,by omega⟩
lemma sheet_one {Q:List (LeafD G)}(H:Sheet T e m Q E σ A)(b:LeafD G)(h:b.u=e)(hb:b.t=m)(e': Honest b E σ B)(p: b.arr e (m+2)= T e (m+2)) : Sheet T e (m+1) (b::Q) E σ (B+A):= by
   constructor
   · exact by_edition e' H.printed
   · rw [List.length_cons];exact Nat.succ_le_succ H.cap
   · intro p hp; rcases List.mem_cons.mp hp with rfl|hp; exact ⟨h,hb.symm ▸ Nat.lt_succ_self _⟩; exact ⟨(H.tags _ hp).1,Nat.lt_add_right 1 (H.tags _ hp).2⟩
   intro i hi;rw [binding_one,Pi.add_apply,Pi.add_apply]; by_cases hp:i=m
   · subst i; rw [p,show binding Q e (m+2)=0 from ?_, add_zero]
     by_contra hx; obtain ⟨k,hx,hz⟩:= (no_extra H hx).2.1 rfl; omega
   rw [H.matched i (by omega),show b.arr e (i+2)=0 from ?_, zero_add]; by_contra hx; have ht:=e'.paths.lives _ _ hx; omega
lemma sheet_mono {P:List (LeafD G)}(h: Sheet T e m P E σ A)(h1:η≤σ)(h2:A≤B): Sheet T e m P E η B:= {h with printed:=h.printed.mono h1 h2}
lemma hatch_list (hG:G.Simple)(hs:0<σ)(E j:ℕ): ∃ δ K:ℝ,0<δ ∧ 0≤K∧ ∀ e≤E,∀ (T:Pot G),Temper T E →∀ A,Fits T E σ A → Pale T e → (∀ a:hue G,0<e→value a (T e 2)=0) → ∃ P:List (LeafD G), Sheet T e j P E δ (A*K):= by
   induction j with
   | zero=> refine ⟨σ,0,hs,le_rfl,fun e he T h A H B he'=>⟨[],no_edition (by simp),by simp,by simp,fun i hi=>by omega⟩⟩
   | succ j ih=>
     obtain ⟨δ,K,h,h',H⟩:=ih
     obtain ⟨η,B,hp,hB,H'⟩:= hatch_one hG hs E j
     let τ:=min δ η
     refine ⟨τ,B+K,lt_min h hp,add_nonneg hB h',fun e he T P A k a b=>?_⟩
     obtain ⟨l,hl⟩:= H e he T P A k a b
     have hw:=sheet_mono hl (min_le_left δ η) le_rfl
     have hh:=k.money; by_cases hZ:T e (j+2)=0
     · have hr: binding l e (j+2)=0:=by by_contra u; obtain ⟨v,hx,hv⟩:= (no_extra hl u).2.1 rfl; omega
       exact ⟨l, hw.printed.mono le_rfl (by rw [mul_add];exact le_add_of_nonneg_left (mul_nonneg hh hB)), hl.cap.trans (by omega), fun p he=>⟨(hl.tags _ he).1,Nat.lt_succ_of_lt (hl.tags _ he).2⟩,fun i hi=>by
        by_cases hz:i=j
        · subst i;exact hr.trans hZ.symm
        exact hl.matched i (by omega)⟩
     obtain ⟨p,hp,hi,hP,Ht⟩:= H' e he T P A k a b hZ
     rw [mul_add]; exact ⟨p::l,sheet_one hw p hp hi (hP.mono (min_le_right ..) le_rfl) Ht.symm⟩
lemma hatch (hG:G.Simple)(hs:0<σ)(E:ℕ): ∃ δ K:ℝ,0<δ ∧ 0≤K ∧ ∀ e≤E,∀ (T:Pot G),Temper T E →∀ A,Fits T E σ A → Pale T e → (∀ a:hue G,0<e→value a (T e 2)=0) → ∃ P:List (LeafD G), Sheet T e (E+1) P E δ (A*K) ∧ binding P e=T e := by
   obtain ⟨δ,K,h,hK,H⟩:=hatch_list hG hs E (E+1); refine ⟨δ,K,h,hK,fun e he T p A H' a b=> ?_⟩
   obtain ⟨P,hP⟩:=H e he T p A H' a b;refine ⟨P,hP,?_⟩; funext r; by_cases hr:2≤r ∧ r≤E+2
   · obtain ⟨i,hi⟩:∃ i,r=i+2:= ⟨r-2,by omega⟩;rw [hi];exact hP.matched i (by omega)
   have hE:binding P e r=0:= by by_contra u; obtain ⟨j,hv,hb⟩:= (no_extra hP u).2.1 rfl; omega
   rw [hE]; symm; by_contra z; have hh:=p.valence e he r z; have hu:=level_nil hG hs (H'.pay e he 1) p.rite he (p.ports e he 1) (p.up e he 1) (pale_stone a); exact z ((show r=1 by omega) ▸ hu)
end YM.FormalBulk08.Broc
