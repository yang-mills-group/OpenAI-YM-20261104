import YM.WilsonCoeffUV.Marked.Paths.Pricing
/-!
# foreshortened publication NOT cutting paths. Quantized Lipschitz
 display coequal until a chosen scale permit. Operator can be applied
 AFTER obtaining angular branches from Fk. Includes any canonical texture
 with priced payment.
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{k h r t i j l e m b:ℕ}{s v u A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{F T X:Bookend V G}
-- Rains default beyond warm

def wild (G:Gauge)(V:Type)(k:ℕ)[NormedAddCommGroup V][NormedSpace ℝ V] : Robes G V k:= fun _=> shelfM 0 _ k

def automa (P:Bookend V G)(k i:ℕ): Robes G V k:= climbSteps P (wild G V k) 0 i
lemma candour {R:Robes G V k} {F:Bookend V G}(h:Nimbus k e F)(v:Rain F e s A)(q:t+m≤e)(p:0<s)(w:Rains R t s A)(x:∀ i< t,(baton R t).2 i=F i): ∃ b:ℝ,∃ E:ℝ,0<b∧Rains (climbSteps F R t m) (t+m) b E:= by
   obtain ⟨b,C,hB,t' ,c,q⟩:= buildC G k t m e q s p; exact ⟨b,C*A,hB,(q V F R A h v w x).1⟩
lemma autoK (G:Gauge)(s:ℝ)(e k:ℕ)(p:0<s):∃ t:ℝ,∃ C:ℝ,0<t∧ t≤ s∧1≤ C∧∀ i≤ e, ∀ (V:Type)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](P:Bookend V G)(A),Nimbus k e P→ Rain P e s A→ Rains (automa P k i) i t (C*A) ∧ ∀ j< i,(baton (automa P k i) i).2 j=P j :=by
    let X i:= buildC G k 0 i.val e (show 0+(i:Fin (e+1)).val≤ e from by omega) s p
    choose v C u hp hs H using X
    let t:=Finset.univ.inf' Finset.univ_nonempty v; have ht:0<t:=  (Finset.lt_inf'_iff _).mpr (fun i _=> u i)
    let W:=Finset.univ.sup' Finset.univ_nonempty C; let k':Fin (e+1):=0
    have hv i:t≤v i:= Finset.inf'_le _ (Finset.mem_univ _); have hu i:C i ≤ W:= Finset.le_sup' _ (Finset.mem_univ _)
    refine ⟨t,W,ht,(hv k').trans (hp k'),(hs k').trans (hu k'),?_⟩; intro i hi V _ _ _ P A b X
    let i':Fin (e+1):=⟨i,by omega⟩; obtain ⟨c,z,r⟩:=H i' V P (wild G V k) A b X ⟨X.1,fun j j'=>by omega⟩ (fun j j'=>by omega); have ht:0+i'.val=i:=Nat.zero_add i; rw [ht] at c z
    exact ⟨c.slack (hv _) (mul_le_mul_of_nonneg_right (hu _) X.1),z⟩
-- append common representations

def streaks (P Q Z:Comet G V r): Prop:= Z.sl=P.sl ∧ Z.sl=Q.sl∧ Z.wage=P.wage+Q.wage
def Pog (P Q Z:RailsP G k i V):Prop:=∀ r v, streaks (P r v) (Q r v) (Z r v)
def Vista (P Q Z:Robes G V k)(i:ℕ):Prop:= ∀ j< i,Pog (P j) (Q j) (Z j)
omit [CompleteSpace V] in
lemma meetA (P Q:Ten V (YForest G) k)(x) : streaks (meteor P x) (meteor Q x) (meteor (P+Q) x):=⟨rfl,rfl,funext fun _=>smul_add ..⟩
omit [CompleteSpace V] in
lemma meldZ (P Q:Bookend V G)(k i) : Pog (shelfM P i k) (shelfM Q i k) (shelfM (P+Q) i k) := fun _ _=> meetA _ _ _
omit [CompleteSpace V] in
lemma innerM {P Q Z:Comet G V r}(h:streaks P Q Z): (volumeR Z i).2=(volumeR P i).2+(volumeR Q i).2:=by
    have ht j: august Z j=august P j+ august Q j:= by
       funext x; unfold august; rw [Pi.add_apply,←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro u _; have hp:rayOne Q u=rayOne Z u:=by unfold rayOne; rw [h.2.1]
       have hq: rayOne P u=rayOne Z u:=by unfold rayOne; rw [h.1]
       rw [hp,hq,h.2.2,Pi.add_apply,smul_add]
    funext j kall x; unfold volumeR; simp only [moved,Pi.add_apply]; split
    next t=> by_cases h:r+(j-i)=kall; · subst kall; simp_rw [shine_lit,ht]; rfl
             simp only [shine_dark h, Pi.zero_apply,zero_add]
    next c=>simp
lemma together (P Q Z: RailsP G k i V)(h:Pog P Q Z)(a:tintR P s A)(b:tintR Q v B)(hp:0<s)(hu:0<v): (linesR Z).2= (linesR P).2+(linesR Q).2:= by
    unfold linesR; simp only [Prod.snd_sum]; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro x _; let J:= RadP G x.val; funext m j y; change (∑' k,(volumeR _ _).2 _ _ _)= _
    change (∑' k:J,(volumeR (Z x k) i).2 m j y)=(∑' k,(volumeR (P x k) i).2 m j y)+(∑' k,(volumeR (Q x k) i).2 m j y)
    have ht k: (volumeR (Z x k) i).2= (volumeR (P x k) i).2+(volumeR (Q x k) i).2:=innerM (h x k)
    have hz (P:RailsP G k i V)(u t:ℝ)(p:tintR P u t)(b:0<u): Summable (fun k=> (volumeR (P x k) i).2 m j y):=by
       let C (r):= integerP (P x r) u
       apply Summable.of_norm_bounded (f:=fun v=> (volumeR (P x v) i).2 m j y) (g:=fun v=>C v* flour G (steep u) x.val j*Real.exp (-steep u*tread Bank.terrain 0 y)) ?_ ?_
       · exact (((p.2 x).2.2.1).mul_right _).mul_right _
       intro i'; exact (volume_price (P x i') b i m j).2 _
    simp_rw [ht,Pi.add_apply]; exact (hz P s A a hp).tsum_add (hz Q v B b hu)
lemma togetherB (P Q Z:Robes G V k)(h:Vista P Q Z e)(p:Rains P e s A)(u:Rains Q e v B)(hp:0<s)(hv:0<v): (baton Z e).2= (baton P e).2+(baton Q e).2:=by
    simp only [baton, Prod.snd_sum]; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i t=>together _ _ _ (h i (Finset.mem_range.mp t)) (p.2 i (Finset.mem_range.mp t)) (u.2 i (Finset.mem_range.mp t)) hp hv)
omit [CompleteSpace V] in
lemma initiated (F:Bookend V G)(k i:ℕ): automa F k (i+1)= Function.update (automa F k i) i (shelfM (F-(baton (automa F k i) i).2) i k):=by change Function.update _ (0+i) _ =_; rw [Nat.zero_add]; rfl
lemma looping (F T: Bookend V G)(p:Nimbus k e F)(q:Nimbus k l T)(a:Rain F e s A)(t:Rain T l u B)(i:ℕ)(h:i ≤ e)(b:i ≤ l)(v:0<s)(z:0<u): Vista (automa F k i) (automa T k i) (automa (F+T) k i) i:=by
    induction i with
    | zero=> intro j v; omega
    | succ i ih=>
       let P:=automa F k i; let Q:=automa T k i; let Z:=automa (F+T) k i
       have hh:i≤ e:=by omega
       have he:i≤l:=by omega
       specialize ih hh he; obtain ⟨s,C,hp,hv,hx,c⟩:=autoK G s e k v; obtain ⟨u,E,he',hv,hx,d⟩:=autoK G u l k z
       have hy:= togetherB P Q Z ih (c i hh V F A p a).1 (d i he V T B q t).1 hp he'
       intro j x; by_cases H:j=i
       · subst j; rw [initiated,initiated,initiated,Function.update_self,Function.update_self,Function.update_self];
         let R:=baton P i; let S:=baton Q i
         change Pog (shelfM (F-R.2) i k) (shelfM (T-S.2) i k) (shelfM (_-(baton Z i).2) i k); rw [hy,show F+T-((baton P i).2+(baton Q i).2)=(F-R.2)+(T-S.2) from by unfold R S; abel]; exact meldZ _ _ k i
       rw [initiated,initiated,initiated,Function.update_of_ne H, Function.update_of_ne H,Function.update_of_ne H]; exact ih j (by omega)
end YM.WilsonCoeffUV.Mer.Rolls
