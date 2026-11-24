import YM.WilsonCoeffUV.Stable.Height
/-!
# Ward post charges in rolling rooted position moments
(important not to charge dimension even when retaining aperture).
-/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Wilson Tree Power PowerSeries Exterior Soil Precision Embroider Fountain Cosmos
open scoped Topology BigOperators
variable {L:Side}{U α V W ι : Type*}{i e k r u j l:ℕ} {A B C D s σ η δ : ℝ} {o:Cover}{G:Gauge}
lemma finance_terms [Fintype α]{s:α→U→ℝ}{F:α→ℝ}(p:∀ i,SumBudget (s i) (F i)): SumBudget (fun i:α×U=>s i.1 i.2) (∑ i,F i):= finance_glob p ⟨fun i=>cap_nn (p i),summable_of_hasFiniteSupport (Set.toFinite _), by rw [tsum_fintype]⟩
private lemma spark_cost (a b:G.Color)(q:Edge Cover)(j:G.ColorIndex)(k:ℕ) : SumBudget (fun x=>‖spark a b q j k x‖) ((Fintype.card (Fin k→ Hooks G):ℝ)* ∑ i,‖rye (electric a b j) k i‖):=by
    let f:=spark a b q j k; let C:= ∑ i,‖rye (electric a b j) k i‖; have hc:0≤C:= Finset.sum_nonneg fun i _=> norm_nonneg _
    let T (x:Fin k→ Hooks G):dock Cover (Hooks G) k:= fun i=>(q.1,x i); let S:= Finset.univ.image T; let Q x:= if x∈S then C else 0
    have hx : SumBudget Q ((Fintype.card (Fin k→Hooks G):ℝ)*C):= by
        have hh : Summable Q:= summable_of_ne_finset_zero (s:=S) (fun i hi=>if_neg hi)
        refine ⟨fun i=>by unfold Q; split; exact hc; rfl,hh,?_⟩
        rw [tsum_eq_sum (s:=S) (fun i hi=>if_neg hi), show (∑ i∈ S,Q i)=∑ _i∈ S,C from Finset.sum_congr rfl (fun i hi=>if_pos hi), Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le.trans_eq (Finset.card_univ)) hc
    apply budget_minor hx (fun i=>norm_nonneg (f i)); intro i; by_cases h:f i=0; · rw [show f i=0 from h,norm_zero]; exact hx.1 _
    have he:i∈ S:=Finset.mem_image.mpr ⟨Prod.snd ∘ i,Finset.mem_univ _,funext fun x=> Prod.ext (show (T (Prod.snd ∘ i) x).1= _ from (spark_here a b q j i h x).symm) rfl⟩
    rw [show Q i=C from if_pos he]; exact spark_bound ..

variable [NormedAddCommGroup V][NormedSpace ℝ V]
private abbrev Earth (G:Gauge)(r) := Cover × dock Cover (Hooks G) r
def rance (o:Cover)(η:ℝ)(u:ℕ)(Y:Cover→ Ten V (YForest G) r)(A:ℝ): Prop:= Award (fun i:Earth G r=> Y i.1 i.2) (fun i=> autumn η u (stance o i.1 i.2)) A
namespace rance
variable {P Q:Cover→Ten V (YForest G) r}
omit [NormedSpace ℝ V] in lemma epochT(p:rance o η u P A)(h:A≤B) : rance o η u P B:= Award.more p h
omit [NormedSpace ℝ V] in lemma plus (p:rance o η u P A)(q:rance o η u Q B)(h:0≤η): rance o η u (P+Q) (A+B):= Award.plus p q fun _=>zero_le_one.trans (autumn_pos h ..)
lemma scaled (p:rance o η u P A)(c:ℝ):rance o η u (c•P) (|c| *A):= Award.μ p c
omit [NormedSpace ℝ V] in lemma sum {S:Finset ι}{P:ι→Cover→Ten V (YForest G) r}{M:ι→ℝ}(h:∀ i∈S,rance o η u (P i) (M i))(p:0≤η): rance o η u (fun x=>∑ i∈ S,P i x) (∑ i∈ S,M i):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Award.zero
   | @insert i S e ih=> simp_rw [Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=>h j (Finset.mem_insert_of_mem hj)) p
lemma spool (p:rance o η u P A)(h:0≤η): rance o η u (fun x=>swirl (P x)) A:=by
   have he v: rance o η u (fun x y=>P x (y ∘ (v:Equiv.Perm (Fin r)))) A := by
       let S:= v.symm.arrowCongr (Equiv.refl (YForest G)); exact Award.pivot p ((Equiv.refl _).prodCongr S) rfl (funext fun j=>congr_arg (autumn η u) (pace_perm o j.1 j.2 v))
   let C:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hp:0<C:=by unfold C; positivity
   have hv:= (rance.sum (S:=Finset.univ) (fun i _=>he i) h).scaled (C⁻¹); rw [abs_of_pos (show 0<C⁻¹ by positivity),Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hv; change rance o η u _ (C⁻¹*(C*A)) at hv; rw [inv_mul_cancel_left₀ hp.ne'] at hv; exact hv
omit [NormedSpace ℝ V] in lemma token (p:rance o η u P A)(v:Axis)(h:0≤η)(he:η≤1): rance o η u (fun x=>P (x-step v)) (2^u*A):=by
    let S : Equiv.Perm (Earth G r):=(Equiv.subRight (step v)).prodCongr (Equiv.refl _); let s (x:Earth G r):= autumn η u (stance o x.1 x.2); let f (x:Earth G r):= P x.1 x.2
    have hv:Award (f ∘ S) (s ∘ S) A:= Award.pivot p S rfl rfl
    have hp (x:Earth G r): s x ≤ 2^u*s (S x):=by
        have ht : stance o x.1 x.2 ≤ stance o (S x).1 (S x).2 +1:= (fee_stance ..).trans (Nat.add_le_add_left (show Bank.terrain.gap x.1 (x.1-step v) ≤1 by change size ((x.1-step v)-x.1)≤1; rw [show x.1-step v-x.1= -step v by abel,size_neg]; simp [size,apply_ite Int.natAbs]) _)
        apply (autumn_mono h u ht).trans; refine (autumn_tax h ..).trans ?_; rw [mul_comm (autumn _ _ _)]
        apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (autumn_pos h ..)); unfold autumn; rw [Nat.cast_one,mul_one]; gcongr; linarith
    exact budget_minor (cap_scale hv (show 0≤(2:ℝ)^u by positivity)) (fun _=>mul_nonneg (zero_le_one.trans (autumn_pos h ..)) (norm_nonneg _)) (fun x=>(mul_le_mul_of_nonneg_right (hp x) (norm_nonneg _)).trans_eq (by rw [mul_assoc]; rfl))
end rance
private def spanLink (U:Type*)(k e r:ℕ)(h:k+e=r) : ((Fin e→U)×(Fin k→U))≃(Fin r→U) where
    toFun x:= Fin.append x.2 x.1 ∘ Fin.cast h.symm
    invFun x:= (x ∘ Fin.cast h ∘ Fin.natAdd k,x ∘ Fin.cast h ∘ Fin.castAdd e)
    left_inv := by subst r; rintro ⟨x,y⟩; exact Prod.ext (funext fun i=>by simp) (funext fun i=>by simp)
    right_inv :=by subst r; intro x; ext1 i; refine Fin.addCases (fun _=>by simp) (fun _=>by simp) i

lemma wick_rance {P:Gen V (YForest G)}(a b:G.Color)(v:Axis)(j:G.ColorIndex)(h:Fruit o η u (P (r-k+1)) A)(p:0≤η): rance o η u (fun x=> wickLamp a b (x,v) j k P r) ((Fintype.card (Fin k→ Hooks G) * ∑ i,‖rye (electric a b j) k i‖) * (r-k+1:ℕ)*A):=by
    let M:ℝ:= Fintype.card (Fin k→ Hooks G)*∑ i,‖rye (electric a b j) k i‖; have hm:0≤M:=mul_nonneg (by positivity) (Finset.sum_nonneg fun i _=>norm_nonneg _)
    let n:= r-k+1; have ha:=h.C; have ht:0 ≤ (n:ℝ):= by positivity
    by_cases he:r<k; · simp_rw [wick_pos _ _ _ _ _ he]; exact rance.epochT Award.zero (show 0≤ M * n*A by positivity)
    simp_rw [wick_leg _ _ _ _ _ (Nat.le_of_not_gt he)]; apply rance.spool _ p; let Q:=spanLink (YForest G) k (r-k) r (by omega)
    let Y: ((Cover×dock Cover (Hooks G) (r-k)) × dock Cover (Hooks G) k) ≃ Earth G r:= (Equiv.prodAssoc ..).trans ((Equiv.refl _).prodCongr Q); let T (x:Earth G (r-k)):dock Cover (Hooks G) n:= Fin.cons (stone (x.1,v) j) x.2
    have hi:Injective T:= by
        intro i j h; refine Prod.ext ?_ ?_ ; swap; · exact funext fun p=> congr_fun h (Fin.succ p)
        exact congr_arg (fun y:dock Cover (Hooks G) n=>(y 0).1) h
    have hx:= cap_scale (prod_cap (finance_pick h hi) hm (fun x=>spark_cost a b (x.1,v) j k)) ht
    rw [show ((Fintype.card _:ℝ)*_)*(r-k+1:ℕ)*A=(n:ℝ)*(A*M) from by unfold n M; ring]; unfold rance Award
    refine cap_walk _ _ Y (fun _=>rfl) (budget_minor hx ?_ ?_)
    · intro i; exact mul_nonneg (zero_le_one.trans (autumn_pos p ..)) (norm_nonneg _)
    intro i; let x:= (Y i).1; let y:= (Y i).2
    change autumn η u (stance o x y)* ‖interweave (spark a b (x,v) j k) (sever (stone (x,v) j) P (r-k)) r y‖≤ _
    rw [interweave,dif_pos (show k+(r-k)=r by omega)]
    have hL: Q.symm y=(i.1.2,i.2):= Q.symm_apply_apply ..
    rw [show (y ∘ Fin.cast _ ∘ Fin.castAdd _)=i.2 from congr_arg Prod.snd hL, show (y ∘ Fin.cast _ ∘ Fin.natAdd k)= i.1.2 from congr_arg Prod.fst hL]
    set f:= spark a b (x,v) j k; change _*‖f i.2 • _‖≤ _; by_cases hg:f i.2=0; · rw [hg,zero_smul,norm_zero,mul_zero]; exact hx.1 _
    have hS: stance o x y≤ tread Bank.terrain o (T i.1):=by
       let K: Fin (r+2)→Cover:= Fin.cons o (stud x y); let F:=stud o (T i.1); have hw (c:Fin (r+2)):∃ j,F j=K c:=by
           refine Fin.cases ⟨0,rfl⟩ (fun a'=>?_) c; refine Fin.cases ⟨Fin.succ 0,rfl⟩ (fun c=>?_) a'
           let S : Fin (k+(r-k))≃ Fin r:= finCongr (by omega); obtain ⟨c,rfl⟩:= S.surjective c; refine Fin.addCases (fun d=>?_) (fun d=>?_) c
           · exact ⟨Fin.succ 0,(spark_here a b (x,v) j (y ∘ S ∘ Fin.castAdd (r-k)) (by rw [show y ∘ S ∘ Fin.castAdd (r-k)=i.2 from congr_arg Prod.snd hL]; exact hg) d).symm⟩
           exact ⟨Fin.succ (Fin.succ d),(show (i.1.2 d).1= _ from congr_arg Prod.fst (congr_fun (congr_arg Prod.fst hL).symm d))⟩
       apply league_le Bank.terrain K; intro i j; obtain ⟨a,ha⟩:= hw i; obtain ⟨b,hb⟩:=hw j; rw [←ha,←hb]; exact leg_le Bank.terrain F _ _
    rw [norm_smul,sever,Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (R:=ℝ),norm_smul, Real.norm_eq_abs ((r-k+1:ℕ):ℝ), abs_of_nonneg ht]
    refine (mul_le_mul_of_nonneg_right (autumn_mono p u hS) (by positivity)).trans_eq ?_
    change _*(‖f i.2‖*((n:ℝ)* ‖P n (T i.1)‖))=n*((hedge o η u (T i.1) * ‖P n (T i.1)‖)*‖f i.2‖); ring
end YM.WilsonCoeffUV.Shard
