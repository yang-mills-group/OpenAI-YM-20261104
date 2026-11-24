import YM.WilsonCoeffUV.Marked.Bounds.Wig
/-!
# Span thru arbitrary mixed operations (no dilation of pre-block widths)

Include e=0 field-independent vertices. S nonempty where summing.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{p:ι→U}{d:Bank.Distance U}{D k:ι→ℕ}{i j e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}

lemma across_.charge (p:ι→U)(d:Distance U)(S: Finset ι)(x:dock U α r)(y:dock U β r): billow d p S x y≤ Syn d p S y + ∑ i, d.gap (y i).1 (x i).1:=by
    -- prove directly
    let X:= foyer p S x; let Y:= foyer p S y; let L:=visitN p S x y; let A:= Syn d p S y; let D (i:Fin r):= d.gap (y i).1 (x i).1; let B:=∑ i,D i
    have hp i:(∃ j,L i=Y j)∨(∃ j:Fin r,L i=(x j).1):=by
       cases i with
       | inr i=> exact Or.inl ⟨.inr i,rfl⟩
       | inl i=> cases i with
                 | inl i=> exact Or.inl ⟨.inl i,rfl⟩
                 | inr i=> exact Or.inr ⟨i,rfl⟩
    have he i j: d.gap (Y i) (x j).1≤ A + D j:= (d.tri _ (Y (.inr j)) _).trans (add_le_add_left (leg_le _ Y i _ ) _)
    have hv i:D i≤B:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    refine league_le d L fun i j=>?_; rcases hp i with ⟨u,hu⟩|⟨u,hu⟩ <;> rcases hp j with ⟨v,hv'⟩|⟨v,hv'⟩<;> rw [hu,hv']
    · exact (leg_le d Y u v).trans (Nat.le_add_right ..)
    · exact (he u v).trans (add_le_add_right (hv v) _)
    · rw [d.swap]; exact (he v u).trans (add_le_add_right (hv u) _)
    by_cases h:u=v; · subst u; rw [d.self]; exact Nat.zero_le _
    have hm: D u+D v≤ B:=by
        unfold B; rw [← Finset.add_sum_erase _ D (Finset.mem_univ u)]; exact add_le_add_right (Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_erase_of_ne_of_mem (Ne.symm h) (Finset.mem_univ v))) _
    refine (d.tri _ (Y (.inr u)) _).trans ?_; rw [d.swap]; exact (add_le_add_right (he (.inr u) v) _).trans ((by omega:A+(D u+D v)≤A+B) |>.trans_eq (Eq.refl _) |>.trans' (by change D u+(A+D v)≤_; omega))

lemma motionNp [NormedAddCommGroup V][NormedSpace ℝ V]{G:ropes U α β}{p:ι→U}{F:Ten V (U×α) i}{S:Finset ι}(h:dragCup d σ B G)(v:Wig d p σ A S F)(q:0≤σ): Grapple d p σ (B^i*A) S (gloss G F):=by
    refine ⟨mul_nonneg (pow_nonneg h.1 _) v.1,fun x y=>?_⟩
    let n:= billow d p S x y; let L:=Syn d p S y; let M (i:Fin i):=d.gap (y i).1 (x i).1; let Z:= ∑ i,M i
    have hx:n≤L+Z:= across_.charge p d S x y
    have hv : ‖∏ i,G (y i) (x i)‖ ≤ B^i*Real.exp (-σ*↑Z):=by
        have h1 i: ‖G (y i) (x i)‖≤B*Real.exp (-σ*M i):= h.2 ..
        have hy:= Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i (_:i∈Finset.univ)=> h1 i); rw [norm_prod]; apply hy.trans; unfold Z; rw [Finset.prod_mul_distrib]; simp_rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin, Nat.cast_sum,Finset.mul_sum,Real.exp_sum]; exact le_rfl
    rw [gloss,ribbon,norm_smul]; refine (mul_le_mul hv (v.2 y) (norm_nonneg _) ((norm_nonneg _).trans hv)).trans ?_; rw [mul_mul_mul_comm,←Real.exp_add,←mul_add,add_comm (Z:ℝ),← Nat.cast_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hx) (neg_nonpos.mpr q))) (mul_nonneg (pow_nonneg h.1 _) v.1)

lemma lace_.rain (d:Distance U)(p:ι→U)(x:dock U α r)(y:dock U α 2)(S:Finset ι) : billow d p S x y≤ Syn d p S (Fin.cons (y 1) (Fin.cons (y 0) x)):=by
   let v:=visitN p S x y; let w:=foyer p S (Fin.cons (y 1) (Fin.cons (y 0) x)); apply league_le d v
   have he i:∃ j,v i=w j:=by
      cases i with
      | inl i=>cases i with
              | inl i=> exact ⟨.inl i,rfl⟩
              | inr i=> exact ⟨.inr i.succ.succ,rfl⟩
      | inr i=> fin_cases i
                · exact ⟨.inr (Fin.succ 0),rfl⟩
                exact ⟨.inr 0,rfl⟩
   intro i j; obtain ⟨a,ha⟩:= he i; obtain ⟨b,hb⟩:= he j; rw [ha,hb]; exact leg_le ..

lemma grassyRain [NormedAddCommGroup V][NormedSpace ℝ V]{G:ropes U α α}{P:Gen V (U×α)}(h:dragCup d σ B G)(v:Wig d p σ A S (P (r+2)))(q:0≤σ): Grapple d p σ (B*A*sealM r (r+1)) S (rain G P r):=by
    have ht:0 ≤ sealM r (r+1):=by unfold sealM; positivity
    refine ⟨mul_nonneg (mul_nonneg h.1 v.1) ht,fun x y=>?_⟩; rw [rain_spell,norm_smul,show 1/2*_*_ *_=sealM r (r+1)*G (y 0) (y 1) by unfold sealM; push_cast; ring,norm_mul,Real.norm_of_nonneg ht]; let z:=billow d p S x y
    have he : ‖G (y 0) (y 1)‖≤ B:= (h.2 ..).trans (mul_le_of_le_one_right h.1 (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr q) (by positivity))))
    have hx : ‖P _ (Fin.cons (y 1) (Fin.cons (y 0) x))‖≤A*Real.exp (-σ*z):= (v.2 _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (lace_.rain d p x y S)) (neg_nonpos.mpr q))) v.1); apply (mul_le_mul (mul_le_mul_of_nonneg_left he ht) hx (norm_nonneg _) (mul_nonneg ht h.1)).trans_eq; unfold z; ring

-- joint cross arbor. adapt term kernel line; unchanged width
lemma splat_t {a b c:Type}[Fintype a][Fintype b][Fintype c](d:Distance U)(p:a→U)(q:b→U)(w:c→U)(h:∀ i,(∃ j,w i=p j)∨(∃ j,w i=q j))(i j): league d w≤league d p+d.gap (p i) (q j)+league d q:=by
   let P:=league d p; let Q:=league d q; let K:=d.gap (p i) (q j); have he x y:d.gap (p x) (q y)≤ P+K+Q:= (d.tri _ (p i) _).trans ((add_le_add (leg_le ..) ((d.tri _ (q j) _).trans (add_le_add_right (leg_le ..) _))).trans_eq (add_assoc ..).symm); apply league_le d w; intro i j; rcases h i with ⟨a,ha⟩|⟨a,ha⟩<;>rcases h j with ⟨b,hb⟩|⟨b,hb⟩<;> rw [ha,hb]
   · exact (leg_le d p _ _).trans (by omega)
   · exact he a b
   · rw [d.swap]; exact he b a
   exact (leg_le d q _ _).trans (by omega)
lemma riverRow (d:Distance U)(p:ι→U)(x:dock U α (i+j))(y:dock U α 2)(S:Finset ι) :
     billow d p S x y ≤ soar d (Fin.cons (y 0) (x∘ Fin.castAdd j)) + d.gap (y 0).1 (y 1).1+ Syn d p S (Fin.cons (y 1) (x ∘ Fin.natAdd i)):=by
    let a: Fin (i+1)→ U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd j); let b: Fin (j+1) → U × α:= Fin.cons (y 1) (x ∘ Fin.natAdd i); refine splat_t d (Prod.fst ∘ a) (foyer p S b) (visitN p S x y) ?_ 0 (.inr 0); intro k
    cases k with
    | inl k=> cases k with
             | inl k=> exact Or.inr ⟨.inl k,rfl⟩
             | inr k=> refine Fin.addCases (m:=i) (n:=j) (fun k=>Or.inl ⟨k.succ,rfl⟩) (fun k=>Or.inr ⟨.inr k.succ,rfl⟩) k
    | inr k=> fin_cases k
              · exact Or.inl ⟨0,rfl⟩
              exact Or.inr ⟨.inr 0,rfl⟩

lemma grassyFlow [NormedAddCommGroup V][NormedSpace ℝ V]{G:ropes U α α}{P:Gen ℝ (U×α)}{Q: Gen V (U×α)}(h:dragCup d σ B G)(v:Amber d σ A (P (i+1)))(e:Wig d p σ C S (Q (j+1)))(q:0≤σ): Grapple d p σ (sealM i j*B*A*C) S (rill G P Q (i+j) i j):=by
    have ht:0≤ sealM i j:=by unfold sealM; positivity;
    refine ⟨mul_nonneg (mul_nonneg (mul_nonneg ht h.1) v.1) e.1,fun x y=>?_⟩; let n:= billow d p S x y; let H:=d.gap (y 0).1 (y 1).1; let a : Fin (i+1) → U×α:= Fin.cons (y 0) (x ∘ Fin.castAdd j); let b : Fin (j+1) → U×α:= Fin.cons (y 1) (x∘ Fin.natAdd i); let X:= soar d a; let Y:=Syn d p S b; have he:n≤ X+H+Y:= riverRow d p x y S
    rw [rill_spell,norm_smul,show 1/2*_ *_*_ =sealM i j *G (y 0) (y 1) by unfold sealM; ring,norm_mul,norm_mul,Real.norm_of_nonneg ht]; calc
    _ ≤ (sealM i j*(B*Real.exp (-σ*H))*(A*Real.exp (-σ*X)))*(C*Real.exp (-σ*Y)) := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (h.2 ..) ht) (v.2 a) (norm_nonneg _) (mul_nonneg ht (mul_nonneg h.1 (Real.exp_pos _).le))) (e.2 b) (norm_nonneg _) (mul_nonneg (mul_nonneg ht (mul_nonneg h.1 (Real.exp_pos _).le)) ((norm_nonneg _).trans (v.2 a)))
    _=sealM i j*B*A*C*Real.exp (-σ*(X+H+Y:ℕ)):=by push_cast; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]; ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr he) (neg_nonpos.mpr q))) (mul_nonneg (mul_nonneg (mul_nonneg ht h.1) v.1) e.1)

lemma riverRim [DecidableEq ι](d:Distance U)(p:ι→U)(x:dock U α (i+j))(y:dock U α 2)(_v:J⊆ S):
     billow d p S x y ≤ Syn d p J (Fin.cons (y 0) (x∘ Fin.castAdd j)) + d.gap (y 0).1 (y 1).1+ Syn d p (S\J) (Fin.cons (y 1) (x ∘ Fin.natAdd i)):=by
    let a: Fin (i+1)→ U × α :=Fin.cons (y 0) (x ∘ Fin.castAdd j); let b: Fin (j+1) → U × α:= Fin.cons (y 1) (x ∘ Fin.natAdd i); refine splat_t d (foyer p J a) (foyer p (S\J) b) (visitN p S x y) ?_ (.inr 0) (.inr 0); intro k
    cases k with
    | inl k=> cases k with
             | inl k=> by_cases h:k.val∈ J; · exact Or.inl ⟨.inl ⟨_,h⟩,rfl⟩
                       exact Or.inr ⟨.inl ⟨_, Finset.mem_sdiff.mpr ⟨k.property,h⟩⟩,rfl⟩
             | inr k=> refine Fin.addCases (m:=i) (n:=j) (fun k=>Or.inl ⟨.inr k.succ,rfl⟩) (fun k=>Or.inr ⟨.inr k.succ,rfl⟩) k
    | inr k=> fin_cases k
              · exact Or.inl ⟨.inr 0,rfl⟩
              exact Or.inr ⟨.inr 0,rfl⟩

lemma grassyLeaf [DecidableEq ι]{G:ropes U α α}{P:Gen (Pen D J) (U×α)}{Q:Gen (Pen D (S\J)) (U×α)}(b:J⊆ S)(h:dragCup d σ B G)(v:Wig d p σ A J (P (i+1)))(e:Wig d p σ C (S\J) (Q (j+1)))(q:0≤σ): Grapple d p σ (sealM i j*B*A*C) S (lakeL G b P Q (i+j) i j):=by
    have ht:0≤ sealM i j:=by unfold sealM; positivity
    refine ⟨mul_nonneg (mul_nonneg (mul_nonneg ht h.1) v.1) e.1,fun x y=>?_⟩; let n:= billow d p S x y; let H:=d.gap (y 0).1 (y 1).1; let a : Fin (i+1) → U×α:= Fin.cons (y 0) (x ∘ Fin.castAdd j); let u : Fin (j+1) → U×α:= Fin.cons (y 1) (x∘ Fin.natAdd i); let X:= Syn d p J a; let Y:=Syn d p (S\J) u; have he:n≤ X+H+Y:= riverRim d p x y b
    rw [lakeV,norm_smul,norm_mul,Real.norm_of_nonneg ht,waveJoy]; calc
    _ ≤ (sealM i j*(B*Real.exp (-σ*H)))*((A*Real.exp (-σ*X))*(C*Real.exp (-σ*Y))) := mul_le_mul (mul_le_mul_of_nonneg_left (h.2 ..) ht) ((joy_norm b _ _).trans (mul_le_mul (v.2 a) (e.2 u) (norm_nonneg _) ((norm_nonneg _).trans (v.2 a)))) (norm_nonneg _) (mul_nonneg ht (mul_nonneg h.1 (Real.exp_pos _).le))
    _=sealM i j*B*A*C*Real.exp (-σ*(X+H+Y:ℕ)):=by push_cast; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]; ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr he) (neg_nonpos.mpr q))) (mul_nonneg (mul_nonneg (mul_nonneg ht h.1) v.1) e.1)
end YM.WilsonCoeffUV.Wheel.Mark
