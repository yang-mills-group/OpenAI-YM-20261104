import YM.WilsonCoeffUV.Vacuum.Gain.Gradient
/-!
# Price lower-order divergence tell in same-level strips.
No shrink for the local tell. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power
open scoped ContDiff Topology BigOperators
variable {G:Gauge} {s A C:ℝ}{r d e:ℕ} {V:Type*}

section
variable [NormedAddCommGroup V][NormedSpace ℝ V]

-- torch at same edge x. Exact concentration; price arithmetic.
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma spark_bound (a b:G.Color)(w:Edge Cover)(j:G.ColorIndex)(x):
    ‖spark a b w j d x‖ ≤ ∑ i, ‖rye (electric a b j) d i‖ := by
  unfold spark fade; simp only [shine_lit]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_));
  rw [norm_smul, Real.norm_eq_abs,Finset.abs_prod]
  apply mul_le_of_le_one_left (norm_nonneg _) ((Finset.prod_le_prod (fun _ _=>abs_nonneg _) ?_).trans (le_of_eq (Finset.prod_const_one)))
  intro v _; rw [spear, Matrix.of_apply]; split<;> norm_num
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma spark_here (a b:G.Color)(w:Edge Cover)(j:G.ColorIndex)(x)(h:spark a b w j d x≠0)(l:Fin d): (x l).1=w.1:= by
   by_contra he; apply h; unfold spark fade; apply Finset.sum_eq_zero; intro i _; rw [Finset.prod_eq_zero (Finset.mem_univ l), zero_smul]; rw [spear,Matrix.of_apply,if_neg]; intro hu; apply he; rw [hu]; rfl

-- oriented length d.gap x+. normalized row.
abbrev port_d (u:Cover)(x:Fin r→ YForest G): ℕ:= league terrain (Fin.cons u (Prod.fst ∘ x))
lemma port_soar (c:YForest G)(x:Fin r→YForest G) : soar terrain (Fin.cons c x) = port_d c.1 x:=by unfold port_d soar; rw [comps_head]
lemma port_perm (p:Cover)(x:Fin r→YForest G)(s:Equiv.Perm (Fin r)): port_d p (x ∘ s)=port_d p x:=by
  let T: Equiv.Perm (Fin (r+1)):= ((finSuccEquiv r).trans (Equiv.optionCongr s)).trans (finSuccEquiv r).symm
  unfold port_d; rw [← league_equiv terrain (Fin.cons p (Prod.fst ∘ x)) T]
  congr 1; funext i; refine Fin.cases (by simp [T]) (fun j=> by simp [T]) i
lemma property_le (p q : Cover)(x:Fin r→YForest G): port_d p x≤ port_d q x+terrain.gap p q:=by
    let z : Fin (r+1) → Cover := Fin.cons q (Prod.fst ∘ x); let y : Fin (r+1) → Cover := Fin.cons p (Prod.fst ∘ x)
    have hp i j : terrain.gap (z i) (z j)≤ port_d q x:= leg_le terrain z i j
    have hv i : terrain.gap (y 0) (y i)≤ port_d q x+terrain.gap p q:= by
       refine Fin.cases (by simp [y,terrain,size]) (fun j=>?_) i
       exact (terrain.tri p q (x j).1).trans ((Nat.add_le_add_left (hp 0 (Fin.succ j)) _).trans_eq (add_comm ..))
    apply league_le terrain y; intro i j
    refine Fin.cases (hv j) (fun k=>?_) i
    refine Fin.cases ?_ (fun b=>?_) j
    · rw [terrain.swap (y _) (y 0)]; exact hv _
    exact (hp k.succ b.succ).trans (Nat.le_add_right ..)

def Twig (p:Cover)(σ A:ℝ)(F:Ten V (YForest G) r): Prop:= 0≤A∧∀ x, ‖F x‖≤ A*Real.exp (-σ*port_d p x)
omit [NormedSpace ℝ V] in
lemma Twig.add {p}{P Q:Ten V (YForest G) r}(h:Twig p s A P)(t:Twig p s C Q): Twig p s (A+C) (P+Q):=⟨add_nonneg h.1 t.1,fun x=>(norm_add_le ..).trans ((add_le_add (h.2 x) (t.2 x)).trans_eq (by ring))⟩
omit [NormedSpace ℝ V] in
lemma Twig.zero {p}: Twig p s 0 (0:Ten V (YForest G) r):=by simp [Twig]
omit [NormedSpace ℝ V] in
lemma Twig.cost {p}{F:Ten V (YForest G) r}(h:Twig p s A F)(he:A≤C): Twig p s C F:=⟨h.1.trans he,fun x=>(h.2 x).trans (mul_le_mul_of_nonneg_right he (by positivity))⟩
lemma Twig.μ {p}{F: Ten V (YForest G) r}(h:Twig p s A F)(c:ℝ): Twig p s (|c| *A) (c•F):= ⟨mul_nonneg (abs_nonneg _) h.1,fun x=>(norm_smul c (F x)).le.trans ((mul_le_mul_of_nonneg_left (h.2 x) (norm_nonneg c)).trans_eq (by rw [mul_assoc]; rfl))⟩
omit [NormedSpace ℝ V] in
lemma Twig.sum {ι:Type*}{p σ}{s:Finset ι}{P:ι→Ten V (YForest G) r}{M:ι→ℝ}(h:∀ i∈s,Twig p σ (M i) (P i)): Twig p σ (∑ i∈s,M i) (∑ i∈s,P i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Twig.zero
  | @insert i s e H=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))
omit [NormedSpace ℝ V] in
lemma Twig.token {p q}{F: Ten V (YForest G) r}(h:Twig p s A F)(hs:0≤s)(he:terrain.gap q p≤1): Twig q s (A*Real.exp s) F:=by
   refine ⟨mul_nonneg h.1 (by positivity),fun x=>(h.2 x).trans ?_⟩
   have hv : port_d q x ≤ port_d p x+1:= (property_le q p x).trans (Nat.add_le_add_left he _)
   rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h.1
   rw [←Real.exp_add,Real.exp_le_exp]; have ht : (port_d q x:ℝ) ≤ port_d p x+1:= by exact_mod_cast hv
   linarith only [mul_le_mul_of_nonneg_left ht hs]
lemma Twig.swirl {p}{F:Ten V (YForest G) r}(h:Twig p s A F): Twig p s A (swirl F):=by
    have he i: Twig p s A (fun x=>F (x ∘ (i:Equiv.Perm (Fin r)))):= ⟨h.1,fun x=>by rw [←port_perm p x i]; exact h.2 _⟩
    let Q:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hp:0<Q:=by unfold Q; positivity
    have ht:= (Twig.sum (s:=Finset.univ) (fun i _=>he i)).μ Q⁻¹; rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<Q⁻¹ by positivity)] at ht
    change Twig p s (Q⁻¹*(Q*A)) _ at ht; rw [inv_mul_cancel_left₀ hp.ne'] at ht; exact ht
lemma wickBill (a b:G.Color)(u:Edge Cover)(v:G.ColorIndex){P:Gen V (YForest G)}{k r:ℕ}(p:Amber terrain s C (P (r-k+1))) (h:0≤s):
    Twig u.1 s ((∑ i,‖rye (electric a b v) k i‖)* (r-k+1:ℕ)*C) (wickLamp a b u v k P r) := by
   have he:=p.1; by_cases ht:r<k; · rw [wick_pos _ _ _ _ _ ht]; exact Twig.zero.cost (by positivity)
   rw [wick_leg _ _ _ _ _ (by omega)]; apply Twig.swirl
   set c:= spark a b u v k; set B:=∑ i,‖rye (electric a b v) k i‖
   have hc : 0≤B:=Finset.sum_nonneg fun _ _=> norm_nonneg _
   refine ⟨by positivity,fun x=>?_⟩
   have hv: k+(r-k)=r:=by omega
   rw [interweave,dif_pos hv]; let y:= x ∘ Fin.cast hv; let z:= y ∘ Fin.natAdd k; let w:=y ∘ Fin.castAdd (r-k)
   change ‖c w • sever (stone u v) P (r-k) z‖≤ B*_*_*_
   by_cases hr:c w=0; · rw [show c _=0 from hr,zero_smul,norm_zero]; positivity
   have hz : port_d u.1 x ≤ port_d u.1 z:= by
       let Q : Fin (r+1)→Cover := Fin.cons u.1 (Prod.fst ∘ x); let H : Fin (r-k+1) → Cover:= Fin.cons u.1 (Prod.fst ∘ z)
       have hs (j:Fin (r+1)): ∃ i, H i=Q j:= by
          refine Fin.cases ⟨0,rfl⟩ (fun i=>?_) j
          obtain ⟨i,rfl⟩ := (finCongr hv).surjective i
          refine Fin.addCases (fun j=>?_) (fun i=>?_) i
          · exact ⟨0,(spark_here a b u v w hr j).symm⟩
          exact ⟨Fin.succ i,rfl⟩
       refine league_le terrain Q fun i j=>?_; obtain ⟨l,hl⟩:=hs i; obtain ⟨m,hm⟩:=hs j
       rw [←hl,←hm]; exact leg_le terrain H _ _
   have hg :=p.2 (Fin.cons (stone u v) z); rw [port_soar] at hg
   have hd : (port_d u.1 x : ℝ) ≤ port_d u.1 z:= Nat.cast_le.mpr hz
   have H : ‖sever (stone u v) P (r-k) z‖ ≤ ((r-k+1:ℕ):ℝ)*(C*Real.exp (-s*port_d u.1 x)):=by
      rw [sever, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (R:=ℝ),norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left hd (by linarith))) he)) (by positivity)
   rw [norm_smul]; exact (mul_le_mul (spark_bound a b u v w) H (norm_nonneg _) hc).trans_eq (by unfold B; simp only [mul_assoc])

lemma north_bill (x:Cover)(a:G.Color){P:Gen V (YForest G)}{k r:ℕ}(p:Amber terrain s C (P (r-k+1)))(hs:0≤s):
    Twig x s (∑ _ :Axis,∑ i:G.ColorIndex, ((∑ j, ‖rye (electric a 0 i) k j‖)*(r-k+1:ℕ) * C + ((∑ j,‖rye (electric 0 a i) k j‖)*(r-k+1:ℕ)*C)*Real.exp s)) (northL k x a P r):=by
    unfold northL; simp_rw [Finset.sum_apply,Pi.add_apply]; apply Twig.sum; intro j _; apply Twig.sum; intro i _; refine (wickBill a 0 (x,j) i p hs).add ((wickBill 0 a (x-step j,j) i p hs).token hs ?_)
    change size (x-step j-x)≤1; rw [show x-step j-x= -step j by abel,size_neg]; simp [size,apply_ite Int.natAbs]
end
section
variable [NormedAddCommGroup V][NormedSpace ℝ V]

def Draft {r:ℕ}(P: Ten V (YForest G) (r+1))(σ C : ℝ): Prop := 0≤C ∧ ∀ x j,Twig x σ C (windsL x j P)
lemma floatT (P:Gen V (YForest G))(a b:G.Color)(x:Edge Cover)(k i)(Q): wickLamp a b x i k (P-Q)=wickLamp a b x i k P-wickLamp a b x i k Q:= by
   ext1 r; by_cases h:k≤r; swap; · simp_rw [Pi.sub_apply, wick_pos (r:=r) _ _ _ _ _ (show r<k by omega), sub_zero]
   rw [Pi.sub_apply]; simp_rw [wick_leg _ _ _ _ _ h]; unfold Blue.swirl
   simp_rw [← smul_sub, ← Finset.sum_sub_distrib]; apply congr_arg (fun z:Ten V (YForest G) r=> ((Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹) • z); exact Finset.sum_congr rfl (fun s _=>funext fun y=> by simp [interweave,sever,prune, Pi.smul_apply,smul_sub, show k+(r-k)=r by omega])
lemma vertical_pair {P Q:Pal V (YForest G)}(h:vertical P)(q:vertical Q): vertical (P-Q):=by
   intro b x k; rw [show (0:Gen V (YForest G))=(∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k,(wickLamp b 0 (x,v) j z.1 (P z.2)+wickLamp 0 b (x-step v,v) j z.1 (P z.2)))- (∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k,(wickLamp b 0 (x,v) j z.1 (Q z.2)+wickLamp 0 b (x-step v,v) j z.1 (Q z.2))) from ?_];
   swap; · rw [h,q]; simp
   simp_rw [← Finset.sum_sub_distrib,Pi.sub_apply,floatT]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; abel

-- sum construct coefficient depends only on V-independent sizes.
def postWind (b:G.Color)(σ C:ℝ)(r k:ℕ):= ∑ _ :Axis,∑ i:G.ColorIndex, ((∑ j, ‖rye (electric b 0 i) k j‖)*(r-k+1:ℕ) * C + ((∑ j,‖rye (electric 0 b i) k j‖)*(r-k+1:ℕ)*C)*Real.exp σ)
def levyWind (G:Gauge)(σ:ℝ)(e r:ℕ):= ∑ i:G.ColorIndex, ((r+1:ℕ):ℝ)⁻¹ * ∑ j∈(Finset.antidiagonal e).erase (0,e), postWind (coatC G (Pi.single i 1)) σ 1 r j.1
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in lemma levyWind_nn (G:Gauge)(σ:ℝ)(e r:ℕ): 0≤ levyWind G σ e r:= by unfold levyWind postWind; positivity
lemma draft_due {P:Pal V (YForest G)}(h:vertical P)(p:∀ i,Pure (P i))(hr:∀ i<e,∀ j≤r+1,Amber terrain s C (P i j))(he:0≤s)(hc:0≤C): Draft (P e (r+1)) s (levyWind G s e r*C):=by
    set S:= (Finset.antidiagonal e).erase (0,e); let b (i:G.ColorIndex) := coatC G (Pi.single i 1)
    set D := levyWind G s e r *C; let M (i:G.ColorIndex):= ∑ j∈ S,postWind (b i) s C r j.1
    have ht : 0<((r+1:ℕ):ℝ):=by positivity
    let L:= ((r+1:ℕ):ℝ)⁻¹
    have hz j k : postWind (b j) s 1 r k*C= postWind (b j) s C r k:=by
      unfold postWind; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i hi=>?_
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=> by ring
    have he' : D=∑ i:G.ColorIndex,L*M i :=by unfold D levyWind; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [mul_assoc,Finset.sum_mul]; congr 1; exact Finset.sum_congr rfl fun k _=> hz i k.1
    refine ⟨mul_nonneg (levyWind_nn ..) hc,?_⟩; intro x i
    set T:= P e (r+1); set a:= b i
    have hb : Twig x s (M i) ((∑ j∈S,northL j.1 x a (P j.2)) r):=by
        rw [Finset.sum_apply]; apply Twig.sum; intro j hj; obtain ⟨hu,hv⟩:= Finset.mem_erase.mp hj; have ht:= Finset.mem_antidiagonal.mp hv
        have hq : j.1≠0:= fun h=> hu (Prod.ext h (show j.2=e from by omega))
        exact north_bill x a (hr _ (by omega) _ (by omega)) he
    have H : windsL x i (P e (r+1)) = -L • (∑ j∈ S,northL j.1 x a (P j.2)) r:= by
        have he:= essence h p x i e r
        rw [← Nat.cast_smul_eq_nsmul (R:=ℝ)] at he
        rw [neg_smul, ← smul_neg, ←he, smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
    rw [H]; have hp:= hb.μ (-L); rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr ht.le)] at hp
    apply hp.cost; rw [he']; apply Finset.single_le_sum _ (Finset.mem_univ i); intro b _; apply mul_nonneg (by positivity); unfold M postWind; positivity
end
end YM.WilsonCoeffUV.Bank
