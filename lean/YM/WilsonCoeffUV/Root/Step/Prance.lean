import YM.WilsonCoeffUV.Root.Step.Vertical
/-! # True single mark's wind lease. Both receipts root w.r.t SAME origin incl x. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Wilson Tree Power PowerSeries
open Precision Exterior Soil
open scoped Topology BigOperators
variable {n c L : Side}{α β V:Type*} {p q e k r:ℕ}{G:Gauge}{A B C D s t : ℝ}
-- Cork same α cause.
lemma stance_eq (o:Cover)(b:YForest G)(x:dock Cover (Hooks G) r): tread terrain o (Fin.cons b x) = league terrain (Fin.cons o (stud b.1 x)):=by unfold tread stud; rw [←comps_head]
def stance (o x:Cover)(y:dock Cover (Hooks G) r):= league terrain (Fin.cons o (stud x y))
lemma fee_stance (o x z:Cover)(y:dock Cover (Hooks G) r): stance o x y≤stance o z y + terrain.gap x z:=by
    let u : Fin (r+2)→Cover:= Fin.cons o (stud x y); let w: Fin (r+2)→Cover:= Fin.cons o (stud z y); let j: Fin (r+2):= Fin.succ 0
    have he (i) (h:i≠j): u i=w i:= by
       revert h; refine Fin.cases (fun _=> rfl) (fun k=>?_) i
       refine Fin.cases (fun h=> (h rfl).elim) (fun k h=> by simp [u,w,stud]) k
    have hv i (hi:i≠j) : terrain.gap (u j) (u i)≤stance o z y+terrain.gap x z:= by rw [he i hi]; apply (terrain.tri _ (w j) _).trans; rw [add_comm]; exact Nat.add_le_add_right (leg_le terrain w j i) _
    apply league_le terrain u; intro i k
    by_cases h:i=j
    · subst i; by_cases a:k=j; · subst k; simp only [terrain.self]; omega
      exact hv k a
    by_cases a:k=j; · subst k; rw [terrain.swap]; exact hv i h
    rw [he i h,he k a]; exact (leg_le terrain w i k).trans (Nat.le_add_right ..)
lemma pace_perm (o x:Cover)(y:dock Cover (Hooks G) r)(v:Equiv.Perm (Fin r)): stance o x (y ∘ v)=stance o x y:=by
    let A (r:ℕ)(v:Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)):= ((finSuccEquiv r).trans (Equiv.optionCongr v)).trans (finSuccEquiv r).symm
    let p: Fin (r+2)→Cover:= Fin.cons o (stud x y); let T:= A _ (A _ v); unfold stance
    rw [← league_equiv terrain p T]; congr 1; funext i
    have he r (v:Equiv.Perm (Fin r)): A r v 0=0:= by simp [A]
    have ht r (v:Equiv.Perm (Fin r)) (x: Fin r) : A r v x.succ=(v x).succ:= by simp [A]
    refine Fin.cases (by rw [Function.comp_apply,show T 0=0 from he ..]; rfl) (fun j=>?_) i
    unfold T; rw [Function.comp_apply,ht]; refine Fin.cases (by rw [he]; rfl) (fun u=>by rw [ht]; simp [p,stud]) j

variable [NormedAddCommGroup V]
def Prance (o x:Cover) (s A:ℝ)(P:Ten V (YForest G) r): Prop:=0≤A∧∀ y,‖P y‖≤A*Real.exp (-s*stance o x y)
variable {o x:Cover}
lemma Prance.zero : Prance o x s 0 (0:Ten V (YForest G) r):=by simp [Prance]
lemma Prance.add {P Q:Ten V (YForest G) r}(p:Prance o x s A P)(q:Prance o x s B Q): Prance o x s (A+B) (P+Q):=⟨add_nonneg p.1 q.1,fun y=> (norm_add_le ..).trans ((add_le_add (p.2 y) (q.2 y)).trans_eq (by ring))⟩
lemma Prance.le {P:Ten V (YForest G) r}(h:Prance o x s A P)(p:A≤B): Prance o x s B P:=⟨h.1.trans p,fun y=>(h.2 y).trans (mul_le_mul_of_nonneg_right p (by positivity))⟩
lemma Prance.μ [NormedSpace ℝ V]{P:Ten V (YForest G) r}(h:Prance o x s A P)(b:ℝ): Prance o x s (|b| *A) (b•P):=⟨mul_nonneg (abs_nonneg _) h.1,fun y=>(norm_smul b (P y)).le.trans ((mul_le_mul_of_nonneg_left (h.2 y) (norm_nonneg _)).trans_eq (by rw [mul_assoc]; rfl))⟩
lemma Prance.sum {S:Finset α}{P:α→Ten V (YForest G) r}{M:α→ℝ}(h:∀ i∈S,Prance o x s (M i) (P i)): Prance o x s (∑ i∈S,M i) (∑ i∈S,P i):=by
    classical
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact Prance.zero
    | @insert a b e H=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (h a (Finset.mem_insert_self ..)).add (H fun i hi=> h i (Finset.mem_insert_of_mem hi))
lemma Prance.token {y:Cover}{P:Ten V (YForest G) r}(h:Prance o x s A P)(hs:0≤s)(he:terrain.gap y x≤1): Prance o y s (A*Real.exp s) P:=by
   refine ⟨mul_nonneg h.1 (by positivity),fun z=>(h.2 z).trans ?_⟩
   have hv : stance o y z≤stance o x z+1:= (fee_stance o y x z).trans (Nat.add_le_add_left he _)
   rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h.1
   rw [←Real.exp_add,Real.exp_le_exp]; have ht : (stance o y z:ℝ) ≤ stance o x z+1:= by exact_mod_cast hv
   linarith only [mul_le_mul_of_nonneg_left ht hs]
lemma Prance.rotation [NormedSpace ℝ V] {P:Ten V (YForest G) r}(h:Prance o x s A P): Prance o x s A (swirl P):=by
    have he i: Prance o x s A (fun y=>P (y ∘ (i:Equiv.Perm (Fin r)))):= ⟨h.1,fun y=>by rw [←pace_perm o x y i]; exact h.2 _⟩
    let Q:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hp:0<Q:=by unfold Q; positivity
    have ht:= (Prance.sum (S:=Finset.univ) (fun i _=>he i)).μ Q⁻¹; rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<Q⁻¹ by positivity)] at ht
    change Prance o x s (Q⁻¹*(Q*A)) _ at ht; rw [inv_mul_cancel_left₀ hp.ne'] at ht; exact ht

variable [NormedSpace ℝ V]
def roaring (o:Cover)(F:Ten V (YForest G) (r+1))(s C:ℝ): Prop := 0≤C ∧ ∀ x j,Prance o x s C (windsL x j F)
lemma prance_wick (a b:G.Color)(u:Edge Cover)(v:G.ColorIndex){P:Gen V (YForest G)}{k r:ℕ}(p:Cork terrain o s C (P (r-k+1))) (h:0≤s):
    Prance o u.1 s ((∑ i,‖rye (electric a b v) k i‖)* (r-k+1:ℕ)*C) (wickLamp a b u v k P r) := by
   have he:=p.1; by_cases ht:r<k; · rw [wick_pos _ _ _ _ _ ht]; exact Prance.zero.le (by positivity)
   rw [wick_leg _ _ _ _ _ (by omega)]; apply Prance.rotation
   set c:= spark a b u v k; set B:=∑ i,‖rye (electric a b v) k i‖
   have hc : 0≤B:=Finset.sum_nonneg fun _ _=> norm_nonneg _
   refine ⟨by positivity,fun x=>?_⟩
   have hv: k+(r-k)=r:=by omega
   rw [interweave,dif_pos hv]; let y:= x ∘ Fin.cast hv; let z:= y ∘ Fin.natAdd k; let w:=y ∘ Fin.castAdd (r-k)
   change ‖c w • sever (stone u v) P (r-k) z‖≤ B*_*_*_
   by_cases hr:c w=0; · rw [show c _=0 from hr,zero_smul,norm_zero]; positivity
   have hz : stance o u.1 x ≤ stance o u.1 z:= by
       let K (r:ℕ)(x:dock Cover (Hooks G) r): Fin (r+2)→Cover:= Fin.cons o (stud u.1 x); let Q:=K r x; let H:=K (r-k) z
       have hs (j:Fin (r+2)): ∃ i, H i=Q j:= by
          refine Fin.cases ⟨0,rfl⟩ (fun i=>?_) j; refine Fin.cases ⟨Fin.succ 0,rfl⟩ (fun i=>?_) i
          obtain ⟨i,rfl⟩ := (finCongr hv).surjective i
          refine Fin.addCases (fun j=>?_) (fun i=>?_) i
          · exact ⟨Fin.succ 0,(spark_here a b u v w hr j).symm⟩
          exact ⟨Fin.succ (Fin.succ i),rfl⟩
       refine league_le terrain Q fun i j=>?_; obtain ⟨l,hl⟩:=hs i; obtain ⟨m,hm⟩:=hs j
       rw [←hl,←hm]; exact leg_le terrain H _ _
   have hg :=p.2 (Fin.cons (stone u v) z); rw [stance_eq] at hg
   have hd : (stance o u.1 x : ℝ) ≤ stance o u.1 z:= Nat.cast_le.mpr hz
   have H : ‖sever (stone u v) P (r-k) z‖ ≤ ((r-k+1:ℕ):ℝ)*(C*Real.exp (-s*stance o u.1 x)):=by
      rw [sever, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (R:=ℝ),norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left hd (by linarith))) he)) (by positivity)
   rw [norm_smul]; exact (mul_le_mul (spark_bound a b u v w) H (norm_nonneg _) hc).trans_eq (by unfold B; simp only [mul_assoc])
lemma north_roar (x:Cover)(a:G.Color){P:Gen V (YForest G)}{k r:ℕ}(p:Cork terrain o s C (P (r-k+1)))(hs:0≤s):
    Prance o x s (postWind a s C r k) (northL k x a P r):=by
    unfold northL; simp_rw [Finset.sum_apply,Pi.add_apply]; apply Prance.sum; intro j _; apply Prance.sum; intro i _; refine (prance_wick a 0 (x,j) i p hs).add ((prance_wick 0 a (x-step j,j) i p hs).token hs ?_)
    change size (x-step j-x)≤1; rw [show x-step j-x= -step j by abel,size_neg]; simp [size,apply_ite Int.natAbs]
lemma roar_le_levy {P:Pal V (YForest G)}(h:vertical P)(p:∀ i,Pure (P i))(hr:∀ i<e,∀ j≤r+1,Cork terrain o s C (P i j))(he:0≤s)(hc:0≤C): roaring o (P e (r+1)) s (levyWind G s e r*C):=by
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
    have hb : Prance o x s (M i) ((∑ j∈S,northL j.1 x a (P j.2)) r):=by
        rw [Finset.sum_apply]; apply Prance.sum; intro j hj; obtain ⟨hu,hv⟩:= Finset.mem_erase.mp hj; have ht:= Finset.mem_antidiagonal.mp hv
        have hq : j.1≠0:= fun h=> hu (Prod.ext h (show j.2=e from by omega))
        exact north_roar x a (hr _ (by omega) _ (by omega)) he
    have H : windsL x i (P e (r+1)) = -L • (∑ j∈ S,northL j.1 x a (P j.2)) r:= by
        have he:= essence h p x i e r
        rw [← Nat.cast_smul_eq_nsmul (R:=ℝ)] at he
        rw [neg_smul, ← smul_neg, ←he, smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
    rw [H]; have hp:= hb.μ (-L); rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr ht.le)] at hp
    apply hp.le; rw [he']; apply Finset.single_le_sum _ (Finset.mem_univ i); intro b _; apply mul_nonneg (by positivity); unfold M postWind; positivity

omit [NormedSpace ℝ V] in
lemma ledger_stencil {P:Ten V (YForest G) (r+1)}(h: roaring o P s A)(i): Cork terrain o s A (ledger P i):=by
   refine ⟨h.1,fun x=>?_⟩; unfold ledger; split; swap; · rw [norm_zero]; exact mul_nonneg h.1 (by positivity)
   refine ((h.2 ..).2 (aside i x)).trans_eq ?_; congr 3
   rw [show stance o (x i).1 _=tread terrain o (enlist i (x i) (aside i x)) from ?_, leaves]
   unfold enlist; change _ = port_d o _; rw [port_perm]; rw [← show tread terrain o _= port_d o (Fin.cons (x i) (aside i x)) from rfl]; exact (stance_eq ..).symm
end YM.WilsonCoeffUV.Bank
