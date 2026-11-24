import YM.WilsonCoeffUV.Wick.Stamps
/-!
# Native polynomial position moment cost

An ℓ1, including the root; θ allows keeping all ranks through joining
scale-relative center weights without charging block-dependent apertures.
It does NOT include exponential weights on test addresses.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Soil
open scoped Topology BigOperators
variable {n:Side}{U α β V W ι : Type*}{k r u j:ℕ} {A B σ η : ℝ}

lemma subfinance {f:ι→ℝ}(p:SumBudget f A)(h:A≤ B):SumBudget f B:=⟨p.1,p.2.1,p.2.2.trans h⟩
lemma finance_add {f g:ι → ℝ}(p:SumBudget f A)(q:SumBudget g B): SumBudget (fun i=>f i+g i) (A+B) :=⟨fun _=> add_nonneg (p.1 _) (q.1 _),p.2.1.add q.2.1,(p.2.1.tsum_add q.2.1).trans_le (add_le_add p.2.2 q.2.2)⟩
lemma finance_glob {f:ι→α→ℝ}{g:ι→ℝ}(p:∀ i,SumBudget (f i) (g i))(q:SumBudget g A): SumBudget (fun i:ι×α=>f i.1 i.2) A:=by
   let h (i:ι×α):= f i.1 i.2; have hp (i:ι×α):0≤ h i:= (p _).1 _
   have ht:= budget_minor q (fun i=>tsum_nonneg fun a=>hp (i,a)) (fun i=>(p i).2.2)
   have H: Summable h := (summable_prod_of_nonneg hp).mpr ⟨fun i=>(p i).2.1,ht.2.1⟩
   refine ⟨hp,H,H.tsum_prod.trans_le ht.2.2⟩
lemma finance_port {f:ι×α→ℝ}(p:SumBudget f A): SumBudget (fun i=>∑' a,f (i,a)) A:=⟨fun i=> tsum_nonneg fun a=>p.1 (i,a),((summable_prod_of_nonneg p.1).mp p.2.1).2,p.2.1.tsum_prod.symm.trans_le p.2.2⟩
lemma finance_flip {f:ι×α→ℝ}(p:SumBudget f A): SumBudget (fun i:α×ι=> f (i.2,i.1)) A:= cap_walk _ _ (Equiv.prodComm ..) (fun _=>rfl) p
lemma each_finance {f: (i:Fin k)→α→ℝ}{A: Fin k→ℝ}(p:∀ i,SumBudget (f i) (A i)): SumBudget (fun x: Fin k→α=>∏ i, f i (x i)) (∏ i,A i):=by
   induction k with
   | zero=> simpa using (series_bill (A:=0) (f:=fun _:α=> (0:ℝ)) (by simp [SumBudget]) 0)
   | succ k ih=> rw [Fin.prod_univ_succ]; exact cap_walk _ _ (Fin.consEquiv (fun _:Fin (k+1)=> α)) (fun x=> by rw [Fin.prod_univ_succ]; simp) (prod_cap (p 0) (Finset.prod_nonneg fun i _=> cap_nn (p i.succ)) (fun _=> ih (fun i=> p i.succ)))
-- weighted bud, also useful where rank pinned before root
section
variable [NormedAddCommGroup V]

def Award {I:Type*}(P:I→V)(s:I→ℝ)(A:ℝ): Prop:= SumBudget (fun i=>s i * ‖P i‖) A
variable {I:Type*}{s t:I→ℝ}{P Q:I → V}
lemma Award.C (p:Award P s A):0≤A:= cap_nn p
lemma Award.zero : Award (0:I→V) s 0:=by simp [Award,SumBudget]
lemma Award.more (p:Award P s A)(h:A≤ B):Award P s B:= subfinance p h
lemma Award.less (p:Award P s A)(h:t≤ s)(ht:0≤ t):Award P t A:= budget_minor p (fun i=>mul_nonneg (ht i) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_right (h i) (norm_nonneg _))
lemma Award.plus (p:Award P s A)(q:Award Q s B)(h:0≤s): Award (P+Q) s (A+B):= budget_minor (finance_add p q) (fun i=>mul_nonneg (h i) (norm_nonneg _)) (fun i=>by rw [Pi.add_apply]; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (h i)).trans_eq (mul_add ..))
lemma Award.minus (p:Award P s A): Award (-P) s A:= by unfold Award; simp_rw [Pi.neg_apply,norm_neg]; exact p
lemma Award.diff (p:Award P s A)(q:Award Q s B)(h:0 ≤ s):Award (P-Q) s (A+B):=by rw [sub_eq_add_neg]; exact p.plus q.minus h
lemma Award.μ [NormedSpace ℝ V](p: Award P s A)(c:ℝ): Award (c•P) s (|c| *A):=by unfold Award; simp_rw [Pi.smul_apply,norm_smul, mul_left_comm _ ‖c‖]; exact cap_scale p (abs_nonneg _)
lemma Award.sum {S:Finset ι}{P:ι→I→V}{w:ι→ℝ}(p:∀ i∈S,Award (P i) s (w i))(h:0≤s): Award (∑ i∈S,P i) s (∑ i∈S,w i):=by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Award.zero
  | @insert i S e ih=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (p i (Finset.mem_insert_self ..)).plus (ih fun j hj=> p j (Finset.mem_insert_of_mem hj)) h
lemma Award.cell {f:I→α→V}(p: Award (fun i:I×α=>f i.1 i.2) (s ∘ Prod.fst) A)(h:1≤s): Award (fun i=> ∑' a,f i a) s A:=by
   apply budget_minor (finance_port p) (fun i=>mul_nonneg (zero_le_one.trans (h i)) (norm_nonneg _)); intro i
   simp_rw [Function.comp_apply, tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (h i)); apply norm_tsum_le_tsum_norm
   have he (a):‖f i a‖≤ (s i)*‖f i a‖ := le_mul_of_one_le_left (norm_nonneg _) (h _)
   exact (((summable_prod_of_nonneg p.1).mp p.2.1).1 i).of_nonneg_of_le (fun _=>norm_nonneg _) he
lemma Award.pass {f:I→α→V}{t:α→ℝ}{g:I→ℝ}(p:∀ i,Award (f i) t (g i))(q:SumBudget g A)(hx:1≤t) : Award (fun a=>∑' i,f i a) t A:= by
   have he:= finance_flip (finance_glob p q)
   exact Award.cell (f:=fun i a=> f a i) he hx
lemma Award.pivot {Q: U→V}{t:U→ℝ}(p: Award Q t A)(q:I≃U)(h:Q ∘ q=P)(v:t ∘ q=s): Award P s A:=by rw [← h,← v]; apply cap_walk _ _ q.symm ?_ p; intro i; simp
lemma Award.touch [NormedAddCommGroup W][NormedSpace ℝ W][NormedSpace ℝ V] (F:V→L[ℝ] W)(p:Award P s A)(h:0≤s): Award (F ∘ P) s (‖F‖*A):= budget_minor (cap_scale p (norm_nonneg F)) (fun i=>mul_nonneg (h _) (norm_nonneg _)) (fun i=> (mul_le_mul_of_nonneg_left (F.le_opNorm (P i)) (h i)).trans_eq (by ring))
lemma Award.sumnorm (p: Award P s A)(h:1≤s): Summable fun i=>‖P i‖:= p.2.1.of_nonneg_of_le (fun _=>norm_nonneg _) fun i=> le_mul_of_one_le_left (norm_nonneg _) (h i)
end

def autumn (η:ℝ)(i:ℕ)(a:ℕ):ℝ:= (1+η*a)^i
lemma autumn_pos (h:0≤η) (i a):1≤autumn η i a:= one_le_pow₀ (le_add_of_nonneg_right (by positivity))
lemma autumn_mono (h:0≤η)(i:ℕ) : Monotone (autumn η i) := fun a b hx=>by unfold autumn; gcongr
lemma autumn_tax (h:0≤η)(a b i:ℕ) : autumn η i (a+b)≤ autumn η i a*autumn η i b:=by unfold autumn; rw [← mul_pow]; gcongr; push_cast; nlinarith only [show 0≤ (η*(a:ℝ))*(η*(b:ℝ)) by positivity]
lemma autumn_shrink (h:0≤η)(hs:η≤σ)(i a:ℕ) : autumn η i a≤autumn σ i a:=by unfold autumn; gcongr

abbrev hedge (p:Cover)(η:ℝ)(i:ℕ)(x:dock Cover α r):ℝ:= autumn η i (tread Bank.terrain p x)
def Fruit [NormedAddCommGroup V](o:Cover)(η:ℝ)(u:ℕ)(P:Ten V (Cloth α) r)(A:ℝ): Prop:= Award P (hedge o η u) A
lemma hedge_nn {o:Cover}(p:0≤η): (0:dock Cover α r→ℝ)≤ hedge o η u:= fun _=> zero_le_one.trans (autumn_pos p ..)

variable [NormedAddCommGroup V]{o:Cover} {P Q:Ten V (Cloth α) r}

lemma Fruit.C (p:Fruit o η u P A) : 0≤A:= Award.C p
lemma Fruit.zero : Fruit o η u (0:Ten V (Cloth α) r) 0:= Award.zero
lemma Fruit.more (p:Fruit o η u P A)(h:A≤B): Fruit o η u P B:= Award.more p h
lemma Fruit.shave (p:Fruit o η u P A) (h:0≤σ)(v:σ≤η): Fruit o σ u P A:= Award.less p (fun _=> autumn_shrink h v ..) (hedge_nn h)
lemma Fruit.slice (p:Fruit o η u P A) (h:0≤η)(v:j≤u): Fruit o η j P A:= Award.less p (fun _=>pow_le_pow_right₀ (show 1≤1+η*(_ :ℝ) from le_add_of_nonneg_right (by positivity)) v) (hedge_nn h)
lemma Fruit.plus(p:Fruit o η u P A)(q:Fruit o η u Q B)(h:0≤η): Fruit o η u (P+Q) (A+B):= Award.plus p q (hedge_nn h)
lemma Fruit.diff(p:Fruit o η u P A)(q:Fruit o η u Q B)(h:0≤η): Fruit o η u (P-Q) (A+B):= Award.diff p q (hedge_nn h)
lemma Fruit.sum {S:Finset ι}{P:ι→Ten V (Cloth α) r}{w:ι→ℝ}(p:∀ i∈S,Fruit o η u (P i) (w i))(h:0≤η): Fruit o η u (∑ i∈S,P i) (∑ i∈S,w i):= Award.sum p (hedge_nn h)
variable [NormedSpace ℝ V]
lemma Fruit.μ (p:Fruit o η u P A)(c:ℝ): Fruit o η u (c•P) (|c| * A):= Award.μ p c
lemma Fruit.touch [NormedAddCommGroup W][NormedSpace ℝ W](F:V→L[ℝ] W)(p:Fruit o η u P A)(h:0≤η): Fruit o η u (F ∘ P) (‖F‖* A):= Award.touch F p (hedge_nn h)
end YM.WilsonCoeffUV.Shard
