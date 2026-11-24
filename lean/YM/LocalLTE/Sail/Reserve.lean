import YM.LocalLTE.XPhase.Store
import YM.LocalLTE.XPhase.Closure
import YM.LocalLTE.Concert.Contact
import YM.MergeProof.Bungalow
/-!
# A zero exponent-loss version of branch(), for finite-region letters

There is no exponent reserve for the actual K input on the summit. Use contact
instead. Estimates an entire box-scale sum, not the projection at output. (At
other knots the exponent loss version ok, no finite-support premise there.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Extra.Trajectories Progress.DirectedRecipe MergeProof Accent Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type*} [DecidableEq V] {B:Census V} {G:Gauge}{n:Side} {R:BudgetPoint}
variable (K:Box n → Config G n→Poly B)(u : J→ Config G n→Poly B) (X:J→Support n)
variable {t:ℝ} (W:Finset J)
/-- Connected and disjoint X and K at any point. A **payable** left hits a letter region
or the request pin. Not using any K outside such finite volume. -/
lemma stock_hits (p:Period X) {z:Box n}(hz:z∈p.val.toLeft)(x:Site n)
    (hp:p.val.toRight⊆ W) (hx:x∈(forst X p).1): ¬Disjoint z.1 (insert x (W.biUnion X)):=by
    intro ht
    obtain ⟨e,he,hX⟩:= mem_biUnion.mp hx
    have hu:= p.property.spark.2 (.inl z) (mem_toLeft.mp hz) e he
    have hh i (hi:Relation.ReflTransGen (Ac.bonds (bloom X) p.val) (.inl z) i): i= Sum.inl z:=by
       induction hi with
       | refl=> rfl
       | @tail a j h h' IH=>
          subst a; obtain ⟨-,ha,y,hy,hY⟩:= h'; cases j
          next j=>
             by_contra h; exact Finset.disjoint_left.mp (p.property.neat hz (mem_toLeft.mpr ha) (fun h'=> h (h' ▸ rfl))) hy hY -- h shadow
          next j=> exact (Finset.disjoint_left.mp ht hy (mem_insert_of_mem (mem_biUnion.mpr ⟨j,hp (mem_toRight.mpr ha),hY⟩))).elim -- implicit? edit
    obtain rfl:= (hh e hu).symm -- need subst
    exact Finset.disjoint_left.mp ht hX (mem_insert_self ..)

variable [Fintype J][Fintype V]
variable {o:V→ Site n} (d:J→ℝ) (w:V→ℝ) (P:BudgetPoint) {C:ℝ}
variable (hp:Towed w Prod.fst K P.B P.supportExponent C)(hx: ∀ i,0<w i)
    (h:∀ i,Loci w (u i) (d i)) (hu:∀ i,d i ≠0→ i∈ W)
include hp hx h hu
lemma branch_localized : Towed w Prod.fst (Accent.closure K u X t) P.B P.supportExponent
      ((Real.exp (((W.biUnion X).card+1:ℝ)*C)-1) * ∏ i:J,(1+P.mass (X i) (d i))):=by
   apply Accent.towing (forst X) _ ?_ hx
   obtain ⟨a,ha,hA,hq⟩:=hp
   let g(i : FlowKind J n):= i.elim a d; have hv i : Loci w (pork K u i) (g i):= by cases i; exact hq _; exact h _
   have hG i : 0 ≤ g i:= (hv i|>.fares hx).1
   choose S hS hU hF using hv
   let e(p:Period X):= ∏ j∈p.val,g j
   refine ⟨e,Summable.of_finite,fun x=>?_,fun p=>?_⟩
   · let loc:= insert x (W.biUnion X); let f(j:Box n):= if ¬Disjoint j.1 loc then P.mass j.1 (a j) else 0
     have hf :SumBudget f ((↑(W.biUnion X).card +1:ℝ)*C):=by
        let A (y:Site n)(j:Box n):=if y∈ j.1 then a j*Real.exp (P.supportExponent * coverNumber P.B j.1) else 0
        have he:C≥0:= (tsum_nonneg (hA x).1).trans (hA x).2.2
        let Q:=(W.biUnion X)
        have h' : SumBudget (fun j=>∑ i∈loc,A i j) (loc.card*C):=by
           have hp:= budget_over loc A (fun _=>C) (fun y _=> hA y); simpa only [Finset.sum_const,nsmul_eq_mul] using hp
        refine Extra.Multi.Budget.mono h' (fun i=>?_) (fun j=>?_) (mul_le_mul_of_nonneg_right (show (loc.card:ℝ)≤ ↑(W.biUnion X).card+1 from by exact_mod_cast Finset.card_insert_le x (W.biUnion X)) he) -- math name
        · unfold f; split; exact mul_nonneg (Real.exp_nonneg _) (hG (.inl i)); rfl
        unfold f;split
        next h=> obtain ⟨y,hx,hp⟩:=not_disjoint_iff.mp h; exact le_trans (show _ ≤ A y j from ((if_pos hx).trans (mul_comm ..)).symm.le) (Finset.single_le_sum (f:=fun i=>A i j) (fun i _=> (hA i).1 j) hp)
        exact h'.1 _
     have he' : SumBudget (fun s:Finset (Box n)=> (∏ i∈s,f i)- ∏ _∈s, (0:ℝ)) (Real.exp (((W.biUnion X).card+1:ℝ)*C)-1):=by
        refine ⟨fun i=>?_,Summable.of_finite,?_⟩
        · exact sub_nonneg.mpr (Finset.prod_le_prod (fun _ _=> le_rfl) (fun i _=> hf.1 i))
        have h0:(∑ i:Finset (Box n),∏ _∈i, (0:ℝ))=1:=by
           rw [Finset.sum_eq_single ∅,Finset.prod_empty]; swap; · simp
           intro i _ hi; obtain ⟨k,hk⟩:= Finset.nonempty_iff_ne_empty.mpr hi; exact Finset.prod_eq_zero hk rfl
        rw [tsum_fintype,Finset.sum_sub_distrib,h0,sub_le_sub_iff_right,← Finset.powerset_univ,← Finset.prod_one_add]; apply le_trans (Finset.prod_le_prod (g:=fun i:Box n=>Real.exp (f i)) (fun i _=> add_nonneg zero_le_one (hf.1 i)) fun i _=> by rw [add_comm];exact Real.add_one_le_exp _) _; rw [← Real.exp_sum]; exact Real.exp_le_exp.mpr ((tsum_fintype _).symm.trans_le hf.2.2)
     have hM(i:J): 0 ≤ P.mass (X i) (d i):= mul_nonneg (Real.exp_nonneg _) (hG (.inr i))
     have hh : SumBudget (fun s:Finset J=> ∏ i∈s,P.mass (X i) (d i)) (∏ i:J,(1+P.mass (X i) (d i))):=by
        refine ⟨fun i=>Finset.prod_nonneg fun j _=> hM j,Summable.of_finite,?_⟩
        rw [tsum_fintype,Finset.prod_one_add,Finset.powerset_univ]
     let j(p:Period X):= Finset.sumEquiv p.val
     have hv:= budget_pull j (show Injective j from Finset.sumEquiv.injective.comp Subtype.val_injective) (budget_prod he' hh)
     refine budget_mono hv (fun i=> ?_) (fun p=>?_)
     · split
       next=> exact mul_nonneg (Finset.prod_nonneg fun j _=>hG j) (Real.exp_nonneg _)
       rfl
     by_cases h':e p=0
     · split; rw [h',zero_mul];exact hv.1 p; exact hv.1 p
     split; next H=>
        have ht(i)(hi:i∈p.val.toLeft):f i=P.mass i.1 (a i):= if_pos (stock_hits X W p hi x (fun i hi=> hu i (fun h=> h' (Finset.prod_eq_zero (Finset.mem_toRight.mp hi) (show g (.inr i)=0 from h)))) H)
        obtain ⟨k,hk⟩:=p.property.life
        change (∏ i∈p.val,g i)* _ ≤ ((∏ i∈p.val.toLeft,f i) -∏ _∈p.val.toLeft, (0:ℝ))*(∏ i∈p.val.toRight,P.mass (X i) (d i))
        rw [Finset.prod_eq_zero (f:=fun _=>0) hk (show (0:ℝ)=0 from rfl),sub_zero,Finset.prod_congr (s₂:=p.val.toLeft) (f:=f) rfl ht, ← show ∏ i∈p.val,P.mass (bloom X i) (g i)=(∏ i∈p.val.toLeft,P.mass i.1 (a i))*(∏ i∈p.val.toRight,P.mass (X i) (d i)) from Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight ..]
        simp only [BudgetPoint.mass, Finset.prod_mul_distrib,← Real.exp_sum,← mul_sum,mul_comm (∏ i∈p.val,g i)]
        apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=> hG i)
        rw [Real.exp_le_exp]; apply mul_le_mul_of_nonneg_left _ (P.exponent_pos.le)
        exact_mod_cast Ac.cover (bloom X) P.B p.property.spark
     exact hv.1 p
   obtain ⟨q,hq,he,hW⟩:= all_prices p.val S g (fun x l=>pork K u l x) w hx hS hF (fun x i=>hU i x); refine ⟨q,hq,fun U j=>?_,he⟩
   unfold crow;dsimp only;split;exact hW U j;simpa using hq j
end YM.LocalLTE.Sail
