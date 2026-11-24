import YM.WilsonCoeffUV.Root.Step.Prance
/-!
# Single price for the transmission proof. Coarse packing in Wick.
Here postWind uses same packed ribbon restricted to rooted word.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Wilson Tree Power PowerSeries
open Precision Exterior Soil
open scoped Topology BigOperators
variable {n c L : Side}{α β V:Type*} {p q e k r:ℕ}{G:Gauge}{A B C D s t η: ℝ}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

-- Owning/spun functions of own position only.
def usher (L:Side)(g:ropes Cover (Co L α) β)(i:Fin r): Roof α β r:= owns L g i
lemma brush_spunk (M: Fin r→ ropes Cover (Co L α) β)(P:Ten V (Cloth α) r): spunk L P (fun i=> owns L (M i) i)=ribbon M (turnTen (panel L α).symm P):=by
    funext x y
    change (∏ i,spring L (M i) ((panel L α ∘ y) i) (x i)) • _= _; simp only [Function.comp_apply,spring,Matrix.submatrix_apply,Equiv.symm_apply_apply]; rfl

lemma patrol (P: Ten V (Cloth α) r)(R: Fin r→ Roof α β r): pump P R=ruins (spunk L P R):=by
    funext x; rw [pump,← ((Equiv.refl _).arrowCongr (panel L α)).tsum_eq]; rfl
lemma inspectFace (P: Ten V (Cloth α) r)(M:ropes Cover (Co L α) β): pump P (owns L M)=reflectCut M (turnTen (panel L α).symm P):=by rw [patrol (L:=L), brush_spunk]; exact funext fun x=> Eq.symm (climb_cut ..)

variable {M:Fin r→ ropes Cover (Co L α) β}
lemma widget {o:Site L}{P: Ten V (Cloth α) r}(h:Cork terrain (lift o) t A P)(e:∀ i,dragCup terrain s B (M i))(hp:s/L.val≤ t)(hs:0≤s) : Peb terrain 0 s (B^r*(A*Real.exp (8*s))) (spunk L P (fun i=> owns L (M i) i)):=by
   rw [brush_spunk]; have he:= palmcash_ribbon e ((h.mono hp).cipher hs) hs; rwa [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at he

variable [Fintype α]
lemma pumpFace {o:Site L}{P:Ten V (Cloth α) r}(h:Cork terrain (lift o) t A P)(e:∀ i,dragCup terrain s B (M i))(hp:s/L.val≤t)(hv:0≤η)(hs:η<s): Cork terrain 0 η ((B^r*(A*Real.exp (8*s)))*tiePay (Co L α) r (s-η)) (pump P (fun i=>owns L (M i) i)):=by rw [patrol (L:=L)]; exact (widget h e hp (hv.trans hs.le)).meter hs hv

variable [CompleteSpace V]
lemma pumpFaceReady {o:Site L}{P:Ten V (Cloth α) r}(h:Cork terrain (lift o) t A P)(e:∀ i,dragCup terrain s B (M i))(hp:s/L.val≤t)(hv:0<s)(x): Summable (spinJob P (fun i=> owns L (M i) i) x):= by
   let Q:= (Equiv.refl (Fin r)).arrowCongr (panel (L:=L) (α:=α)); apply (Q.summable_iff (f:=spinJob P (fun i=> owns L (M i) i) x)).mp; exact ((widget h e hp hv.le).cache hv le_rfl x).2.1.of_norm

variable {Q H:ropes Cover (Co L (Hooks G)) (Hooks G)}
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma adequacy {P:Ten V (YForest G) r}(o){h:Cork terrain o s A P}(hs:0≤s): Amber terrain s A P:=by
    refine ⟨h.1,fun x=>(h.2 x).trans ?_⟩; apply mul_le_mul_of_nonneg_left _ h.1; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (by linarith); apply Nat.cast_le.mpr; apply league_le; intro i j; exact leg_le terrain (stud o x) i.succ j.succ

def assumeU (Z:ReaderT L G): ropes Cover (Co L (Hooks G)) (Hooks G):= fun u i=> Z (u.1,u.2.1,Exterior.vac,u.2.2.2) i
lemma flagL (i:Fin (r+1))(Z:ReaderT L G): apex i (fun _ x j=>spring L Z (well x j))=owns L (assumeU Z) i:=by funext p x; change Z _ _ = Z _ _; simp only [patchwork]; rfl

-- proof B size ≥ θ and all touched M. R->R'.
lemma neighborC (i:Fin (r+1)){b:Site L} {K:Fin (r+1) → ropes Cover (Co L (Hooks G)) (Hooks G)}{W:ropes Cover (Co L (Hooks G)) (Hooks G)}{P:Ten V (YForest G) (r+1)}(h:Cork terrain (lift b) t A P)(g:∀ j,dragCup terrain s B (K j))(hf:dragCup terrain s B W)(e:Smooth P){Z:ReaderT L G}(u: verdant (K i) W Z)(hg:roaring (lift b) P t D)(hk:dragCup terrain s B Z)(hp:s/L.val ≤ t)(hv:0≤η)(hs:η<s):
    let R j:= owns L (K j) j; Cork terrain 0 η ((B^(r+1)*(D*Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-η)) (pump P (Function.update R i (owns L W i))-pump P R):=by
    intro R; let T:=Function.update K i (assumeU Z); let F:=ledger P i; let V':=owns L W i - R i; let Y:=Function.update R i V'
    have he:= lt_of_le_of_lt hv hs; have hy : ∀ j,dragCup terrain s B (T j):= by
       intro j; unfold T; by_cases h:i=j
       · subst j; rw [Function.update_self]; exact ⟨hk.1,fun _ _=> hk.2 ..⟩
       rw [Function.update_of_ne (Ne.symm h)]; exact g _
    have hT : (fun i=>owns L (T i) i)=Function.update R i (apex i (fun _ x j=>spring L Z (well x j))):=by
       funext j; unfold T; by_cases h:j=i; · rw [h,Function.update_self,Function.update_self,flagL]
       rw [Function.update_of_ne h, Function.update_of_ne h]
    have h' := (adequacy _ (h:=h) (le_trans (div_nonneg he.le (by positivity)) hp)); rw [spin_sub h' hp he (fun j=> ownS (g j) j) (ownS hf i)]
    let S:=fun j=> owns L (T j) j
    have hA := pumpFace (ledger_stencil hg i) hy hp hv hs
    rw [show pump _ _= -(pump F S) from ?_]; exact hA.neg
    funext x
    have he' : ∀ j, sells L s (B+B) (Y j):=by
       intro j; by_cases h:j=i; · subst j; unfold Y; rw [Function.update_self]; exact (ownS hf _).sub (ownS (g i) i) he.le
       unfold Y; rw [Function.update_of_ne h]; exact (ownS (g j) j).cost (le_add_of_nonneg_right hk.1)
    have hw : Summable (spinJob P Y x):= (pump_sum he' h' he hp x).of_norm
    have hE : Summable (spinJob F S x):= pumpFaceReady (ledger_stencil hg i) hy hp he _
    have hF : Summable (spinJob P S x):= pumpFaceReady h hy hp he _
    apply eyeY i (spinJob P Y x) (spinJob F S x) hw hE
    intro p; cases isEmpty_or_nonempty (YForest G); · simp
    next hv=>
     let k:= Classical.arbitrary (YForest G); set D':= ∏ j∈Finset.univ.erase i, R j (enlist i k p) (x j)
     let J:=visitJ (YForest G) i
     have hu (z:YForest G): ∏ j∈Finset.univ.erase i,R j (enlist i z p) (x j)=D':=by
        apply Finset.prod_congr rfl; intro j hj; unfold R owns; rw [remote (Finset.mem_erase.mp hj).1 p z k]
     let c y j:= D' * spring L Z (well y j) (x i)
     have hc (F:Ten V (YForest G) (r+1)) (z:YForest G): spinJob F S x (enlist i z p)= c z.1 z.2.2 • F (enlist i z p):=by
        unfold S; rw [hT,spin_replace,hu]; unfold c apex; rw [outside,enlist_it,mul_comm]
     apply tally2 i e c p _ _ ((J.summable_iff.mpr hw).prod_factor p) ((J.summable_iff.mpr hE).prod_factor p) _ (hc F) (((J.summable_iff.mpr hF).prod_factor p).congr (hc P))
     intro y j d; change spinJob P (Function.update R i V') x (enlist i (waive y d j) p)=_; rw [spin_replace,hu]; unfold c V' R; rw [Pi.sub_apply,Pi.sub_apply, owns,owns,enlist_it,u,mul_comm, mul_sub]

lemma mixRoad {w:Site L}{P:Ten V (YForest G) (r+1)}{Z:ReaderT L G}(h:Cork terrain (lift w) t A P)(g:dragCup terrain s B H)(p:dragCup terrain s B Q)(k:verdant H Q Z)(hp:Smooth P)(ha:roaring (lift w) P t D)(hx:dragCup terrain s B Z)(he:s/L.val≤t)(hv:0≤η)(hs:η<s) : Cork terrain 0 η ((r+1:ℕ)* ((B^(r+1)*(D * Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-η))) (pump P (owns L Q)-pump P (owns L H)):=by
    let M i (j:Fin (r+1)):= if j.val< i then Q else H; let V i:= fun j=> owns L (M i j) j; let S:= (B^(r+1)*(D*Real.exp (8*s)))*tiePay (Co L (Hooks G)) (r+1) (s-η)
    have hh :∀ i≤r+1,Cork terrain 0 η (i*S) (pump P (V i)-pump P (owns L H)):=by
       intro i; induction i with
       | zero=> intro _; rw [Nat.cast_zero,zero_mul,show V 0=owns L H from funext fun _=>by simp only [V,M,Nat.not_lt_zero,↓reduceIte],sub_self]; exact Cork.zero
       | succ i ih=>
         intro h'; let v:Fin (r+1):= ⟨i,h'⟩
         rw [Nat.cast_succ,add_mul,one_mul,add_comm _ S, show pump _ _-_= (pump P (V (i+1))-pump P (V i))+(pump P (V i)-pump P (owns L H)) by abel]
         have heq: V (i+1)=Function.update (V i) v (owns L Q v):=by
            funext j; by_cases hh:j=v; · subst j; unfold V; rw [Function.update_self,show M (i+1) v= Q from if_pos (Nat.lt_succ_self i)]
            rw [Function.update_of_ne hh]; unfold V; congr 1; have ht:j.val≠i:= fun h=>hh (Fin.ext h); simp only [M,show j.val< i+1 ↔ j.val< i by omega]
         have hm j:dragCup terrain s B (M i j):= by unfold M; split<;> assumption
         rw [heq]; exact (neighborC v h hm p hp (by rw [show M i v=H from if_neg (lt_irrefl i)]; exact k) ha hx he hv hs).add (ih (by omega))
    specialize hh (r+1) le_rfl; rw [show V (r+1)=owns L Q from funext fun i=>by dsimp only [V,M]; rw [if_pos i.isLt]] at hh; exact hh
end YM.WilsonCoeffUV.Bank
