import YM.Frontier6.Bouquet.Atlas.Lending

/-! For the inductive application of Sails: every compatible disjoint-region
 subquestion is admissible, inheriting payments. Also use to read the same charts
 in order and coherence statements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Fareway Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L J X:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{K:Final C F S}
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable {P Q:Ensemble} (R:Air (S:=S) P I L Y)(h:Q≤P)(f:J→ I)(B:J→ Aura Q)
section
variable [DecidableEq X]{r:ℝ}{c:Fabric I}{T:Fareway I}{L:Finset ℝ}
lemma children (s:Finset X)(e:s.Nonempty)(a:X→ Art S I) (b:X→ Fabric I)(t:X→ℝ)(he:∀ i∈s, Extends T c (b i))(ht:∀ i∈s,Pen K T L r (b i) (a i) (t i))(hh:∀ i∈s,∀ j∈s, i≠j → Cross T (b i) (b j) r): Pen K T L r c (∏ i∈s, a i) (∑ i∈s,t i):=by
    induction s using Finset.induction_on generalizing c with
    | empty=> simp at e
    | @insert i s hx ih=>
       by_cases hv:s.Nonempty; swap; obtain rfl:= Finset.not_nonempty_iff_eq_empty.mp hv; simpa using (ht i (by simp)).weaker (he i (by simp))
       rw [Finset.prod_insert hx,Finset.sum_insert hx]; let C' := fun j:I=> ⋃ i∈s,b i j; have hr i' (hj:i'∈s):i'∈insert i s:= Finset.mem_insert_of_mem hj
       let u:= Finset.mem_insert_self i s; have h' :Pen K T L r C' (∏ i∈s,a i) (∑ i∈s,t i):= ih hv (fun k hk=> Eventually.of_forall fun j=> subset_iUnion₂ (s:= fun i (_:i∈s)=> b i j) k hk) (fun i hi=> ht _ (hr i hi)) (fun i hi j hj=> hh _ (hr i hi) _ (hr j hj))
       have hk: Cross T (b i) C' r:=by
          intro v hv'; filter_upwards [(eventually_all_finset s).mpr (fun j (hj:j∈s)=> hh i u j (hr j hj) (fun e=>hx (e ▸ hj)) _ hv')] with j hj x hx y hy; obtain ⟨k,hk,h⟩:= mem_iUnion₂.mp hy; exact hj k hk _ hx _ h
       refine ((ht i u).mul h' hk).weaker ?_; filter_upwards [he i u, (eventually_all_finset s).mpr fun j (hj:j∈s)=> he j (hr j hj)] with j hi hj; exact Set.union_subset hi (Set.iUnion₂_subset fun k hk=>hj k hk)
end
-- volume.Inheritance. Keep $B.center` independent as supplies (transaction powers only).
def heir : Air (S:=S) Q J L Y where
    region := B
    route := R.route.pull f
    role := R.role ∘ assign h
    account := R.account ∘ f
    sky j:= convey h (R.sky (f j))
lemma heir_lengths (i:J): (heir R h f B).lengths i= R.lengths (f i) ∘ assign h:=rfl
section
variable {M:Pod→ℝ}{c:ℝ}
   (hc:∀ i:J,(B i).foot ≤ (R.region (f i)).foot ∘ assign h)
   (hC:0<c) (he:∀ i:J,∀ u v: Q, assign h u=assign h v→ u≠v→∀ x∈(B i).foot u,∀ y∈(B i).foot v, c*R.lengths (f i) (assign h u) ≤ ‖x-y‖)
include hc hC he
lemma heir_host (ht:Air.Hosts K R) : Air.Hosts K (heir R h f B):=by
    intro X g T hT V x hX hV hv hy u v hp; let Z:=R.foci (f ∘ g); let Q':= (heir R h f B).foci g
    have hV'(i:P): x (R.role i) ∈ V:=by obtain ⟨i,rfl⟩:=assign_surjects h i; exact hy i
    let w(p:P):=∑ i∈dialogues h p,u i; let F(p:P):=∏ i∈dialogues h p,v i
    have hs:P → ℕ:=fun i=>0; -- remove
    have hW(p:P): Pen K T V (x (R.role p)) (Z p) (F p) (w p):=by
        let D:=dialogues h p; have He(i)(hi:i∈D): (heir R h f B).role i=R.role p:= congr_arg _ ((members ..).mp hi) -- shadows
        refine children D ?_ v Q' u (fun i hi=> ?_) (fun i hi=> He i hi ▸ hp i) (fun i hi j hj hh=>?_)
        · obtain ⟨u,hu⟩:= assign_surjects h p; exact ⟨u,(members h ..).mpr hu⟩
        · have hx: assign h i=p:= (members ..).mp hi; apply Eventually.of_forall; intro j; exact hx ▸ hc (g j) i
        have h1:= (members h ..).mp hi; have h2:= (members h ..).mp hj; intro a ha
        have ht:= (T.minted_c c hC).mul (hX (R.role p)); refine ((T.minted (-a)).cheaper ht (by linarith)).mono (fun q hq x' hx y' hy=>le_trans hq.le (?_)); exact h1 ▸ he (g q) i j (h1.trans h2.symm) hh x' hx y' hy
    refine ((ht X (f ∘ g) T _ x hX hV hv hV' w F hW).cf ?_).too (?_)
    · filter_upwards with j; unfold F; simp_rw [Finset.prod_apply]; exact congr_arg (_ • ·) (convey_at ..).symm
    exact (Finset.sum_fiberwise Finset.univ (assign h) u).le -- sum
end
end YM.Frontier6.Bouquet.Audit
