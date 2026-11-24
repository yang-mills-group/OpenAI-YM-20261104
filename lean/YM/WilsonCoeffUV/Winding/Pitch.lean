import YM.WilsonCoeffUV.Winding.Spin
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type}{G:Gauge}{D:ι→ℕ}{i j k r e a l:ℕ}{s A B C W t q :ℝ}
variable {J I S:Finset ι}{p:ι→Cover}{x:ι}{P:Patch}
-- tax
abbrev chartIn (P:Patch)(p:ι→Cover)(b:ι→ Site P.L)(i:ι):Cover:= P.L.val • p i + lift (b i)
lemma escortM (P:Patch)(p:ι→Cover)(b:ι→Site P.L)(y:dock Cover (Co P.L α) r) :
    Syn Bank.terrain (chartIn P p b) S (panel P.L α ∘ y) ≤ P.L.val*(Syn Bank.terrain p S y+8):=by
    let u : ↑S⊕ Fin r → Cloth (Co P.L Unit) := Sum.elim (fun i:S=> (p i.val,b i.val,())) (fun i:Fin r=> ((y i).1,(y i).2.1,()));
    have hx: foyer p S y= Prod.fst ∘ u:= funext fun i=>by cases i<;>rfl
    have he: foyer (chartIn P p b) S (panel P.L α ∘ y)=Prod.fst ∘ (panel P.L Unit ∘ u):= funext fun i=>by cases i<;>rfl
    unfold Syn; rw [he,hx]; apply league_le; intro i j; exact (padLift (u i) (u j)).trans (Nat.mul_le_mul_left P.L.val (Nat.add_le_add_right (leg_le Bank.terrain (Prod.fst∘ u) i j) 8))
lemma escortT (P:Patch)(p:ι→Cover)(b:ι→Site P.L)(y:dock (Site n) (Co P.L α) r) :
     let g:= ratioN P.L n
     P.L.val*Syn (tor n) (wrap n ∘ p) S y ≤ Syn (tor (n*P.L)) (wrap (n*P.L) ∘ (chartIn P p b)) S ((splitCo g α).symm∘ y)+8*P.L.val:=by
    intro g; let u : ↑S⊕ Fin r → Co n (Co P.L Unit) := Sum.elim (fun i:S=> ((wrap n ∘ p) i.val,b i.val,())) (fun i:Fin r=> ((y i).1,(y i).2.1,())); let v:= Fintype.equivFin (↑S⊕ Fin r); let h:=local_pack g (u ∘ v.symm)
    have hx: foyer (wrap n ∘ p) S y=Prod.fst ∘ u:= funext fun i=>by cases i<;>rfl
    have ht: foyer (wrap (n*P.L) ∘ (chartIn P p b)) S ((splitCo g α).symm∘ y)=Prod.fst∘ ((splitCo g Unit).symm ∘ u):=by
        funext i; cases i with
        | inr i=>rfl
        | inl i=>
            change wrap _ (P.L.val • _ + lift (b i.val))= g.embed (wrap n _) + _
            rw [map_add, show wrap _ (P.L.val • _)= g.embed (wrap n _) from (g.embed_wrap _).symm]; rfl
    unfold Syn; rw [hx,ht,← league_equiv _ _ v.symm, ← league_equiv (tor _) (Prod.fst∘ _) v.symm]
    exact h

variable [NormedAddCommGroup V]
lemma coat_grasp {Q:Ten V (Co (n*P.L) α) r}(p:ι→Cover)(b:ι→Site P.L)(h:Wig (tor (n*P.L)) (wrap _ ∘ chartIn P p b) (s/P.L.val) A S Q)(v:0≤s):
    let q:=turnTen (splitCo (ratioN P.L n) α) Q
    Wig (tor n) (wrap n ∘ p) s (A*Real.exp (8*s)) S q:=by
    intro q; refine ⟨mul_nonneg h.1 (by positivity),fun x=> ?_⟩; rw [mul_assoc]; exact (h.2 _).trans (mul_le_mul_of_nonneg_left (spentL P.L (escortT P p b x) v) h.1)

lemma MarkU.pitchIn {F:Ten V (Cloth α) r}{Q:Ten V (Co (n*P.L) α) r}(b:ι→ Site P.L)(h:MarkU (chartIn P p b) J Q F s A)(v:0<s): MarkU p J (turnTen (splitCo (ratioN P.L n) α) Q) (turnTen (panel P.L α).symm F) (s/8) (2*Real.exp (16*s)*A):=by
    let B:=2*Real.exp (16*s)*A; let W:= turnTen (splitCo (ratioN P.L n) α) Q; let F':= turnTen (panel P.L α).symm F
    let q:=Real.exp (8*s); have hg:1≤ q:= Real.one_le_exp (by positivity); have hA:=h.bill.1; have hx:0≤ A*q:=mul_nonneg hA (zero_le_one.trans hg)
    have he: A*q≤ B:=by unfold B; rw [show Real.exp (16*s)=q*q from by unfold q; rw [←Real.exp_add]; congr 1; ring]; nlinarith
    have ht:= h.mono (show s/P.L.val≤ s from div_le_self v.le (by exact_mod_cast P.L.property)); have hz:= plankB P p b J F ht.access v.le; have hr:= coat_grasp p b ht.bill v.le; have hp:s/8 ≤ s:=by linarith
    refine ⟨(hz.shave hp).more he,(hr.shave hp).more he, ⟨hx.trans he,fun x u=>?_⟩⟩; let X:= panel P.L α ∘ x; let f:= n*P.L
    by_cases hb:4*Syn Bank.terrain (chartIn P p b) J X<f.val
    · change ‖W (slideC n x)- _‖≤_; rw [show W (slideC n x)= Q (slideC f X) from congr_arg Q (funext fun i=> (panel_wrap (ratioN P.L n) (x i)).symm)]
      have hV: catchW s f ≤ catchW (s/8) n:= by apply (catch_width hp _).trans; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (by linarith); exact_mod_cast (show n.val≤ f.val from Nat.le_mul_of_pos_right _ P.L.property)
      apply (h.gulf.local_w X hb).trans; exact mul_le_mul ((le_mul_of_one_le_right hA hg).trans he) hV (catch_hot ..) (hx.trans he)
    have hh:n.val≤4*Syn Bank.terrain p J x+32:= guideScale (escortM P p b x) (Nat.le_of_not_gt hb)
    have hL:= cheer_mid v hh; have hX: ‖W (slideC n x)‖ ≤ A*q*(q*catchW (s/8) n):=by refine (hr.2 (slideC n x)).trans ?_; rw [exact_syn p J x u]; exact mul_le_mul_of_nonneg_left hL hx
    apply (norm_sub_le ..).trans ((add_le_add hX ((hz.2 x).trans (mul_le_mul_of_nonneg_left hL hx))).trans_eq _); rw [show Real.exp (16*s)=q*q from by unfold q; rw [←Real.exp_add]; congr 1; ring]; ring
end YM.WilsonCoeffUV.Winding
