import YM.OPE.Compatible.Tides.Pays
/-!
# Mesoscopic vertex symbol. νPower and Lap
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{d:ℝ}{g h:ℕ→ Cover→ℝ}{k j:ℕ}
namespace Port
lemma arms (hf:Port U d k g)(l:List Axis):Port U d (k+l.length) (stalkP l g):=by
    induction l with
    | nil=> exact hf
    | cons i l ih=> rw [List.length_cons,← add_assoc]; exact ih.split i
def listX (j:ℕ):Finset (Multiset Axis):=(trail Axis (j+1)).filter (fun i=> i.card=j)
@[simp] lemma cardA (v:Multiset Axis): v∈listX j ↔ v.card=j:=by rw [listX,Finset.mem_filter,trailed];omega
def eve (U:Gloam)(k j:ℕ)(g:ℕ→Cover→ℝ): E4→ℝ:=∑ v∈ listX j, slit U (k+j) (stalkP v.toList g) • horn v
lemma tap (hf:Port U d k g)(l): Tendsto (fun i=> (U.h i^(k+l.length))⁻¹*dvol l (g i) 0) atTop (𝓝 (slit U (k+l.length) (stalkP l g))):=(hf l).slit.2.2 -- underscore cause
lemma pureE (U:Gloam)(k j:ℕ)(g:ℕ→Cover→ℝ):PureA j (eve U k j g):=by
    unfold eve; rw [show (∑ v∈ listX j,_ )=(fun x:E4=>∑ v∈listX j,(slit U (k+j) (stalkP v.toList g) • horn v) x) from funext fun i=>Finset.sum_apply i _ _]; exact Pure.sumf _ _ (fun i hi=> (cardA i|>.mp hi) ▸ (horn_pure i).vScale _)
lemma ee_a (U:Gloam)(k j:ℕ)(g:ℕ→Cover→ℝ)(a:Axis): grad a (eve U k (j+1) g) = eve U (k+1) j (smear a g):=by
    funext x; let f(v:Multiset Axis):=slit U (k+(j+1)) (stalkP v.toList g); let F(v):= f v • horn v
    unfold eve; rw [grad_sum_f _ (f:=F) (fun i _=> (horn_pure i).smooth.contDiffAt.const_smul (f i)), Finset.sum_apply]
    let H:= (listX j).image (Multiset.cons a); have he:H ⊆ listX (j+1):=fun i hi=> by obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hi; simp_all only [cardA,Multiset.card_cons]
    rw [←Finset.sum_subset he,Finset.sum_image]; swap; · exact fun i _ v _ h=>(Multiset.cons_inj_right a).mp h
    · apply Finset.sum_congr rfl; intro i hi; rw [show F (a ::ₘ i) = _ from rfl]; change grad a (f (a ::ₘ i) • horn (a ::ₘ i)) x= _
      rw [grad_smul (horn_pure (a ::ₘ i)).smooth.contDiffAt, blowing, if_pos (Multiset.mem_cons_self ..),Multiset.erase_cons_head]; have hh:stalkP (a ::ₘ i).toList g = stalkP i.toList (smear a g):=by
           rw [streak]; apply funext; intro j; apply rotate_perm; apply (Multiset.coe_eq_coe ..).mp; rw [Multiset.coe_toList]; change a ::ₘ i=a ::ₘ (i.toList:Multiset Axis);rw [Multiset.coe_toList]
      erw [show f _=_ from rfl]; unfold f -- double
      rw [hh,show k+(j+1)=k+1+j from by omega]; rfl
    intro i hi hh; unfold F; rw [grad_smul (horn_pure i).smooth.contDiffAt,blowing,if_neg (show a∉i from fun hx=> hh (Finset.mem_image.mpr ⟨i.erase a, (cardA _).mpr (by have ht:= (cardA _).mp hi; rw [Multiset.card_erase_of_mem hx,ht,Nat.pred_succ]), Multiset.cons_erase hx⟩))]; simp
end Port
end YM.OPE.Balsam
