import YM.RegulatorIR.Step.Grid

/-! Coupling-rank valences at a step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Step
open Budget Motion Budget.Deck Budget.Tariff Budget.Packet Budget.Layer Diagram Function
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y U V: Type} {P:ℝ} {A:Deck P X U}{B:Deck P Y V}
namespace GridStep
variable (S:GridStep A B)
private lemma crop_zero (f:U↪V){r:ℕ}: crop f (0: Packet V r)=0:=rfl
private lemma offer_z (f:U↪V){r:ℕ}: offer f (0:Packet U r)=0:=by ext1 z; simp [offer,Stalk.collect]
private lemma draft_zero (K:Layer X X){r:ℕ}: draft K (0:Packet X r)=0:=by
 have h (l:List (Fin r)):drawing (0:Packet X r) K l=0:=by induction l with
  | nil=>rfl
  | cons a v ih=>rw [drawing,ih,ray_zero]
 rw [draft,h,sym_zero]
lemma joint_vac_shape {T:Orders X}(h:Vacuum T)(hh:Vacuum S.addon):Vacuum (S.jVac T):= by
 intro e r he; by_cases ht:S.addon e r=0
 · apply h e r; intro hv;apply he;simp_rw [GridStep.jVac,hv,ht,offer_z,zero_add]
 exact hh e r ht
lemma joint_fold_shape {T:Orders U}(h:Vacuum T)(hh:Vacuum S.addon):Vacuum (S.jOrb T):=by
 intro e r he; by_cases ht:S.addon e r=0
 · apply h e r; intro hv; apply he;simp_rw [GridStep.jOrb,hv,ht,offer_z,Deck.desk_zero,zero_add]
 exact hh e r ht
lemma pure_step {T:Orders X}(h:Vacuum (S.jVac T)):Vacuum (S.pure T):=by
 intro e r he; unfold pure at he; split_ifs at he; · exact (he rfl).elim
 have hp : ceaseHeat S.line (S.jVac T) false e r≠0:=fun h'=>he (by rw [pullI,h',draft_zero,crop_zero])
 unfold ceaseHeat heated at hp
 obtain ⟨p,_,hh⟩:= Finset.exists_ne_zero_of_sum_ne_zero hp
 have ht:= heated_cap S.line (S.jVac T) h false e r p hh; exact ⟨ht.1,ht.2.1⟩
lemma fold_step {T:Orders U}(h:Vacuum (S.jOrb T)):Vacuum (S.common T):=by
 intro e r he; unfold common at he; split_ifs at he; · exact (he rfl).elim
 have hp : ceaseHeat S.layer (S.jOrb T) true e r≠0:=fun h'=>he (by rw [pullJ,h',draft_zero,crop_zero])
 unfold ceaseHeat heated at hp
 obtain ⟨p,_,hh⟩:= Finset.exists_ne_zero_of_sum_ne_zero hp
 have ht:=heated_cap S.layer (S.jOrb T) h true e r p hh;exact ⟨ht.1,ht.2.1⟩
lemma each_shape {T W:Orders X}(h:Vacuum (S.jVac T))(m:ℕ)(hh:∀ e,Within (e+m) (W e)) (e): Within (e+m) (S.each m T W e):= by
 let F:Orders (X⊕Y) := fun e r=> offer (firstChannel A B).native (W e r)
 intro r he
 have hx e :Within (e+m) (F e) := fun r h=> hh e r (fun h'=> h (by unfold F; rw [h',offer_z]))
 let V:= endHeat m S.line (logHeat S.line (S.jVac T) false) F
 have hp : V e r≠0 := fun h'=> he (by change S.pullI (V e r)=0; rw [pullI,h',draft_zero,crop_zero])
 unfold V Diagram.endHeat heated at hp
 obtain ⟨p,_,hh'⟩:= Finset.exists_ne_zero_of_sum_ne_zero hp; exact (marked_cap m S.line (S.jVac T) h F hx false e r p hh').1
lemma island_shape {T W:Orders U}(h:Vacuum (S.jOrb T))(m:ℕ)(hh:∀ e,Within (e+m) (W e)) (e): Within (e+m) (S.island m T W e):= by
 let F:Orders (U⊕V) := fun e r=> offer (firstChannel A B).tile (W e r)
 intro r he
 have hx e :Within (e+m) (F e):=fun r h=> hh e r (fun h'=>h (by unfold F; rw [h',offer_z]))
 let X := endHeat m S.layer (logHeat S.layer (S.jOrb T) true) F
 have hp : X e r≠0:=fun h'=>he (by change S.pullJ (X e r)=0; rw [pullJ,h',draft_zero,crop_zero])
 unfold X Diagram.endHeat heated at hp
 obtain ⟨p,_,hh'⟩:= Finset.exists_ne_zero_of_sum_ne_zero hp; exact (marked_cap m S.layer (S.jOrb T) h F hx true e r p hh').1

end GridStep
end YM.RegulatorIR.Step
