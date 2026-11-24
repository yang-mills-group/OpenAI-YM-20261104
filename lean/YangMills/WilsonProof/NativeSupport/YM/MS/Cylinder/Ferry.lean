import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Shade

/-! Transport position modes and scale, morphisms finite or equations after wrap. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Set Finset Koszul Slim
variable {R A B C : Type*} [CommRing R] {p : Sector A} {q : Sector B} {s:Finset A}
variable (r:A→B)

open Classical in
def way (r:A→B) (i:B) (j:A): R:= if i=r j then 1 else 0
lemma only (i:A) : way r (r i) i=(1:R):= if_pos rfl
lemma need {i:A} {j:B} (h:j≠r i): way r j i=(0:R):= if_neg h
lemma way_thin : Slim (way r (R:=R)):= fun i=> (Set.finite_singleton (r i)).subset (fun _ hj=> Classical.byContradiction fun h=> hj (need r h))
def Ferry (r:A→B): Cyl A R→ₗ[R] Cyl B R:= arrive (way r) (way_thin r)
@[simp] lemma sailed (F : Cyl A R): (Ferry r F).val=shade (way r) F:=rfl
lemma ferry_uses {s:Set A} (F:Cyl A R)(h:Uses s F.val): Uses (r '' s) (Ferry r F).val := stretch F h (fun i hi _ hj=> ⟨i,hi,Eq.symm <| Classical.byContradiction fun he=> hj (need r he)⟩)
lemma ferry_tie (h: ∀ i, p i=q (r i)) : Tie p q (way r (R:=R)):= by
    intro i j hh; by_cases he:j=r i; exact he ▸ h i; exact (hh (need r he)).elim
lemma ferry_twist (h:∀ i,p i=q (r i)) (F:Cyl A R)(c:Bool): Ferry r (twisted p c F)= twisted q c (Ferry r F):= (way_thin r).twists (ferry_tie r h) ..
lemma ferry_pair (h:∀ i,p i=q (r i))(F H:Cyl A R): Ferry r (couple p F H)= couple q (Ferry r F) (Ferry r H):= (way_thin r).connect (ferry_tie r h) ..
-- compose with a shade (transport and test)
lemma study (T:C→B→R) (F:Cyl A R): shade T (Ferry r F)=shade (fun i j=> T i (r j)) F:= by
    classical
    funext l; induction l generalizing F with
    | nil=>simp
    | cons a l ih=>
        obtain ⟨s,hs⟩:=fromCyl F; let S:=s.image r; have hS:Uses (S:Set B) (Ferry r F).val:= by dsimp only [S]; rw [Finset.coe_image]; exact ferry_uses r F hs
        rw [deriv_lum T _ _ hS,deriv_lum (fun i j=> T i (r j)) _ _ hs]
        have hx i: enter i (Ferry r F)=∑ j∈s,(way r i j:R) • Ferry r (enter j F):= by unfold Ferry; simp_rw [(way_thin r).drop _ F hs,map_sum,map_smul]
        simp_rw [hx,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i hi=>?_)
        rw [Finset.sum_eq_single (r i),only, one_smul,ih]
        · intro v hv he; rw [need r he,zero_smul,mul_zero]
        exact fun h=> (h (Finset.mem_image_of_mem r hi)).elim
lemma ferry_trans (q:B→C)(F:Cyl A R): Ferry q (Ferry r F)= Ferry (q ∘ r) F:= by
    apply Subtype.ext; simp only [sailed,study _ (way q)]; rfl
lemma us_from (F:Cyl A R)(h:InjOn r (s:Set A))(hs:Uses (s:Set A) F.val){i:A}(hi:i∈s) : enter (r i) (Ferry r F)=Ferry r (enter i F):= by
    classical
    unfold Ferry; rw [(way_thin r).drop _ F hs, Finset.sum_eq_single i,only,one_smul]; swap; exact fun h=> (h hi).elim
    intro b hb he; exact Eq.trans (by rw [need r (fun hh=> he (h hb hi hh.symm))]) (zero_smul R _)
lemma ferry_units (F:Cyl A R)(h:Injective r)(i:A): enter (r i) (Ferry r F)= Ferry r (enter i F):= by
    classical
    obtain ⟨s,hs⟩:=fromCyl F; exact us_from r F h.injOn (hs.mono (s':=↑(insert i s:Finset A)) (Finset.subset_insert i s)) (mem_insert_self ..)
lemma ferry_test (F:Cyl A R)(h:InjOn r (s:Set A))(hs:Uses (s:Set A) F.val)(l:List A) (he:∀ i∈l, i∈s): (Ferry r F).val (l.map r)=F.val l:= by
    induction l generalizing F with
    | nil=>simp
    | cons i l ih=>
        rw [List.map_cons,show (Ferry r F).val (r i :: _)= (enter (r i) (Ferry r F)).val (l.map r) from rfl, us_from r F h hs (he _ (by simp)), ih (enter i F) (hs.drop _) (fun i hi=> he _ (List.mem_cons_of_mem _ hi))]; rfl
lemma without (F:Cyl A R)(h:Injective r)(l:List A) : (Ferry r F).val (l.map r)=F.val l:=by
   classical
   obtain ⟨s,hs⟩:=fromCyl F; exact ferry_test r F h.injOn (hs.mono (s':=↑(s∪l.toFinset:Finset A)) (by simp)) _ (by simp +contextual)
lemma ferry_id (F:Cyl A R) : Ferry id F=F:=Subtype.ext (funext fun l=> by simpa using without id F injective_id l)
lemma ferry_zero (F:Cyl A R)(h:InjOn r (s:Set A))(hs:Uses (s:Set A) F.val)(he:Ferry r F=0): F=0:= by
   apply Subtype.ext; funext l; by_cases h':∀ i∈l,i∈s
   · rw [← ferry_test r F h hs l h',he]; rfl
   push Not at h'; obtain ⟨i,hi,hJ⟩:=h'; exact hs l i hi hJ
-- Scaling rule with multiplicative α : A→R, no finite-type assumptions

def rent (c:A→R)(f:Raw A R): Raw A R:=fun l=> (l.map c).prod*f l
def graffiti (c:A→R): Cyl A R→ₗ[R] Cyl A R where
    toFun f:= ⟨rent c f.val, by obtain ⟨s,hs⟩:=fromCyl f; exact ⟨s,fun l i hi hx=> by simp [rent,hs l i hi hx]⟩⟩
    map_add' x y:= Subtype.ext (funext fun l=> mul_add ..)
    map_smul' t x:= Subtype.ext (funext fun l=> mul_left_comm ..)
lemma landc (c:A→R)(F:Cyl A R): (graffiti c F).val=rent c F.val:=rfl
lemma tagged (c:A→R)(F:Cyl A R): (graffiti c F).val []=F.val []:= by simp [landc,rent]
lemma tagged_s (c:A→R)(F:Cyl A R)(i:A): enter i (graffiti c F)= (c i) • graffiti c (enter i F):= by apply Subtype.ext; funext l; exact mul_assoc ..
lemma tagUses (c:A→R)(F:Cyl A R){s:Set A}(h:Uses s F.val): Uses s (graffiti c F).val:= fun l i hi hx=> by simp [landc,rent,h l i hi hx]
lemma tag_sign (c:A→R)(F:Cyl A R)(x:Bool): twisted p x (graffiti c F)=graffiti c (twisted p x F):= Subtype.ext (funext fun _=> mul_left_comm ..)
lemma tag_grows (c:A→R)(F H:Cyl A R) : graffiti c (couple p F H)=couple p (graffiti c F) (graffiti c H):= by
   apply Subtype.ext; funext l; induction l generalizing F H with
   | nil=> simp [tagged]
   | cons x l ih=>
       simp_rw [D_eval x (Subtype.val _),← enterp,tagged_s,couple_diff,tag_sign,tagged_s] -- order
       simp only [map_add,map_smul,smul_add,LinearMap.smul_apply,smul_stack,add_stack,Pi.smul_apply,Pi.add_apply,ih]
lemma ferry_rent (c:B→R) (F:Cyl A R): Ferry r (graffiti (c ∘ r) F)=graffiti c (Ferry r F):= by
    apply Subtype.ext; funext l; induction l generalizing F with
    | nil=> simp [tagged]
    | cons j l ih=>
       obtain ⟨s,hs⟩:=fromCyl F
       rw [sailed,deriv_lum _ _ _ (tagUses _ F hs),landc]; unfold rent; rw [sailed,deriv_lum _ _ _ hs, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i hi=>?_)
       by_cases he:j=r i; swap; · simp [need r he]
       subst j; rw [only,tagged_s,map_smul, Pi.smul_apply,← sailed,ih,landc,rent]; simp [mul_assoc]
end YM.MS.Cylinder
