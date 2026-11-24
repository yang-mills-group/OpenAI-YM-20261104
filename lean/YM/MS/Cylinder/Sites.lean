import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Ferry
import YM.MS.Plane

/-!
# One site coordinates; translation equivalence

`s` as native sites only. Translation is of **origin** of density. Plane
 is just bookkeeping; these don't live on reciprocal test spaces. Distinguish
 integrated stencil from anchored kernel. Some lemmas allow arbitrary positions
 perhaps not groups.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Lab
open Function Set Finset Koszul Plane
variable {R A P Q J : Type*} [CommRing R] {p : Sector A} {s:Finset P}
-- Notes reuse Axis etc
abbrev Seed (A P R : Type*) [CommRing R]:= Cyl (Mode A P) R
abbrev BoundBy (s:Set P)(F:Seed A P R): Prop := Uses (Prod.snd ⁻¹' s) F.val
lemma obliges (F:Seed A P R): ∃ s:Finset P, BoundBy (s:Set P) F:= by
   classical
   obtain ⟨u,hu⟩:=fromCyl F; exact ⟨u.image Prod.snd,hu.mono fun i hi=> Finset.mem_image_of_mem Prod.snd (show i∈u from hi)⟩
lemma each_side (F H:Seed A P R): ∃ s:Finset P, BoundBy (s:Set P) F∧BoundBy (s:Set P) H:= by
   classical
   obtain ⟨u,hu,hv⟩:=encloses F H; have he : (u:Set _)⊆ Prod.snd ⁻¹' (u.image Prod.snd:Set P):= fun i hi=> Finset.mem_image_of_mem Prod.snd (show i∈u from hi)
   exact ⟨u.image Prod.snd,hu.mono he,hv.mono he⟩

def post (r:P→Q): Mode A P→Mode A Q:=fun i=>(i.1,r i.2)
def transport (r:P→Q): Seed A P R→ₗ[R] Seed A Q R:= Ferry (post r)
lemma site_post (r:P→Q)(i:Mode A P): field p (post r i)=field p i:= rfl
lemma move_tie (r:P→Q): Tie (field p) (field p) (way (post r) (R:=R)) := ferry_tie _ (fun _=>rfl)
lemma transport_sign (r:P→Q)(c:Bool)(F:Seed A P R): transport r (twisted (field p) c F)= twisted (field p) c (transport r F):= (ferry_twist (post r) (fun _=> rfl) (p:=field p) (q:=field p) F c)
lemma transport_comes (r:P→Q)(F H:Seed A P R): transport r (couple (field p) F H)=couple (field p) (transport r F) (transport r H):= ferry_pair (post r) (fun _=>rfl) (p:=field p) (q:=field p) F H
lemma relax {s:Set P}(F:Seed A P R)(h:BoundBy s F) (r:P→Q): BoundBy (r '' s) (transport r F):= (ferry_uses (post r) F h).mono (by rintro _ ⟨u,hu,rfl⟩; exact ⟨u.2,hu,rfl⟩)
lemma post_inj {s:Set P} (r:P→Q)(h:InjOn r s): InjOn (post r (A:=A)) (Prod.snd ⁻¹' s):= fun _ hx _ hy he=> Prod.ext (congr_arg (Prod.fst (β:=Q)) he) (h hx hy (congr_arg (Prod.snd (β:=Q)) he))
lemma transport_single (r:P→Q)(h:InjOn r (s:Set P))(F:Seed A P R)(hs:BoundBy (s:Set P) F)(i:Mode A P)(hi:i.2∈s): enter (post r i) (transport r F)=transport r (enter i F):=by
   classical
   obtain ⟨u,hu⟩:=fromCyl F; let S := insert i (u.filter fun i=> i.2∈s)
   have he : (S:Set (Mode A P))⊆ Prod.snd ⁻¹' (s:Set P):= by
       intro j hj; rcases Finset.mem_insert.mp (show _∈S from hj) with rfl|he
       · exact hi
       exact (Finset.mem_filter.mp he).2
   refine us_from (post r) F ((post_inj r h).mono he) ?_ (show i∈S from Finset.mem_insert_self ..)
   intro l j hj hx; by_cases hv : j∈u; swap; · exact hu l j hj hv
   exact hs l j hj (fun hh=> hx (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hv,hh⟩)))
lemma transport_zero (r:P→Q)(h:InjOn r (s:Set P))(F:Seed A P R)(hs:BoundBy (s:Set P) F)(hz:transport r F=0): F=0:= by
   classical
   obtain ⟨u,hu⟩:=fromCyl F; let S := u.filter fun i=> i.2 ∈s
   have he : (S:Set (Mode A P)) ⊆ Prod.snd ⁻¹' (s:Set P):=fun _ hv=> (Finset.mem_filter.mp (show _∈S from hv)).2
   refine ferry_zero _ F ((post_inj r h).mono he) ?_ hz; intro l j hj hx; by_cases hv:j∈u; swap; · exact hu l j hj hv
   exact hs l j hj (fun hh=> hx (Finset.mem_filter.mpr ⟨hv,hh⟩))

section
def totalShade (T : Q→P→R) (i:Mode A Q) (j:Mode A P): R:= T i.2 j.2 * way id (i.1:A) (j.1:A)
omit p in
lemma block [Fintype A][DecidableEq A](F:Seed A P R)(h:BoundBy (s:Set P) F) (T: Mode A Q→Mode A P→R) (hc:∀ i j, T i j≠0→ i.1=j.1)(v : Mode A Q) : D v (shade T F)=∑ x∈s,T v (v.1,x) • shade T (enter (v.1,x) F):= by
    classical
    let W : Finset (Mode A P) := Finset.univ ×ˢ s; have he : (W:Set (Mode A P)) = Prod.snd ⁻¹' (s:Set P):=by ext; simp [W]
    rw [shade_drop T v F (show Uses (W:Set (Mode A P)) F.val from he.symm ▸ (show Uses (Prod.snd ⁻¹' (s:Set P)) F.val from h))]; unfold W; rw [Finset.sum_product,Finset.sum_eq_single v.1]
    · intro a _ ha; apply Finset.sum_eq_zero; intro i _; rw [show T v (a,i)=0 from Classical.byContradiction (fun hh=> ha (hc _ _ hh).symm),zero_smul]
    exact fun h=> (h (Finset.mem_univ _)).elim
lemma way_map (r:P→Q)(x:Q)(y:P)(a:A): way (post r) (a,x) (a,y)=(way r x y:R):= by
    by_cases he:x=r y; exact he ▸ (only (post r) (a,y)).trans (only r y).symm
    exact (need (post r) (fun H=> he (congr_arg Prod.snd H))).trans (need r he).symm
lemma fibre [Fintype A][DecidableEq A] (r:P→Q)(F:Seed A P R)(h:BoundBy (s:Set P) F)(j:A)(x:Q):
    enter (j,x) (transport r F)=∑ y∈s, (way r x y:R) • transport r (enter (j,y) F):= by
    apply Subtype.ext; simp only [sum_stack,enterp,smul_stack,transport,sailed,block F h (way (post r)) (fun i j h=> congr_arg Prod.fst (show i=post r j from Classical.byContradiction (fun he=> h (need _ he)))),way_map]
end

section additive
variable [AddCommGroup P]
def Shift (x:P) : Seed A P R→ₗ[R] Seed A P R:= transport fun i=> x+i
lemma shift_add (F:Seed A P R)(x y:P): Shift x (Shift y F)=Shift (x+y) F:= by
    unfold Shift transport; rw [ferry_trans]; congr! 2; unfold post; simp [add_assoc,Function.comp_def]
lemma shift_nil (F:Seed A P R): Shift 0 F=F:= by unfold Shift transport; rw [show post (fun i:P=>0+i)= @id (Mode A P) by ext <;> simp [post], ferry_id]
lemma shift_enter (F:Seed A P R)(a:A)(x y:P): Shift x (enter (a,y) F)=enter (a,x+y) (Shift x F):= (ferry_units (post (fun i:P=>x+i)) F (fun i j h=> Prod.ext ((congr_arg (Prod.fst (β:=P)) (show post _ i=post _ j from h) : (post (fun i:P=>x+i) i).1=(post (fun i:P=>x+i) j).1)) (add_left_cancel (show x+i.2=x+j.2 from congr_arg Prod.snd h))) _).symm
lemma shift_couple (F H:Seed A P R)(x:P): Shift x (couple (field p) F H)=couple (field p) (Shift x F) (Shift x H):= transport_comes (fun i:P=>x+i) (p:=p) F H
lemma trans_shift [AddCommGroup Q](F:Seed A P R)(x:P)(r:P→+Q): transport r (Shift x F)= Shift (r x) (transport r F):= by unfold Shift transport; rw [ferry_trans,ferry_trans]; congr! 2; simp [post,Function.comp_def]

section finite
variable [Fintype P]
def sumHome : Seed A P R→ₗ[R] Seed A P R:=∑ x:P, Shift x
lemma total_uses (F:Seed A P R): sumHome F=∑ x:P, Shift x F:= LinearMap.sum_apply ..
lemma totals (F:Seed A P R)(x:P): sumHome (Shift x F)=sumHome F:= by rw [total_uses,total_uses]; simp_rw [shift_add]; exact Equiv.sum_comp (Equiv.addRight x) (fun x=> Shift x F)
lemma shift_sums (F:Seed A P R)(x:P): Shift x (sumHome F)=sumHome F:= by rw [total_uses,map_sum]; simp_rw [shift_add]; exact Equiv.sum_comp (Equiv.addLeft x) (fun x=> Shift x F)
end finite
end additive
end YM.MS.Cylinder.Lab
