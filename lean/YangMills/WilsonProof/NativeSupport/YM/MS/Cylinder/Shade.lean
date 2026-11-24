import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Dwells

/-!
# Test a cylinder polynomial on arbitrary momentum or color lists

Evaluate the derivative coefficients. Parity grading matters under products. No factorial.
   Also support picky rows (to discrete stencil output); this also works with ghosts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Set Finset Koszul
variable {R A B : Type*} [CommRing R] {p : Sector A} {q : Sector B} {F H u v:Raw A R}
variable (T : B→A→R) {s s' : Finset A}
def lit (s:Finset A) (T:B→A→R) : Raw A R → List B → R
 | f, []=> f []
 | f, j::l=> ∑ i∈s, T j i*lit s T (D i f) l

def lantern (s:Finset A) (T:B→A→R): Raw A R→ₗ[R] Raw B R where
   toFun := lit s T
   map_add' := by
     intro x y; funext l; induction l generalizing x y with
     | nil=>rfl
     | cons a l ih=> simp only [lit,map_add, Pi.add_apply,ih,mul_add, Finset.sum_add_distrib]
   map_smul' := by
     intro c x; funext l; induction l generalizing x with
     | nil=>rfl
     | cons a l ih=> simp only [lit,map_smul,Pi.smul_apply, RingHom.id_apply,ih,smul_eq_mul,Finset.mul_sum,mul_left_comm c]
@[simp] lemma lantern_nil (f:Raw A R): lantern s T f []=f []:= rfl
lemma lantern_drop (j:B) (f : Raw A R): D j (lantern s T f) = ∑ i∈s,T j i • lantern s T (D i f):= by
    ext l; rw [at_D,Finset.sum_apply]; exact lit.eq_2 ..
lemma enlarge (F:Cyl A R) (hs:Uses (s:Set A) F.val)(he:s⊆s'): lantern s T F.val=lantern s' T F.val:= by
    ext l; induction l generalizing F with
    | nil=> simp
    | cons j l ih=>
        rw [D_eval j (lantern s T _),D_eval j (lantern s' T _), lantern_drop,lantern_drop,Finset.sum_apply,Finset.sum_apply]
        refine Eq.trans (Finset.sum_congr rfl (fun i _=> ?_)) (Finset.sum_subset he (fun i h hx=>?_))
        · change (T j i) • (lantern s T (enter i F).val l)= _
          rw [ih (enter i F) (hs.drop i)]; rfl
        simp [hs.off (show i∉(s:Set A) from hx)]
lemma art (F:Cyl A R) (hs:Uses (s:Set A) F.val)(he:Uses (s':Set A) F.val) : lantern s T F.val=lantern s' T F.val:= by classical exact (enlarge T F hs (Finset.subset_union_left (s₂:=s'))).trans (enlarge T F he Finset.subset_union_right).symm

def fuel (F:Cyl A R) : Finset A := (fromCyl F).choose
def lamp (T:B→A→R) (F:Cyl A R):= lantern (fuel F) T F.val
lemma lamp_at (F:Cyl A R)(h:Uses (s:Set A) F.val): lamp T F=lantern s T F.val:= art T F ((fromCyl F).choose_spec) h

def shade (T:B→A→R): Cyl A R→ₗ[R] Raw B R where
   toFun:= lamp T
   map_add' f g:= by obtain ⟨s,hs,hg⟩:= encloses f g; rw [lamp_at T (f+g) (hs.add hg), lamp_at T f hs, lamp_at T g hg,add_stack,map_add]
   map_smul' c f:= by obtain ⟨s,hs⟩:=fromCyl f; rw [lamp_at T f hs,lamp_at T (c • f) (hs.smul c),smul_stack,map_smul]; rfl
lemma tinted (F:Cyl A R) (h:Uses (s:Set A) F.val) : shade T F=lantern s T F.val:= lamp_at T F h
@[simp] lemma shade_nil (F:Cyl A R) : shade T F []=F.val []:= rfl
lemma shade_drop (j:B) (F:Cyl A R)(h:Uses (s:Set A) F.val): D j (shade T F)= ∑ i∈s,T j i • shade T (enter i F):= by
     rw [tinted T F h,lantern_drop]; exact Finset.sum_congr rfl (fun i _=> by rw [tinted T (enter i F) (h.drop _)]; rfl)
lemma deriv_lum (j:B) (F:Cyl A R)(h:Uses (s:Set A) F.val) l: shade T F (j::l)=∑ i∈s,T j i * shade T (enter i F) l:= by rw [D_eval j (shade T F), shade_drop T j F h,Finset.sum_apply]; rfl
lemma shade_hooks (j:B) (F:Cyl A R)(h:Uses (s:Set A) F.val): D j (shade T F)= shade T (∑ i∈s,T j i • enter i F):= by rw [shade_drop T j F h]; simp

variable {T}
def Tie (p:Sector A)(q:Sector B)(T:B→A→R): Prop:=∀ i j,T j i≠0→ p i=q j
namespace Tie
variable (HT : Tie p q T)
include HT
-- Symm and Pure even. Keep rank charges later.
lemma commute (F:Cyl A R) (x:Bool): shade T (twisted p x F)= sign q x (shade T F):= by
   funext l; induction l generalizing F with
   | nil=> simp
   | cons j l ih=>
     obtain ⟨s,hs⟩:=fromCyl F
     have he i : enter i (twisted p x F)=(cross x (p i):R) • twisted p x (enter i F):= Subtype.ext (sign_D p x i _)
     simp only [at_sign,deriv_lum T j F hs]; rw [deriv_lum T j _ (hs.sign x),Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=> ?_)
     by_cases hv:T j i=0; simp [hv]
     rw [he,map_smul,Pi.smul_apply,smul_eq_mul,ih, at_sign,HT _ _ hv,degree_cons,cross_right]; ring
lemma pure {b:Bool} (F:Cyl A R)(h:Pure p b F.val): Pure q b (shade T F):= by
   intro l he; induction l generalizing b F with
   | nil=> rw [shade_nil T]; exact h [] he
   | cons j l ih=>
       obtain ⟨s,hs⟩:=fromCyl F; rw [deriv_lum T j F hs]; apply Finset.sum_eq_zero; intro i hi; by_cases hv:T j i=0; simp [hv]; rw [ih (enter i F) (h.drop i) ?_,mul_zero]
       rw [HT _ _ hv]; revert he; simp only [degree_cons]; cases b <;> cases hq:q j <;> cases hb:degree q l <;> simp
lemma sym (F:Cyl A R) (h:Symm p F.val): Symm q (shade T F):= by
    intro l i j r; induction l generalizing F with
    | nil=>
       obtain ⟨s,hs⟩:=fromCyl F
       have he z (y:B) : D z (D y (shade T F))=∑ a∈s, ∑ b∈s, ((T y a)*(T z b)) • shade T (enter b (enter a F)) := by rw [shade_drop T y _ hs]; simp_rw [map_sum,map_smul,shade_drop T z (enter _ F) (hs.drop _),Finset.smul_sum, smul_smul]
       have H (a b:A) : enter a (enter b F)=(cross (p b) (p a):R) • enter b (enter a F):= Subtype.ext (h.commute a b)
       suffices D j (D i (shade T F))=(cross (q i) (q j):R) • D i (D j (shade T F)) from congr_fun this r
       rw [he,he,Finset.sum_comm]; simp_rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_
       by_cases h1:T i b=0; simp [h1]; by_cases h2:T j a=0; simp [h2]; rw [H,map_smul,HT _ _ h1,HT _ _ h2,mul_comm (T i b),smul_comm]
    | cons x l ih=>
       obtain ⟨s,hs⟩:=fromCyl F; simp only [List.cons_append, deriv_lum T x F hs,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; rw [ih _ (h.drop k)]; ring
lemma prod (F H:Cyl A R): shade T (couple p F H)= product q (shade T F) (shade T H):= by
    funext l; induction l generalizing F H with
    | nil=> simp
    | cons x l ih=>
       obtain ⟨s,hK,hH⟩:= encloses F H
       rw [D_eval x (shade T _),D_eval x (product q _ _), D_product, shade_drop T _ _ hK, shade_drop T _ _ hH,shade_drop T _ _ (hK.pair hH),map_sum,map_sum]
       simp only [map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,couple_diff,map_add]
       rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=> ?_)
       by_cases hv:T x i=0; simp [hv]; rw [HT _ _ hv,ih,ih,HT.commute]; simp [mul_add]
end Tie

def Slim (T:B→A→R):= ∀ i:A, (support (fun b=> T b i)).Finite
namespace Slim
variable (HT:Slim T)
include HT
omit HT in
lemma stretch (F:Cyl A R) {s: Set A}{t:Set B} (hs:Uses s F.val)(hh:∀ i∈s,(support (fun b=> T b i))⊆t): Uses t (shade T F) := by
    intro l i hi hu; induction l generalizing F with
    | nil=> exact (List.not_mem_nil hi).elim
    | cons j l ih=>
        obtain ⟨S,hS⟩:=fromCyl F; rcases List.mem_cons.mp hi with hv|hv<;> rw [deriv_lum T j F hS]; swap
        · apply Finset.sum_eq_zero; intro i' _; rw [ih (enter i' F) (hs.drop _) hv, mul_zero] -- he ordering?
        subst j; refine Finset.sum_eq_zero fun a _=> ?_
        by_cases hx:T i a=0; simp [hx]
        have he: a ∉ s:= fun hi =>hu (hh a hi hx)
        rw [notEnter _ hs a he,map_zero,Pi.zero_apply,mul_zero] -- Pi.zero_apply
lemma reaches (F:Cyl A R): shade T F ∈ Stack B R:= by
    obtain ⟨s,hs⟩:=fromCyl F; let t:= ⋃ i∈s, (support (fun b=> T b i)); have ht : t.Finite:= s.finite_toSet.biUnion (fun i _=> HT i)
    refine ⟨ht.toFinset,?_⟩; rw [ht.coe_toFinset]; exact stretch (T:=T) F hs fun i hi=> Set.subset_iUnion_of_subset i ((Set.subset_iUnion (fun _:i∈s=> support (fun b=> T b i)) (show i∈s from hi)))

def arrive (T:B→A→R) (h:Slim T): Cyl A R →ₗ[R] Cyl B R:= (shade T).codRestrict (Stack B R) h.reaches
@[simp] lemma lands (F:Cyl A R) : (arrive T HT F).val=shade T F:=rfl
lemma drop (j:B) (F:Cyl A R)(h:Uses (s:Set A) F.val): enter j (arrive T HT F)= arrive T HT (∑ i∈s,T j i • enter i F):= Subtype.ext (shade_hooks T j F h)
lemma twists (HQ:Tie p q T)(c:Bool)(F:Cyl A R): arrive T HT (twisted p c F)= twisted q c (arrive T HT F):=Subtype.ext (HQ.commute F _)
lemma connect (HQ:Tie p q T)(F H:Cyl A R): arrive T HT (couple p F H)=couple q (arrive T HT F) (arrive T HT H):=Subtype.ext (HQ.prod ..)
end Slim
end YM.MS.Cylinder
