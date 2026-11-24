import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
/-!
# Augment markers to obtain CTA support estimates for ACTUAL test-space-valued μs
 on SAME solver. Arbitrary W→V many-to-one. Ring hom & derivatives of
 generated labels; preserves exact masks. Use source α prices l1 not norm
 equivalence. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Annuncia
open Function Filter Finset YM.Marker Extra.Trajectories
open scoped Matrix.Norms.Frobenius ContDiff BigOperators Topology Classical
variable {V W:Type*}[DecidableEq V][Fintype W][DecidableEq W](u:W→V)(R:Census V)
-- All permitted sensor combos. no predicate beyond fibers being disjoint in images. Caller can factor through sub-prob with other helper.Not allow several in same root.I bound.
structure Admitted (s:Finset W): Prop where
  sector : s.image u∈R.choices
  separate : Set.InjOn u (s : Set W)
 omit [Fintype W] [DecidableEq W] in
lemma slide {s t}(h:Admitted u R s)(ht:t⊆s):Admitted u R t:=⟨R.down h.sector _ (image_subset_image ht),h.separate.mono (by simpa using! ht)⟩

def Replica : Census W where
  choices:= univ.filter (Admitted u R)
  blank:=by rw [mem_filter];exact ⟨mem_univ _,⟨by simp [R.blank],by simp⟩⟩
  solo i:= by rw [mem_filter];exact ⟨mem_univ _,⟨by simp [R.solo],by simp⟩⟩
  down hs _ ht:=by simp only [mem_filter,mem_univ,true_and] at hs ⊢; exact slide u R hs ht
local notation "S"=> Replica u R
namespace Replica
lemma admit (s:(S).Mode): Admitted u R s.val:= (mem_filter.mp s.property).2
def bill (s:(S).Mode):R.Mode:=⟨s.val.image u,(admit u R s).sector⟩
@[simp] lemma blank : bill u R (S).quiet=R.quiet:= by ext1; simp [bill,Census.quiet]
@[simp] lemma that (w:W): bill u R ((S).fire w)=R.fire (u w):=by ext1; simp [bill,Census.fire]
lemma hot (s:(S).Mode): bill u R s=R.quiet ↔ s=(S).quiet:= by simp [bill,Census.quiet,Subtype.ext_iff]
lemma length (s:(S).Mode):(bill u R s).val.card=s.val.card:= card_image_of_injOn (admit u R s).separate

variable {u R}
lemma distant {A B C:(S).Mode}(hz:Poly.merges A B C):Poly.merges (bill u R A) (bill u R B) (bill u R C):=by
 refine ⟨?_, by simp only [bill,← image_union,hz.2]⟩
 rw [disjoint_left]; rintro _ h h'
 obtain ⟨a,ha,rfl⟩:= mem_image.mp (show _∈ A.val.image _ from h)
 obtain ⟨b,hb,ht⟩:=mem_image.mp (show _∈ B.val.image _ from h')
 have he:b=a:=(admit u R C).separate (hz.2 ▸ mem_union_right _ hb) (hz.2 ▸ mem_union_left _ ha) ht
 exact disjoint_left.mp hz.1 ha (he ▸ hb)
lemma owns {A B:(S).Mode}{z:R.Mode} (ht:Poly.merges (bill u R A) (bill u R B) z):∃ K:(S).Mode,Poly.merges A B K∧bill u R K=z:=by
 have hX:Disjoint (A.val.image u) (B.val.image u):=ht.1
 have hD:Disjoint A.val B.val:= disjoint_left.mpr (fun i h hs=> disjoint_left.mp hX (mem_image_of_mem u h) (mem_image_of_mem u hs))
 have hz:(A.val∪B.val).image u=z.val:=by rw [image_union]; exact ht.2
 let H : Admitted u R (A.val∪B.val):=⟨hz ▸ z.property,by
    intro i hi j hj he; change i∈A.val∪B.val at hi;change j∈A.val∪B.val at hj
    rcases mem_union.mp hi with hi|hi <;> rcases mem_union.mp hj with hj|hj
    · exact (admit u R A).separate hi hj he
    · exact False.elim (disjoint_left.mp hX (mem_image_of_mem u hi) (he.symm ▸ mem_image_of_mem u hj))
    · exact False.elim (disjoint_left.mp hX (mem_image_of_mem u hj) (he ▸ mem_image_of_mem u hi))
    exact (admit u R B).separate hi hj he⟩
 exact ⟨⟨A.val∪B.val,mem_filter.mpr ⟨mem_univ _,H⟩⟩,⟨hD,rfl⟩,Subtype.ext hz⟩

variable (u R)
-- Φ on genuine physical labels by gluing given separate linear readings γ(w); arithmetic estimates later perceived. In close window parent cost.WI.SeedH. film.
variable (γ:W→ℂ)
def sign (s:(S).Mode):ℂ:= ∏ j∈s.val,γ j

def absorb (X:Poly S):Poly R:=∑ i:(S).Mode, Poly.send (bill u R i) (sign u R γ i*X.part i)
private lemma scaler(b:R.Mode)(x y:ℂ):Poly.send b (x+y)=Poly.send b x+ Poly.send b y:=by ext i; by_cases he:i=b <;> simp [he]
lemma accepts (X Y:Poly S): absorb u R γ (X+Y)=absorb u R γ X+absorb u R γ Y:=by unfold absorb;simp_rw [Poly.part_plus,mul_add,scaler,sum_add_distrib]
lemma puts(a:(S).Mode)(x:ℂ):absorb u R γ (Poly.send a x)=Poly.send (bill u R a) (sign u R γ a*x):=by
 unfold absorb; rw [sum_eq_single a]; simp
 · intro b _ hb; simp [Poly.part_send,hb]
 simp
lemma one : absorb u R γ 1=1:=by change absorb u R γ (Poly.send (S).quiet 1)=Poly.send R.quiet 1; rw [puts,blank];simp [sign,Census.quiet]
lemma zero: absorb u R γ 0=0:=by simp [absorb]
lemma toScalar(x:ℂ)(f:Poly S):absorb u R γ (x•f)= x • absorb u R γ f:= by
 unfold absorb; ext1 i; simp only [Poly.part_sum,Poly.part_smul,Poly.part_send, Finset.mul_sum]; exact sum_congr rfl fun j _=> by split <;> first | ac_rfl | simp

omit [Fintype W] [DecidableEq W] in
private lemma bang (a b z:R.Mode)(x y:ℂ)(h:Poly.merges a b z):Poly.send a x*Poly.send b y= Poly.send z (x*y):=by
 ext i; change (Poly.prod _ _).part i=_; rw [Poly.cart]; by_cases hh:i=z
 · subst i; simp [h]
 simp only [Poly.part_send,if_neg hh]; exact if_neg fun he=>hh (Subtype.ext (he.2.symm.trans h.2))
omit [Fintype W] [DecidableEq W] in
private lemma void (a b:R.Mode)(x y:ℂ)(h:¬∃ z,Poly.merges a b z):Poly.send a x*Poly.send b y=0:=by
 ext i; change (Poly.prod _ _).part i=_; rw [Poly.cart,if_neg (show ¬Poly.merges a b i from fun h' => h ⟨i,h'⟩)]; rfl

def mouth : Poly S→+* Poly R where
 toFun:=absorb u R γ
 map_zero':=zero u R γ
 map_add':=accepts u R γ
 map_one':=one u R γ
 map_mul' f g:= by
     
    suffices h:∀(a b:(S).Mode)(x y:ℂ),absorb u R γ (Poly.send a x*Poly.send b y)=absorb u R γ (Poly.send a x)*absorb u R γ (Poly.send b y) by
       let A : Poly (Replica u R) →+ Poly R := { toFun:=absorb u R γ, map_zero':=zero u R γ, map_add':=accepts u R γ }
       change A (f*g)=A f*A g; rw [← Poly.studs f,←Poly.studs g]; simp_rw [Finset.sum_mul,Finset.mul_sum,_root_.map_sum,Finset.sum_mul,Finset.mul_sum]; exact sum_congr rfl (fun i _=>sum_congr rfl fun j _=>h i j (f.part i) (g.part j))
    intro a b x y
    rw [puts,puts]
    by_cases he:∃ z,Poly.merges a b z
    · obtain ⟨z,H⟩:=he; rw [bang S _ _ z _ _ H,puts,bang R _ _ (bill u R z) _ _ (distant H)]; congr 1; unfold sign; rw [←H.2,prod_union H.1]; ring
    have hh:¬∃ z,Poly.merges (bill u R a) (bill u R b) z:= fun ⟨z,hz⟩=>by obtain ⟨Zi,H,_⟩:=owns hz; exact he ⟨Zi,H⟩
    rw [void S _ _ _ _ he,void R _ _ _ _ hh,zero]
@[simp] lemma mouth_apply (x:Poly S): mouth u R γ x=absorb u R γ x:=rfl
end Replica
end YM.RG3.Annuncia
