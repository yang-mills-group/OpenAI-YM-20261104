import YM.Frontier6.Bouquet.Meter.Separate

/-! The proper-stratum component and isolated coincidence component at one root.
 In this **finite-length regularized calculation**. Their algebra travels through
 all supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble} (i:P)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
    (x: Seats P) (H:Patron S P Y) (f:Full (fiber P))
def proper (P:Ensemble)(p:Pod) : Finset (Down P):= Finset.univ.filter fun j=>p∉ j.val.choose
def coin (P: Ensemble)(p: Pod): Finset (Down P):= Finset.univ.filter fun j=>p∈ j.val.choose
def lonely (P:Ensemble): Down P:= ⟨_,le_refl P⟩
def pollen := select K A T (proper P i.val) x H f
def marble := select K A T (coin P i.val) x H f
lemma splitting : regulator K A T x H f=pollen K A T i x H f + marble K A T i x H f:=by
   have he: Disjoint (proper P i.val) (coin P i.val):= Finset.disjoint_left.mpr (fun j a b=>(Finset.mem_filter.mp a).2 (Finset.mem_filter.mp b).2)
   have ht: proper P i.val ∪ coin P i.val= Finset.univ:=by ext1 a; by_cases h:i.val∈ a.val.choose <;> simp [proper,coin,h]
   unfold regulator pollen marble select; rw [← Finset.sum_union he,ht]
lemma different_prog (h:Q≤P) (he:i.val∉ Q.choose) (hf:∀ z∈tsupport f,Separate h z): marble K A T i x H f=0:=by
   unfold marble select; exact Finset.sum_eq_zero (fun p hp=> absent_choice K A T h i.property he hf p.property (Finset.mem_filter.mp hp).2 x)
section
variable (h:Free P Q) (p:Down P × Down Q)
lemma pod_left : i.val∈ (twine h p).val.choose ↔ i.val∈ p.1.val.choose:=by rw [twins,Finset.mem_union]; apply or_iff_left_of_imp; intro he; obtain ⟨q,hq,H⟩:= p.2.property.2 i.val he; exact False.elim (i.val.not_disjoint ((h.separate i.val q i.property hq).mono_right H))
lemma pocket_flags (U:Finset (Down P))(A':Finset (Down (merge h)))(H:∀ p, (twine h p)∈ A' ↔ p.1∈U): Curtains.onLeft h U=A':=by
    let e:=twineEquiv h; ext1 y; obtain ⟨⟨p,q⟩,rfl⟩:= e.surjective y; change twine h (p,q)∈ onLeft h U ↔ twine h (p,q)∈A'; rw [H (p,q)]
    unfold onLeft; -- product
    constructor
    · intro he; obtain ⟨u,hu,h⟩:= Finset.mem_map.mp he; exact e.injective h ▸ (mem_product.mp hu).1 -- check
    intro hh; exact Finset.mem_map.mpr ⟨_,mem_product.mpr ⟨hh,Finset.mem_univ _⟩,rfl⟩
lemma pocket_proper : proper (merge h) i.val= onLeft h (proper P i.val):=by symm; apply pocket_flags h; intro p; simp [proper,pod_left i h p]
lemma pocket_coin : coin (merge h) i.val= onLeft h (coin P i.val):=by symm; apply pocket_flags h; intro p; simp [coin,pod_left i h p]
end
section
variable (p:Pod)
lemma coin_alone : coin (only p) p= {lonely (only p)}:=by
   ext1 i; unfold coin; rw [Finset.mem_filter, Finset.mem_singleton]; constructor
   · intro hi; apply Subtype.ext; apply le_antisymm i.property; exact ⟨(ref_slots i.property).symm,fun q h=>⟨p,hi.2,(only_mem.mp h).le⟩⟩
   rintro rfl; exact ⟨Finset.mem_univ _, Finset.mem_singleton_self p⟩
lemma marble_one (i:only p)(u:Seats (only p))(X: Patron S (only p) Y)(f:Full (fiber (only p))): marble K A T i u X f= branch K A T le_rfl u X f:=by
    unfold marble select; rw [only_mem.mp i.property,coin_alone, Finset.sum_singleton]; rfl
end
end YM.Frontier6.Bouquet
