import YM.OPE.Compatible.Assemblage.Preserved
/-!
Global spices on slots on singleton fibers can be factored out of the
purchase. Also the linear surgery identifies non-solo slots with
heavier branches only after all partners there have grown.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG
open scoped Topology BigOperators Classical
variable {V I J A : Type} [DecidableEq V] [DecidableEq A][Fintype V][Fintype A]
    (L:Fibers A V) {v:V}(hv:L.SingleFiber v)
include hv
lemma led_mul (b : (Bud A).Mode)(w:(Bud V).Mode) : Poly.merges ((Bud A).fire (L.twig v)) b (L.plena w) ↔
    ∃ x:(Bud V).Mode, Poly.merges ((Bud V).fire v) x w ∧ b=L.plena x:=by
    constructor
    · rintro ⟨hx,ht⟩; have hV: L.twig v∉b.val:= by apply Finset.disjoint_singleton_left.mp hx
      have hu:v∈w.val:=by rw [← L.sectioned v,← L.reaped]; rw [← ht]; exact mem_union_left _ (mem_singleton_self _)
      let x:(Bud V).Mode:= ⟨w.val.erase v, mem_univ _⟩
      refine ⟨x,⟨Finset.disjoint_singleton_left.mpr (notMem_erase v w.val),?_⟩,Subtype.ext ?_⟩
      · change {v}∪w.val.erase v=w.val; ext i; simp only [mem_union,mem_singleton,mem_erase]; constructor; rintro (rfl|⟨-,hh⟩); exact hu; exact hh
        intro h; exact or_iff_not_imp_left.mpr (fun he=>⟨he,h⟩)
      ext a; rw [L.reaped,show x.val=w.val.erase v from rfl,mem_erase, ne_eq,L.sola _ hv]; constructor
      · intro h; exact ⟨fun he=>hV (he ▸ h),(L.reaped ..).mp (ht ▸ mem_union_right _ h)⟩
      rintro ⟨h,hh⟩; exact (mem_union.mp (ht.symm ▸ (L.reaped ..).mpr hh)).resolve_left (mt mem_singleton.mp h)
    rintro ⟨x,⟨hx,hq⟩,rfl⟩; refine ⟨Finset.disjoint_singleton_left.mpr (by rw [L.reaped,L.sectioned]; exact Finset.disjoint_singleton_left.mp hx),?_⟩
    ext a; rw [mem_union,L.reaped,L.reaped,← hq,mem_union]; exact or_congr (by rw [show ((Bud A).fire _).val={_} from rfl,show ((Bud V).fire _).val={_} from rfl,mem_singleton,mem_singleton,L.sola _ hv]) Iff.rfl
lemma repro (r : ℂ) (p:Poly (Bud A)) : reap L (Poly.send ((Bud A).fire (L.twig v)) r*p)=Poly.send ((Bud V).fire v) r*reap L p := by
    ext1 w
    have he{U:Type} [DecidableEq U] [Fintype U](q:(Bud U).Mode) (v:(Bud U).Mode)(p: Poly (Bud U)) : (Poly.send v r * p).part q=∑ b:(Bud U).Mode,if Poly.merges v b q then r*p.part b else 0:=by
       rw [Poly.part_mul,sum_eq_single v]; simp only [Poly.part_send,if_true]
       intro i _ h; simp [h]
       simp
    change (Poly.send _ r*p).part (L.plena w)= _; rw [he,he]
    let Z := fun b => (if Poly.merges ((Bud A).fire (L.twig v)) b (L.plena w) then r*p.part b else 0)
    have hp: Injective L.plena:= (show LeftInverse L.span L.plena from L.reband).injective
    trans ∑ b:(Bud V).Mode,Z (L.plena b)
    · rw [← Finset.sum_image hp.injOn]; refine (Finset.sum_subset (subset_univ _) (fun i _ hi=> ?_) : ∑ b∈ univ.image L.plena,Z b= ∑ b,Z b).symm
      apply if_neg (fun hh=>?_)
      obtain ⟨v,-,hh⟩:= (L.led_mul hv i w).1 hh; exact hi (hh.symm ▸ mem_image_of_mem L.plena (mem_univ v))
    refine sum_congr rfl fun i _=>?_
    have hf:Poly.merges ((Bud A).fire (L.twig v)) (L.plena i) (L.plena w) ↔ Poly.merges ((Bud V).fire v) i w:=by
       rw [L.led_mul hv]; exact ⟨fun ⟨j,h,h'⟩=> hp h'|>.symm ▸ h,fun h=>⟨_,h,rfl⟩⟩
    unfold Z; rw [if_congr hf rfl (rfl : (0:ℂ)=0)]; rfl

omit hv
lemma mach_add {p q:A→ℂ} : Mach (Bud A) (p+q)=Mach (Bud A) p+Mach (Bud A) q:=by simp only [Mach,Pi.add_apply,Extra.Trajectories.send_add,Finset.sum_add_distrib]
def bypass (p:A→ℂ)(v:V):= if L.SingleFiber v then p (L.twig v) else 0
def divert (p:A→ℂ):A→ℂ:= L.bypass p ∘ L.bunch
def shade (p:A→ℂ): A→ℂ:= p-L.divert p
lemma march_mach (p:A→ℂ)(f:Poly (Bud A)): reap L (Poly.pass (Mach (Bud A) (L.divert p))*f) =
    Poly.pass (Mach (Bud V) (L.bypass p))*reap L f:=by
    let J := univ.filter (L.SingleFiber)
    let x(b:V):=Poly.send ((Bud A).fire (L.twig b)) (p (L.twig b)); let y(b:V):=Poly.send ((Bud V).fire b) (p (L.twig b))
    have he: Mach (Bud A) (L.divert p)=∑ b∈J, x b:=by
       unfold Mach; rw [← Finset.sum_subset (subset_univ (J.image L.twig)) (fun i _ hi=>?_),sum_image L.sectioned.injective.injOn]; exact sum_congr rfl fun i hi=>by rw [divert, comp_apply,L.sectioned, bypass,if_pos (mem_filter.mp hi).2]
       unfold divert bypass; simp only [comp_apply]; split
       next he=> exact (hi ((L.sola _ he i).1 rfl|>.symm ▸ mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,he⟩))).elim
       exact Poly.send_zero ..
    have hz: Mach (Bud V) (L.bypass p)=∑ b∈J,y b:=by
       unfold Mach; rw [← Finset.sum_subset (subset_univ J) (fun i _ hi=>?_)]; exact sum_congr rfl fun i hi=>by rw [bypass,if_pos (mem_filter.mp hi).2]
       exact (congr_arg (Poly.send _) (if_neg (fun h=>hi (mem_filter.mpr ⟨mem_univ _,h⟩)))).trans (Poly.send_zero _)
    rw [he,hz]; -- pass sum finite of distinct? `pass_sum`
    have h (j) : ((Bud A).fire (L.twig j)).val.Nonempty:= singleton_nonempty _
    have h' j: ((Bud V).fire j).val.Nonempty := singleton_nonempty _
    suffices H : ∀ S:Finset V,S⊆J→ reap L ((∏ i∈S, (1+x i))*f)=(∏ i∈S,(1+y i))*reap L f by
       rw [pass_sum,pass_sum]; exact H J (Subset.refl _)
       exact fun _ _=>h' _
       exact fun _ _=> h _
    intro S; induction S using Finset.induction_on with
    | empty=> simp
    | @insert i S hi ih=>
       intro hh; let g : Poly (Bud A) := (∏ i∈S,(1+x i))*f
       have hp: reap L g=_:= ih (subset_trans (Finset.subset_insert ..) hh)
       rw [prod_insert hi,prod_insert hi,mul_assoc]; change reap L ((1+x i)*g)=_; rw [add_mul,one_mul,map_add,L.repro ((mem_filter.mp (hh (mem_insert_self ..))).2),hp,mul_assoc (1+_),add_mul,one_mul]; -- unfold x
end YM.MergeProof.Ribbons.Fibers
