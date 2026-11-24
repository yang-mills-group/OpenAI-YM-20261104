import YM.OPE.Mountains.Assembly
/-!
# Partition off unseen scenery before testing a previously fused product

Here we support the cost of the *remaining* tree, even when every depth
with maximal T has already been contracted. This is used to iterate
flux pricing without any hypothesis on how many leading sizes the repairs
may cost after such redactions (removing a redaction changes even the
`relative rate` of all the other scales).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Real OPE.Log
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {I J K:Type}[Fintype I][Fintype K]{s:Arboreal I}{a:Finset I}(h:s.Active a){φ:Ultrafilter J}
    {t:I→ℝ} {X:I→ E4}{R':I→ℝ} {M δ:ℝ}{x:J→I→E4}{R:J→I→ℝ}
namespace Active
-- patch & live projection
abbrev Patch (s:Arboreal I)(a:Finset I):Type:= (↑(a∪s.live a):Type)
section
local notation "I'"=> Patch s a
include h
private lemma par_mem (i:I'): s.parent i.val ∈a:= (mem_union.mp i.property).elim (fun hi=> h.parent hi) (fun hi=> (s.live_iff ..|>.1 hi).2)
-- shrink
noncomputable def restrict : Arboreal (Patch s a) where
    root := ⟨s.root, mem_union_left _ h.main⟩
    depth i:= s.depth i.val
    parent i:= ⟨s.parent i.val, mem_union_left _ (par_mem h i)⟩
    zones:= univ.filter fun i=> i.val∈a
    step i hi:= s.step _ (Subtype.val_injective.ne hi)
    direct:= Subtype.ext s.direct
    inward i:= mem_filter.mpr ⟨mem_univ _,par_mem h i⟩
-- avoid notation across binder
local notation "V"=> h.restrict
lemma step_val (i : I'): ((V).parent i).val = s.parent i.val:= rfl
lemma root_val : (V).root.val = s.root:=rfl
lemma zones_val (i:I'): i∈(V).zones↔ i.val ∈a:=by change _ ∈ univ.filter _ ↔_; simp
omit h
private lemma middle_mem {I:Type}(s:Arboreal I)(a:Finset I)(i:I): i∈ s.middle a↔ i≠ s.root∧ i∈a:= mem_erase
include h
lemma middle_val (i:I'): i∈ (V).middle (V).zones↔ i.val∈ s.middle a:= by rw [middle_mem,middle_mem,zones_val]; refine and_congr (not_congr ?_) Iff.rfl; exact ⟨fun hi=> hi ▸ rfl,fun hi=>Subtype.ext hi⟩
lemma leaf_val (i:I'): i∈ (V).leaves ↔ i.val∈ s.live a:= by
    rw [(V).leaves_are i, zones_val]; refine ⟨fun hi=> (mem_union.mp i.property).resolve_left hi,fun hi=> (s.live_iff ..|>.1 hi).1⟩ -- h'? remove

def sprout : (↑(V|>.leaves):Type)≃(↑(s.live a):Type):=⟨fun i=> ⟨i.val.val,(leaf_val h i.val).1 i.property⟩,fun i=> ⟨⟨i.val, mem_union_right a i.property⟩,(leaf_val h _).2 i.property⟩,fun _=> rfl,fun _=> rfl⟩
private def houseKeys : (↑(V|>.zones):Type) ≃ (↑a:Type):=⟨fun i=> ⟨i.val.val,(zones_val h i.val).1 i.property⟩,fun i=> ⟨⟨i.val, mem_union_left _ i.property⟩,(zones_val h _).2 i.property⟩,fun _=> rfl,fun _=> rfl⟩
private def balcony : (↑((V).middle (V).zones):Type) ≃ (↑(s.middle a):Type):= ⟨fun i=>⟨i.val.val,(middle_val h i.val).1 i.property⟩,fun i=>⟨⟨i.val, mem_union_left _ (mem_erase.mp i.property).2⟩,(middle_val h _).2 i.property⟩,fun _=>rfl,fun _=>rfl⟩

lemma anc_deep (i j:I')(hp:(V).Anc i j): s.Anc i.val j.val:=by
    have he(n:ℕ)(i : I') : ((V).parent^[n] i).val = s.parent^[n] i.val:=by induction n with
    | zero=>rfl
    | succ n ih=>rw [iterate_succ_apply',iterate_succ_apply',step_val,ih]
    obtain ⟨n,rfl⟩:=hp; exact ⟨n,(he n j).symm⟩
lemma children_deep (i j:I')(hp:j∈(V).kids i) : j.val∈ s.kids i.val:=by obtain ⟨hv,hi⟩:= (V|>.related i j).1 hp; exact (s.related ..).2 ⟨Subtype.val_injective.ne hv, congr_arg Subtype.val hi⟩ -- |> priority parse fix
lemma fork_deep (i j k:I')(hp:(V).Fork i j k): s.Fork i.val j.val k.val:=by
    obtain ⟨a,ha,b,hb,he,hk,hk'⟩:=hp; exact ⟨a.val,h.children_deep i a ha,b.val,h.children_deep i b hb,Subtype.val_injective.ne he,h.anc_deep a j hk,h.anc_deep b k hk'⟩

lemma number : (V|>.zones.card)=a.card:= by
    simpa using (Fintype.card_congr (houseKeys h))
abbrev restrictedFn {L:Type*} (h:s.Active a) (f:I→L): Patch s a→L:= fun i=> f i.val
lemma shrink (hp:s.Convoy M δ R' X): (V).Convoy M δ (h.restrictedFn R') (h.restrictedFn X):=
    ⟨⟨fun i hi=> hp.sizes.allowed _ (h.included ((h.zones_val i).1 hi)),fun i hi=>hp.sizes.coarser _ (h.included ((h.zones_val i).1 hi))⟩,fun i=> hp.travel i.val,fun i j k he=> hp.spread _ _ _ (fork_deep h i j k he)⟩ -- .. parser
lemma smallerT (he:s.Graduated R'): (V).fullLife (h.restrictedFn R') ≤ s.fullLife R':=by
    let T:= fun i=> run (R' i); let t(i:I):= s.stepAt T i; let t'(i:I'):= (V).stepAt (restrictedFn h T) i; let v:= s.middle a; let u:= (V).middle (V).zones; change (∑ i∈u, t' i)+T s.root ≤ (∑ i∈ _,t i)+T s.root
    refine add_le_add (le_trans (le_of_eq (b:=∑ i∈v,t i) ?_) (sum_le_sum_of_subset_of_nonneg (erase_subset_erase _ h.included) (fun i hi _=> he.life (mem_erase.mp hi).2))) le_rfl; rw [← sum_coe_sort u t',← sum_coe_sort v t]; exact (Equiv.sum_comp (balcony h) (fun i:(↑v:Type)=> t i.val))

variable (hv:s.Coterie (φ:Filter J) t M δ x R)
include hv
lemma stay : ∃ t', (V).Coterie (φ:Filter J) t' M δ (fun i=>restrictedFn h (x i)) (fun i=>restrictedFn h (R i)):=by
    let Y i:= restrictedFn h (x i); let r i:=restrictedFn h (R i); have he:(∀ᶠ i in (φ:Filter J),(V).Convoy M δ (r i) (Y i)):=hv.space.mono fun i hi=> shrink h hi; have hk:Tendsto (fun i=> r i (V).root) (φ:Filter J) (𝓝[>]0):= hv.collapse; obtain ⟨g,hg,hG,t',h'⟩:= phase_rates (he.mono fun i hi=>hi.sizes) hk; exact ⟨t',he,hv.cap,hv.keep,φ.unique hg ▸ h',hk⟩ -- include hv

-- observe & truncate rent
omit hv
variable {G:Gauge}{C: Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)(P:Prescription U.sector.derivatives)
    (n:ℕ)(p:I→ C.book.Token)
lemma per_fee (R:I→ℝ) : (V).fee (h.restrictedFn p) (h.restrictedFn R) ((V).leaves) ((V).root) n = s.fee p R (s.live a) s.root n:=by
    unfold fee rent; congr 1; let f(i:I'):= h.restrictedFn R ((V).parent i)^((h.restrictedFn p) i).1; let g(i:I):= R (s.parent i)^(p i).1; change (∏ i∈ (V).leaves,f i)=∏ i∈ s.live a,g i; rw [← prod_coe_sort (V).leaves f,← prod_coe_sort (s.live a) g]; exact Equiv.prod_comp (sprout h) (fun i:(↑(s.live a):Type)=> g i.val)
-- prove on any two position name systems first
omit h
private lemma prune {I J:Type}[Fintype I][Fintype J](k:Viewers U) (X:I→E4) (q:K→ C.book.Token)(y:K→ E4)(o:E4)(p:I→ C.book.Token)(e:J≃I)(hi:Injective (beside X y)) :
    observe (spectator U k) (beside (X ∘ e) y) (beside (p ∘ e) q) - P.truncated (spectator U k) n (X ∘ e) (p ∘ e) o y q= observe (spectator U k) (beside X y) (beside p q)-P.truncated (spectator U k) n X p o y q:=by
    unfold Prescription.truncated Prescription.termRead; simp_rw [P.coefficient_perm _ U.room.kernel.laws.toSymmetric]; let Z:=Equiv.sumCongr e (Equiv.refl K); congr 1; rw [show beside (X ∘ e) y =beside X y ∘ Z from funext fun i=> by rcases i with i|i <;> rfl,show beside (p ∘ e) q=beside p q ∘ Z from funext fun i=> by cases i<;> rfl]; exact perm_observe _ (spectate U k).laws.toSymmetric Z (beside p q) hi
include h
lemma shine (k:Viewers U)(X:I→ E4)(q:K→ C.book.Token)(y:K→E4)(hi:Injective (beside (crop X (s.live a)) y)) : flux P (spectator U k) (V|>.leaves) (restrictedFn h X) (restrictedFn h p) (V|>.root) y q n = flux P (spectator U k) (s.live a) X p s.root y q n:=by
    exact prune U P n k (crop X (s.live a)) q y (X s.root) (crop p (s.live a)) (sprout h) hi

end
end Active
end YM.OPE.Arboreal
