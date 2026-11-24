import YM.OPE.Compatible.Copper.Watch
/-!
# Register at rooted & peeled words. Use canonical slots in both cases not competing peripheral labels.
Also sends assumed old projection comparison for each leaf individually. No constancy across refinements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F:Finset X}{m j s':X→ℕ}
    {G:Gauge}{C:Family G}{L:Extraction.Order}{A:Allot C}
variable (p:X→ C.book.Token)(u:X)(hp:Crown U)(hu:u∈rest U)
variable (y:X→ Cover){v:brim D U→ C.book.Token} {S:Table C.book}
set_option quotPrecheck false
local notation "U*"=>Arboreal.trim U u
local notation "I'"=>brim D U
local notation "J"=>glen D U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=> shore D U u
lemma cove_prod {B:Type}[CommMonoid B](f:V→ B)(g:I'→B)(y:J→B)(hv:∀ x:V, g ((forks D U u) (.inr x))=f x)(hy:∀ x:J, g ((forks D U u) (.inl x))=y x):
   (∏ i∈ cove D U u,g i)=∏ i,y i∧ (∏ i∈univ\cove D U u,g i)=∏ i,f i:=by
   let P:=forks D U u; let Q:J→ I':= P ∘ Sum.inl; let Z: V→ I':=P ∘ Sum.inr
   have h:univ.image Q=cove D U u:=by
       ext i; rw [cove,mem_filter,mem_image, and_iff_right (mem_univ _)]
       constructor
       · rintro ⟨j,_,rfl⟩; exact (Finset.mem_filter.mp j.2).2
       intro hi; exact ⟨⟨_,Finset.mem_filter.mpr ⟨i.2,hi⟩⟩,mem_univ _,Subtype.ext rfl⟩
   have h':univ.image Z=univ\cove D U u:=by
       ext i;  rw [Finset.mem_sdiff,cove,Finset.mem_filter]; simp only [  mem_image, mem_univ,true_and]
       constructor
       · rintro ⟨j,rfl⟩; exact (Finset.mem_filter.mp j.2).2
       intro hi; exact ⟨⟨_,Finset.mem_filter.mpr ⟨i.2,hi⟩⟩,Subtype.ext rfl⟩
   constructor
   · rw [← h, Finset.prod_image (P.injective.comp Sum.inl_injective|>.injOn)]
     exact prod_congr rfl (fun i _=> hy i)
   rw [← h',Finset.prod_image (P.injective.comp Sum.inr_injective|>.injOn)]
   exact prod_congr rfl fun i _=> hv i
-- match with ALL X p : To choose p' extending picked, use override via fix. z and p' must keep p used at center? will paint
variable {W J₀ k n N r d e:ℕ}{a:C.label d}{t:C.label e}
    (g:ℕ×ℕ→ C.label d)
local notation "p₀"=>picked I' p
local notation "p₁"=> fun a':C.label d=> picked H (update p u (⟨d,a'⟩:C.book.Token))
variable (a)
-- param indexing on all X, defined by ite for type-cast
def poleRead (x:X): ℕ×ℕ→ C.label ((update p u (⟨d,a⟩: C.book.Token) x).1):= if h:x=u then ((show C.label d=C.label ((update p u (⟨d,a⟩: C.book.Token) x).1) from by rw [h, update_self]) ▸ g) else fun _=>(update p u (⟨d,a⟩: C.book.Token) x).2
def polesAt (F:Finset X) : ReadLabel C (picked F (update p u (⟨d,a⟩: C.book.Token))):= fun x=> poleRead p u a g x.val
private lemma limit_cast (v v':C.book.Token)(he:v=v'){f:Filter I}(g:I→ C.label v.1)(hg:Tendsto g f (𝓝 v.2)): Tendsto (Eq.rec (motive:=fun x _=> I → x) g (show C.label v.1=C.label v'.1 from congr_arg C.label (congr_arg Sigma.fst he))) f (𝓝 v'.2):=by subst v'; exact hg
private lemma charge_cast (w v:ℕ)(he:w=v)(g:ℕ×ℕ→ C.label w)(z₀:Site (C.side N r))(x:Config G (C.side N r)) : C.O N r (( (Eq.rec (motive:=fun X _=>_ → X) g (show C.label w=C.label v from congr_arg C.label he)):ℕ×ℕ→ C.label v) (N,r)) z₀ x= C.O N r (g (N,r)) z₀ x:=by subst v; rfl
omit [PartialOrder X][OrderBot X][Fintype X] in
private lemma pole_stop {φ:Filter (ℕ×ℕ)}(h:Tendsto g φ (𝓝 a))(i:X): Tendsto (poleRead p u a g i) φ (𝓝 (update p u (⟨d,a⟩:C.book.Token) i).2):=by
    by_cases e:i=u; swap; · unfold poleRead; rw [dif_neg e]; exact tendsto_const_nhds
    subst i; unfold poleRead; rw [dif_pos rfl]; exact limit_cast (C:=C) (⟨d,a⟩:C.book.Token) _ (update_self u _ p|>.symm) _ h
omit [PartialOrder X][OrderBot X][Fintype X] in
lemma poles_tend (F:Finset X){φ:Filter (ℕ×ℕ)}(h:Tendsto g φ (𝓝 a))(i:F): Tendsto (polesAt p u a g F i) φ (𝓝 (picked F (update p u (⟨d,a⟩: C.book.Token)) i).2):= pole_stop p u a g h i.val
local notation "F!"=> fun i:X=>Cells.location C.S W N r (y i)
local notation "S!"=> fun i:X=>Cells.location C.S W N r (y i-y u)
local notation "v'"=>polesAt p u a g H
local notation "ρ"=> (Cards.register C W)
lemma collective : (ρ) (picked I' y) (germ (frozen C p₀)) N r= (∏ i∈ cove D U u, C.O N r (p i.val).2 (F! i.val)) * peers D (fun i:I'=> (p₀ i).1) (fun i=> (p₀ i).2) u F!:=by
    funext t; rw [germ_here]; let g(i:I') := C.O N r (p i.val).2 (F! i.val) t
    unfold peers; rw [Pi.mul_apply,Finset.prod_apply,Finset.prod_apply]; have h:= (prod_inter_mul_prod_sdiff univ (cove D U u) g).symm; rw [univ_inter] at h; exact h
include hp hu
lemma matchingRegister : Cards.register C W (picked H y) (germ v') N r = C.O N r (g (N,r)) (F! u)* peers D (fun i:I'=> (p₀ i).1) (fun i=> (p₀ i).2) u F! :=by
    funext t; rw [germ_here, ← Equiv.prod_comp (trails D U u hp hu), Fintype.prod_sum_type, Fintype.prod_unique, Pi.mul_apply]
    let V'(i:X):= C.O N r (p i).2 (F! i) t; have hh := (cove_prod (U:=U) D u (fun i=>V' i.val) (fun i=>V' i.val) (fun i=>V' i.val) (fun _=>rfl) (fun _=>rfl)) -- order likely D u
    have hx(i:X)(hi:i=u): C.O N r (poleRead p u a g i (N,r)) (F! i) t= C.O N r (g (N,r)) (F! u) t:=by
        subst i; unfold poleRead; rw [dif_pos rfl]; exact charge_cast d _ (by rw [update_self]) _ _ _
    have hQ(i:X)(hi:i≠u): C.O N r (poleRead p u a g i (N,r)) (F! i) t= V' i:=by unfold poleRead;rw [dif_neg hi,update_of_ne hi]
    unfold peers; rw [Finset.prod_apply]; change _= C.O N r _ _ _ * ∏ i∈ univ\cove D U u,V' i.val
    rw [hh.2]; exact congr_arg₂ (· * ·) (hx u rfl) (prod_congr rfl (fun i _=>hQ i.val (shore_ne D U u i.2)))
local notation "Q!" =>fun i:I'=> (p₀ i).1
local notation "X!" =>fun i:I'=> (p₀ i).2
lemma edge_register : shop D Q! X! u (F!) (g (N,r))*peers D Q! X! u F!= Cards.register C W (picked I' y) (germ (frozen C p₀)) N r - Cards.register C W (picked H y) (germ v') N r:=by rw [matchingRegister _ _ _ hp hu,collective D p u]; unfold shop; rw [sub_mul]; rfl
omit hp hu
lemma belly_register : shop D Q! X! u S! (g (N,r))=Cards.register C W (picked J (fun i=> y i-y u)) (germ (frozen C (picked J p))) N r-C.O N r (g (N,r)) 0:=by
    funext t; unfold shop; rw [Pi.sub_apply,Pi.sub_apply, Finset.prod_apply,germ_here]; let V'(i:X):= C.O N r (p i).2 (S! i) t; have hh := (cove_prod (U:=U) D u (fun i=>V' i.val) (fun i=>V' i.val) (fun i=>V' i.val) (fun _=>rfl) (fun _=>rfl)).1
    change (∏ i∈cove D U u,V' i.val)-C.O N r (g (N,r)) (Cells.location C.S W N r (y u-y u)) t=(∏ i:J, V' i.val)-_; rw [sub_self, show Cells.location C.S W N r 0=0 from location_origin,hh]
end YM.OPE.Arboreal.Pixel
