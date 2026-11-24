import YM.RGComparison01.Virtue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Tableau

/-!
# Relay: descend and lift small clusters

 This is on anchored bills (vote EACH site in union). Preserve multiplicities
 with a Nest, not an all-volume cost. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Relay
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
variable {c f C F L₀: Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC:C.val=c.val*M} {he : 2≤ c.val}
variable {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} {R : RG.Rep G f} {R':RG.Rep G F}
  {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b} {Z : χ → ι}
    (L':Relay (A:=A) (D:=D) hC he Z)
open Cabinet
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
set_option quotPrecheck false
local notation "Υ" => ((L).low.cut)

abbrev send (Z : χ→ι) (t : Cabinet.Folder χ):= t.image Z
def recut (Z : χ→ι) (t : Cabinet.Parenthood χ) : Cabinet.Parenthood ι := ⟨t.fst,send Z ∘ t.snd⟩
include L'
lemma here (z : Folder χ) : D.garden (send Z z) = (A.garden z).image Υ := by
  rw [D.orchard,A.orchard]; ext i; constructor
  · intro h; obtain ⟨j,hj,hp⟩:= mem_biUnion.mp h; obtain ⟨k,hk,rfl⟩:= mem_image.mp hj; rw [L'.pitch] at hp
    obtain ⟨m,hm,rfl⟩:=mem_image.mp hp; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨k,hk,hm⟩)
  intro h; obtain ⟨i,hi,rfl⟩:=mem_image.mp h; obtain ⟨k,hk,hv⟩:=mem_biUnion.mp hi
  exact mem_biUnion.mpr ⟨_,mem_image_of_mem Z hk,(L'.pitch k).symm ▸ mem_image_of_mem _ hv⟩
lemma grounds (z : Parenthood χ) : D.ground (recut Z z)=(A.ground z).image Υ := by
  unfold Cabinet.ground unionOf; rw [recut]; ext i; simp only [Function.comp_apply,mem_image,mem_biUnion,L'.here]; grind
lemma leg (p q: Folder χ) (r : ℕ) (hr : 2*r<c.val) (x:Site C) (hp : A.garden p⊆neighbors r x) (hq : A.garden q⊆neighbors r x)
    (ht : send Z p=send Z q) : p=q := by
  have hg (p q: Folder χ) (hp: A.garden p⊆neighbors r x) (hq:A.garden q⊆neighbors r x) (ht : send Z p⊆send Z q): p⊆q:= by
    intro i hi; obtain ⟨j,hj,H⟩:= mem_image.mp (ht (mem_image_of_mem Z hi))
    exact (L'.lift.point hr x j i ((neighbors_mem ..).1 (hq (A.spot q j hj))) ((neighbors_mem ..).1 (hp (A.spot p i hi))) H) ▸ hj
  exact Subset.antisymm (hg p q hp hq ht.le) (hg q p hq hp ht.ge)

lemma constant (p : Parenthood χ) (r:ℕ) (hr : 2*r<c.val) (x:Site C) (hp:A.ground p⊆neighbors r x) :
    coefficient (blocked A.garden) p.2 = coefficient (blocked D.garden) (recut Z p).2 := by
  have hP i : A.garden (p.2 i)⊆neighbors r x:= (A.within p i).trans hp
  apply Meadow.movement; intro i j; apply or_congr; · exact ⟨fun h=>congr_arg (send Z) h,L'.leg _ _ r hr x (hP i) (hP j)⟩
  unfold Ac.meets; dsimp only [recut,Function.comp_apply]; rw [L'.here,L'.here]; constructor
  · rintro ⟨k,ht,h⟩; exact ⟨_,mem_image_of_mem _ ht,mem_image_of_mem _ h⟩
  rintro ⟨v,he,hx⟩; obtain ⟨j,hj,h'⟩:= mem_image.mp he; obtain ⟨i,hi,h⟩:=mem_image.mp hx
  exact ⟨j,hj,(Meadow.garden hC x hr (hP _ hi) (hP _ hj) (h.trans h'.symm)) ▸ hi⟩
lemma injected (x:Site C) (r:ℕ) (ht: 2*r<c.val) (z:Folder χ) (hp: A.garden z⊆neighbors r x) : Set.InjOn Z z := fun i hi j hj H=> L'.lift.point ht x i j ((neighbors_mem ..).1 (hp (A.spot z i hi))) ((neighbors_mem ..).1 (hp (A.spot z j hj))) H

lemma oversea (x : Site C) (r:ℕ) (ht : 2*r<c.val) (z : Parenthood χ) (hp:A.ground z⊆neighbors r x) :
    A.Scene ℓ z ↔ D.Scene ℓ (recut Z z) := by
  have he i:= L'.injected x r ht (z.2 i) ((A.within z i).trans hp)
  have hf i : ((recut Z z).2 i).card=(z.2 i).card:= Finset.card_image_of_injOn (he i)
  have ht i : A.Peach (z.2 i) ↔ D.Peach ((recut Z z).2 i) := by
    rw [A.fruit,D.fruit]; exact Meadow.preheated Z A.foot D.foot (z.2 i) Υ L'.pitch (he i) ((Meadow.garden hC x ht).mono (show _ from (A.orchard (z.2 i)) ▸ Finset.coe_subset.mpr ((A.within z i).trans hp)))
  have h := L'.constant z r ‹_› x hp
  exact ⟨fun H=> ⟨H.start,fun i=> (hf i).trans_le (H.photos i),fun i=> (ht i).1 (H.poses i),h ▸ H.moves⟩,
    fun H=>⟨H.start,fun i=> (hf i).symm.trans_le (H.photos i),fun i=> (ht i).2 (H.poses i),h.symm ▸ H.moves⟩⟩
lemma stretch (x:Site C) (p: Record D ℓ) (hx: Υ x ∈ D.ground p.val) (r:ℕ) (hr: 2*r < c.val) (hK : garage b ℓ+b≤r) :
    ∃ z : Record A ℓ, recut Z z.val=p.val ∧ x∈ A.ground z.val := by
  choose y hy hY using L'.lift.esc x
  have hv i : send Z ((p.val.2 i).image y)=p.val.2 i:= by unfold send; rw [Finset.image_image,show Z ∘ y=id from funext hy,Finset.image_id]
  let z : Parenthood χ:= ⟨p.val.1, fun i=> (p.val.2 i).image y⟩
  have hz : recut Z z=p.val:= by unfold recut z; congr 1; exact funext hv
  have hp:A.ground z⊆neighbors r x:= by
    intro j hj; obtain ⟨i,-,ht⟩:= mem_biUnion.mp hj; change j∈ A.garden _ at ht; rw [orchard] at ht; obtain ⟨k,hk,hj⟩:=mem_biUnion.mp ht; obtain ⟨v,hv,rfl⟩:=mem_image.mp hk
    apply (neighbors_mem ..).2; apply (separation_triangle _ (A.site (y v)) _).trans
    rw [hY]
    refine (Nat.add_le_add ?_ ((neighbors_mem ..).1 ((A.penned (y v)).2 hj))).trans hK
    exact (neighbors_mem ..).1 ((D.extent p (Υ x) hx) (D.within p.val i (D.spot _ _ hv)))
  have hx' := L'.grounds z; rw [hz] at hx'; obtain ⟨i,hi,hu⟩:= mem_image.mp (hx' ▸ hx)
  exact ⟨⟨z,(L'.oversea x _ hr z hp).2 (hz.symm ▸ p.property)⟩,hz,(Meadow.garden hC x hr (hp hi) (show x∈neighbors r x from (neighbors_mem ..).2 (by simp)) hu) ▸ hi⟩

section anchored
variable (hB:4*garage b ℓ<c.val)
  (x : Site C)
include hB
def recycle (p : Record A ℓ) (hp:x∈ A.ground p.val) : Record D ℓ:= ⟨recut Z p.val,(L'.oversea x _ (by omega) _ (A.extent p x hp)).1 p.property⟩
lemma holds (p : Record A ℓ) (hp : x∈A.ground p.val) : Υ x ∈ D.ground (L'.recycle hB x p hp).val := by rw [recycle]; rw [L'.grounds]; exact mem_image_of_mem _ hp
lemma occupation (p : Record A ℓ) (hp : x∈A.ground p.val) (k:ℕ) : recycle L' hB x p hp ∈ D.podium ℓ k ↔ p∈ A.podium ℓ k := by
  rw [D.posted,A.posted]; constructor
  · intro ht i j hj; rw [← L'.hold]; exact ht i _ (mem_image_of_mem Z hj)
  intro ht i j hj; obtain ⟨l,hl,rfl⟩:=mem_image.mp hj; rw [L'.hold]; exact ht i l hl
lemma recycle_inj (p q : Record A ℓ) (hp:x∈A.ground p.val) (hq:x∈A.ground q.val) (hh : recycle L' hB x p hp=recycle L' hB x q hq) : p=q := by
  have ht : recut Z p.val=recut Z q.val:=congr_arg Subtype.val hh; have hkv := A.extent p x hp; have htp := A.extent q x hq
  suffices hz:p.val=q.val from Subtype.ext hz
  obtain ⟨⟨i,t⟩,hi⟩:=p; obtain ⟨⟨j,u⟩,hj⟩:=q; dsimp only at ht hkv htp; change Sigma.mk i t = Sigma.mk j u
  unfold recut at ht; obtain rfl : i=j := congr_arg Sigma.fst ht
  injection ht with ht he
  congr 1; funext j
  exact L'.leg _ _ _ (by omega) x ((A.within ⟨i,t⟩ j).trans hkv) ((A.within ⟨i,u⟩ j).trans htp) (congr_fun he j)
lemma voices (p : Cabinet.Record A ℓ) (hp : x∈A.ground p.val) : (D.ground ((recycle L' hB x p hp).val)).card= (A.ground p.val).card := by
  change (D.ground (recut Z p.val)).card=_; rw [L'.grounds]
  exact card_image_of_injOn ((Meadow.garden hC x (show 2* garage b ℓ< c.val from by omega)).mono (Finset.coe_subset.mpr (A.extent p x hp)))

lemma sum_prism {f : Record D ℓ→ ℝ} {g : Record A ℓ → ℝ} (k:ℕ)
    (ht: ∀ (p : Record A ℓ) (hp:x∈A.ground p.val), p∈ A.podium ℓ k → g p=f (recycle L' hB x p hp)) :
    (∑ p∈(A.podium ℓ k).filter (fun i=> x∈A.ground i.val),g p)=
     ∑ p∈(D.podium ℓ k).filter (fun i=> Υ x∈D.ground i.val),f p := by
  refine Finset.sum_bij (fun i hi => recycle L' hB x i (mem_filter.mp hi).2) (fun i hi=> ?_) (fun i hi j hj=> ?_) (fun i hi=>?_) fun i hi=> ht i _ (mem_filter.mp hi).1
  · exact mem_filter.mpr ⟨(occupation ..).2 (mem_filter.mp hi).1, L'.holds hB x i _⟩
  · exact recycle_inj L' hB x i j _ _
  obtain ⟨z,hz,h⟩:= stretch L' x i (mem_filter.mp hi).2 (garage b ℓ+b) (by unfold garage at hB ⊢; omega) le_rfl
  have he : recycle L' hB x z h=i := Subtype.ext hz
  exact ⟨z,mem_filter.mpr ⟨(occupation L' hB x z h k).1 (he.symm ▸ (mem_filter.mp hi).1),h⟩,he⟩
end anchored
end YM.RGComparison01.Relay
