import YM.RG03.Attach.Exp
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Extra.MULTISOURCE_TRAJECTORIES.Packets

-- Adapted from YM/RG03/Attach Stash/NoOldReserve/Bank. Realigned allocator.
/-! # Stash marked-only reclosure in the **same actual** forced dictionary

`progress/directedrecipe` constructed histories really have infinitely many slots
via sleepK, with exactly the supports and inventory check as extraTest. Use
those slots without widening the eligibility in the output. Stash one new
product into each (collisions with OLD K / OLD marks can be handled by add;
output needs no further choices attached to the same input label). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Qlocal.Parabola
open RG Lattice Wilson Function Marker Filter Finset Pert.Attach RG03.Gather MeasureTheory Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side} {A : Activities G n} {P : BudgetPoint}
    {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
variable (A)
/-- index space for possible merged addresses. -/
abbrev Place (n : Side) := {p : Support n × Support n // p.2.Nonempty ∧ p.2 ⊆ p.1}
def Place.ofForced (i : ForcedAddress G n) : Place n:=⟨⟨i.support,i.inventory⟩,i.inventory_ne,i.inventory_sup⟩
/-- Assign a countable bank per footprint. `openWhen` needn't accept when no
flags; this allows directly using the actual construction's sleepK labels. -/
structure Bank (t : ℝ) where
  storage : Place n × ℕ ↪ ℕ
  covers i : (A.forced (storage i)).support=i.1.val.1
  inventory i : (A.forced (storage i)).inventory=i.1.val.2
  openWhen i U : i.1.val.1 ∩ flags t U=i.1.val.2 → (A.forced (storage i)).extraTest U

variable {A} {t : ℝ} {X : Corrections G n}
open RG03
namespace Bank
lemma simple_page (i : ℕ) (he : ¬ (parts A X i).toRight.Nonempty) (j : ℕ) (h : j∈(parts A X i).toLeft) :
    parts A X i={Sum.inl j} := by
  let s:=parts A X i
  have ht (l : Old) (hl:Ac.chain (X.area A) s (.inl j) l) : l=.inl j:= by
    induction hl with
    | refl=>rfl
    | @tail b c _ hd ih=>
      obtain ⟨-,hc,x,hx,hc'⟩:=hd
      rw [ih] at hx
      cases c with
      | inl k=>
        by_contra hz
        exact disjoint_left.mp ((decoding A X i).2.2.2 h (mem_toLeft.mpr hc) (fun e=>hz (congrArg Sum.inl e.symm))) hx hc'
      | inr k=> exact (he ⟨k,mem_toRight.mpr hc⟩).elim
  exact eq_singleton_iff_unique_mem.mpr ⟨mem_toLeft.mp h,fun l hl=>ht _ ((decoding A X i).2.1.2 _ (mem_toLeft.mp h) _ hl)⟩

lemma singletonPage (j : ℕ) {i : ℕ} (h : parts A X i={Sum.inl j}) :
    (page A X i).support=(A.forced j).support ∧ (page A X i).inventory=(A.forced j).inventory ∧
    (page A X i).extraTest=(A.forced j).extraTest := by
  refine ⟨?_,?_,funext fun U=>propext ?_⟩
  · unfold page; change full A X (parts A X i)=_; rw [h]; simp [full,Pert.Attach.Corrections.area]
  · change bill A _ = _; rw [h,bill_union (X:=X)]; simp [Pert.Attach.Corrections.inventory]
  · change (∀ k∈(parts A X i).toLeft,_) ↔ _; rw [h]; simp
variable (C : Bank A t) (X : Corrections G n)

def reticket (i:ℕ) : ℕ:= C.storage (Place.ofForced (page A X i),i)
lemma reticket_injective : Injective (C.reticket X):= fun _ _ h=> congrArg Prod.snd (C.storage.injective h)
lemma reticket_area (i) : (A.forced (C.reticket X i)).support=(page A X i).support := C.covers ..
lemma reticket_bill (i) : (A.forced (C.reticket X i)).inventory=(page A X i).inventory := C.inventory ..
lemma reticket_eligible {i U} (h : (page A X i).eligible t U) : (A.forced (C.reticket X i)).eligible t U:=
  ⟨C.reticket_area X i ▸ C.reticket_bill X i ▸ h.1, C.openWhen _ U h.1⟩

def opened (i : ℕ):= (parts A X i).toRight.Nonempty
include C
omit C in
def oldIndex (A:Activities G n) (X:Corrections G n) (i : ℕ):= (decoding A X i).property.2.1.choose

omit C in
lemma old_here {i : ℕ} (h : ¬opened (A:=A) X i): parts A X i={Sum.inl (oldIndex A X i)} :=
  simple_page i h _ (decoding A X i).property.2.1.choose_spec

omit C in
lemma old_alone (j : ℕ): ∃ i, (¬ opened (A:=A) X i) ∧ oldIndex A X i=j := by
  obtain ⟨i,he⟩:=(Pert.Attach.decoding A X).surjective (Pert.Attach.singleton A X j)
  have h : parts A X i={Sum.inl j}:= congrArg Subtype.val he
  have hi : ¬ opened (A:=A) X i:=by unfold opened; rw [h]; rintro ⟨b,hb⟩; simp at hb
  exact ⟨i,hi,Sum.inl.inj (Finset.singleton_inj.mp ((old_here X hi).symm.trans h))⟩

def slot (i:ℕ):=if opened (A:=A) X i then C.reticket X i else oldIndex A X i
lemma slot_parts (i : ℕ) : (A.forced (C.slot X i)).support=(page A X i).support ∧ (A.forced (C.slot X i)).inventory=(page A X i).inventory:= by
  unfold slot; split
  · exact ⟨C.reticket_area .., C.reticket_bill ..⟩
  next h=> exact ⟨(singletonPage _ (old_here X h)).1.symm,(singletonPage _ (old_here X h)).2.1.symm⟩

lemma seen (R' : Activities G n) (P : BudgetPoint) (U : Config G n) (i : Finset ℕ) :
    Extra.Trajectories.Packets.selected (C.slot X) (A.admissible P U) i ↔ (attach A X P.threshold R').admissible P U i:= by
  constructor
  · rintro ⟨ha,h⟩
    refine ⟨fun a ha' b hb hh => ?_,?_⟩
    · change Disjoint (page A X a).support (page A X b).support
      rw [← (slot_parts C X a).1, ← (slot_parts C X b).1]
      exact ha.1 (mem_image_of_mem _ ha') (mem_image_of_mem _ hb) (fun hc=>hh (h ha' hb hc))
    change i.biUnion (fun i=> (page A X i).inventory)=_
    rw [← ha.2,image_biUnion]; exact biUnion_congr rfl fun i _ => (C.slot_parts X _).2.symm
  intro h
  refine ⟨⟨fun a ha b hb hh => ?_,?_⟩,fun i hi j hj H=>?_⟩
  · obtain ⟨i,hi,rfl⟩:=mem_image.mp ha; obtain ⟨j,hj,rfl⟩:=mem_image.mp hb
    rw [(C.slot_parts X i).1,(C.slot_parts X j).1]
    exact h.1 hi hj (fun he=>hh (congr_arg _ he))
  · rw [image_biUnion,← h.2]; exact biUnion_congr rfl fun i _=>(C.slot_parts X i).2
  by_contra he
  have hv:=h.1 hi hj he
  change Disjoint (page A X i).support (page A X j).support at hv
  rw [← (C.slot_parts X i).1, ← (C.slot_parts X j).1,H] at hv
  obtain ⟨z,hz⟩:=(A.forced (C.slot X j)).inventory_ne.mono (A.forced (C.slot X j)).inventory_sup
  exact Finset.disjoint_left.mp hv hz hz

/-- There is at most one open hit product stashed at each key. -/
def fresh (F : ℕ→Config G n→Poly R) (i : ℕ) (U : Config G n) : Poly R := if h : ∃ j, opened (A:=A) X j ∧ C.reticket X j=i then F h.choose U else 0
lemma valid (F : ℕ→Config G n→Poly R) {i : ℕ} (h : opened (A:=A) X i) : C.fresh X F (C.reticket X i)=F i:= by
  funext U; unfold fresh
  let P : ∃ j, opened (A:=A) X j ∧ C.reticket X j=C.reticket X i:=⟨i,h,rfl⟩
  rw [dif_pos P,C.reticket_injective X P.choose_spec.2]
lemma invalid (F : ℕ→Config G n→Poly R) {i : ℕ} (h : ¬∃ j, opened (A:=A) X j ∧ C.reticket X j=i):
    C.fresh X F i=0:=funext fun _=>dif_neg h

variable (P : BudgetPoint) (K I : ℕ→Config G n→Poly R)

def lifted (i : ℕ)(U : Config G n):= outKey A X U P (Sum.elim (K · U) (I · U)) i
omit C in
lemma returns_old {b : ℕ}(h : ¬opened (A:=A) X b)(U) (hK : ∀ i:ℕ, K i U≠0→ (A.forced i).eligible P.threshold U):
    lifted (A:=A) X P K I b U= K (oldIndex A X b) U:= by
  unfold lifted outKey; rw [old_here X h,prod_singleton]
  split
  next he=> rfl
  next he=>
    set c:= oldIndex A X b
    obtain ⟨h₁,h₂,h₃⟩:= singletonPage _ (old_here X h)
    unfold ForcedAddress.eligible at *
    symm; by_contra hn; exact he (by rw [h₁,h₂,h₃]; exact hK c hn)

def store (i : ℕ)(U : Config G n):= K i U + C.fresh X (lifted (A:=A) X P K I) i U
omit C in
lemma old_inj : Set.InjOn (oldIndex A X) {i| ¬ opened (A:=A) X i}:= fun i hi j hj h=> parts_inj A X <| by
  rw [old_here X hi, old_here X hj,h]
lemma pack (i:ℕ) (U : Config G n) (hK : ∀ i, K i U≠0→ (A.forced i).eligible P.threshold U):
    ∑' j : {j // C.slot X j=i}, lifted (A:=A) X P K I j.val U=C.store X P K I i U:= by
  obtain ⟨k,hk,hk'⟩:= old_alone (A:=A) X i
  have ht : C.slot X k=i:= by simp [slot,hk,hk']
  let z : {j // C.slot X j=i}:=⟨k,ht⟩
  have hOld (x : {j // C.slot X j=i}) (he : ¬opened (A:=A) X x.val): x=z:= by
    apply Subtype.ext
    apply old_inj X he hk
    simpa [slot,he,hk'] using x.property
  have hz: lifted (A:=A) X P K I z.val U=K i U:=by dsimp only [z]; rw [returns_old X P K I hk U hK,hk']
  unfold store; by_cases hv:∃ j,opened (A:=A) X j∧ C.reticket X j=i
  · obtain ⟨s,hs,rfl⟩ :=hv
    let y:{j // C.slot X j=C.reticket X s}:=⟨s,by simp [slot,hs]⟩
    have he:z≠y:=fun H=>hk ((show s=k from (congrArg Subtype.val H).symm) ▸ hs)
    rw [tsum_eq_sum (s:={z,y}),sum_insert (fun h=>he (mem_singleton.mp h)), sum_singleton,C.valid X _ hs,hz]
    · intro b Hb
      by_cases hO:opened (A:=A) X b.val
      · have hy:b=y:= Subtype.ext (C.reticket_injective X (by simpa [slot,hO,y] using b.property))
        exact (Hb (hy.symm ▸ Finset.mem_insert_of_mem (mem_singleton_self ..))).elim
      exact (Hb ((hOld b hO).symm ▸ mem_insert_self ..)).elim
  rw [C.invalid X _ hv, Pi.zero_apply,add_zero,tsum_eq_single z,hz]
  intro b hb; by_cases he:opened (A:=A) X b.val
  · exact (hv ⟨b.val,he,by simpa [slot,he] using b.property⟩).elim
  exact (hb (hOld b he)).elim
lemma stored (U : Config G n) {r : V→ℝ} (hr:∀ i,0<r i)
    (hK : ∀ i U, K i U≠0→ (A.forced i).eligible P.threshold U)
    (hI : ∀ i U, Healthy P.threshold (X.region i) U → I i U=0)
    (h : Summable fun i=> Poly.price r (K i U)) (h' : Summable fun i=> Poly.price r (I i U)) :
    poem A P (C.store X P K I) U = poem A P K U*(∏' j,(1+I j U)):= by
  let F:=lifted (A:=A) X P K I
  let W:=Sum.elim (K · U) (I · U)
  have hf : Summable fun i=>Poly.price r (W i):= Summable.sum _ h h'
  have he : Summable fun i=> F i U := by
    refine (Poly.budgeted hr ((purchases hr hf).comp_injective (parts_inj A X)) (fun i=>?_)).1
    unfold F lifted outKey; split; exact le_rfl
    rw [Poly.zero_price]; exact Poly.nonnegative hr _
  have hz:Extra.Trajectories.Packets.value (C.slot X) (A.admissible P U) (fun i=>F i U)=Gather.outWord A X U P W:= by
    funext s; unfold Extra.Trajectories.Packets.value Gather.outWord
    have hx: Extra.Trajectories.Packets.selected (C.slot X) (A.admissible P U) s ↔ (Pert.Attach.attach A X P.threshold A).admissible P U s := by
      exact seen C X A P U s
    exact if_congr hx rfl rfl
  have hZ:= Gather.merged (A:=A) (X:=X) (fun j=>hK j U) (fun i=> hI i U) hr h h'
  have hh:=Extra.Trajectories.Packets.repack (C.slot X) (A.admissible P U) (F · U) (hz.symm ▸ hZ.summable) he|>.tsum_eq
  simp_rw [show ∀ i, (∑' j : {j // C.slot X j=i}, F j.val U)= _ from fun i=>pack C X P K I i U (fun i=>hK i U),hz] at hh
  exact hh.trans hZ.tsum_eq
end Bank
open Progress.DirectedRecipe Ovens
private def toFoot (n:Side): Place n ↪ Foot n where
  toFun i:=⟨i.val.1,i.val.2,i.property.1,i.property.2⟩
  inj' a b h:=Subtype.ext (Prod.ext (congrArg Foot.support h) (congrArg Foot.inventory h))

def Bank.ofSlots (h : HasSlots P A) : Bank A P.threshold where
  storage:= ((toFoot n).prodMap (Embedding.refl ℕ)).trans (sleepK G n)
  covers i:= by rw [h.forced]; exact congrArg Foot.support (tile_exact P (toFoot n i.1) i.2)
  inventory i:= by rw [h.forced]; exact congrArg Foot.inventory (tile_exact P (toFoot n i.1) i.2)
  openWhen i U:=by rw [h.forced]; exact (tile_test P (toFoot n i.1) i.2 U).mpr
end YM.Qlocal.Parabola
