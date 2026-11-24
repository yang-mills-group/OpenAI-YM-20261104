import YM.OPE.Compatible.Glades.Maxima
/-!
# Clock requirements on the array geometry. Stated on an entire tree
but used on one cut at a time. No artificial extra gaps on other vertices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {U Q:Finset X}{m j:X→ℕ}
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){P: Ensemble V}
variable {N p b:ℕ} {E:Track C.path V p}{o:X→Track C.path V p}
-- capacities. for any smaller cut (when frontier available at top scale). on union Q and brim Q.
def allUp (D:Origin X)(U:Finset X):= U ∪ brim D U
def roof (U:Finset X)(m:X→ℕ)(N:ℕ)(x:X):= if x∈U then m x else N
def finishAt (m:X→ℕ)(x:X):=m (par D x)
def places (X:Type)[Fintype X]:ℕ:=2* Fintype.card X
variable (U Q m)
omit [OrderBot X][PartialOrder X] in
lemma places_dom : U.card+Q.card ≤ places X:= by unfold places;have h:=Finset.card_le_univ U; have h':=Finset.card_le_univ Q; omega
lemma places_pos (X:Type)[PartialOrder X][OrderBot X][Fintype X]:0<places X:= by unfold places; exact Nat.mul_pos (by decide) (Fintype.card_pos_iff.mpr ⟨⊥⟩)
lemma brim_under (h : Q⊆U) : brim D Q ⊆ allUp D U:=by
    intro x hx; have hb:=(on_brim D Q).mp hx; by_cases he:x∈U; exact Finset.mem_union_left _ he
    exact Finset.mem_union_right _ ((on_brim D U).mpr ⟨he,hb.2.1,h hb.2.2⟩)
lemma lower_earliest (P:Series U m)(x:X)(h:x∈allUp D U): m ⊥ ≤ finishAt D m x:=by
    refine P.timing _ _ bot_le ?_; rcases Finset.mem_union.mp h with he|he; exact P.base.roots (par_le ..) he; exact (on_brim D U).mp he |>.2.2
lemma down_good (P:Series U m)(i:ℕ)(h:whenHigh U m ≤ i)(x:X)(hx:x∈allUp D U): finishAt D m x≤ roof U m i x:=by
    unfold roof; split
    next he=>exact P.timing _ _ (par_le ..) he
    next he=>exact (high D P (((on_brim D U).mp ((Finset.mem_union.mp hx).resolve_left he)).2.2)).trans h
lemma deck (m:X→ℕ):finishAt D m ⊥=m ⊥:=by simp [finishAt,par]
variable {U Q m}
variable {l : ℕ→ℕ}
def atLevel (C:Family G)(i b:ℕ):ℕ:= (gapL C b i +3)*(bins C i).B
structure CutOrder (C: Family G)(P₀:Ensemble V)(D:Origin X)(U:Finset X)(m j:X→ℕ)(N p:ℕ)(E:Track C.path V p)(o:X→Track C.path V p) (b : ℕ) (l:ℕ→ℕ) : Prop where
   plan : Series U m
   head : C.ref 0 < m ⊥
   next : whenHigh U m < N
   epochs x : x∈U→ finishAt D m x ≤ j x∧ j x ≤ m x
   moves : Migrating C.path (m ⊥) p N E
   pare x : x∈allUp D U →∀ i:ℕ, finishAt D m x≤ i → i < roof U m N x→ (C.path.levels.clock.op i p).ratio.parent ∘ o x (i+1)=o x i
   echo x : x∈allUp D U→∀ i,finishAt D m x≤ i→i ≤ roof U m N x→ ∀ a,a≠P₀.v→ o x i a=affine (P₀.move a).1 (E i a) (o x i P₀.v)
   inHost x : x∈ U→ Migrating C.path (j x) p (m x) (o x)
   copies x : x∈allUp D U→∀ i,finishAt D m x≤ i→ i≤ roof U m N x→ Injective (o x i)
   clear x : x∈allUp D U→∀ i,finishAt D m x < i→ i ≤ roof U m N x → ∀ a a', a≠a'→ atLevel C i b ≤ separation (o x i a) (o x i a') -- equality at finish? when x is the only child, refill at i=m_parent+1 still covers yes
   gap x y : x∈ allUp D U→ y∈allUp D U→ ¬ x ≤ y→ ¬ y ≤ x→∀ i, m (couple D x y) < i→finishAt D m x ≤ i→finishAt D m y ≤ i→ i ≤roof U m N x→ i ≤roof U m N y→∀ v w, atLevel C i b ≤ separation (o x i v) (o y i w)
   project x y : x∈U→ y∈allUp D U→ x ≤ y→ finishAt D m y=m x→ ∀ v:V,coverNumber (bins C (m x)).B ({o x (m x) v,o y (m x) v}:Support _) ≤ l (m x)
   solid x v : x∈U→ coverNumber (bins C (m x)).B ({o x (m x) v}:Support _) ≤ l (m x) -- surviving different clock maybe extend
-- solid for every other x at incoming with peg singleton, need trivial cover ≤1. ask from parameter l!
   costL x : x∈U→ 1 ≤ l (m x)
end YM.OPE.Arboreal
