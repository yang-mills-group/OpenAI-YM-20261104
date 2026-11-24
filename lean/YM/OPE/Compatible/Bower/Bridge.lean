import YM.OPE.Compatible.Bower.Poster
/-!
# Second orbit interface. Only compare on aligned epochs ≥ K. No virtual E behind it.
Gap geometry between different members of *same* type; between types no purchase.
Plane mask for slot epochs reused at consecutive events.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave
open scoped Topology BigOperators Classical
variable {X V I G' T : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U Q F K:Finset X}{v:X} {m j:X→ℕ}
    (W:Type)[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype W][DecidableEq W][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p n N b d k g:ℕ}{l:ℕ→ℕ}
variable {A:Allot C}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
-- enough Coasts from one. upper for *all* paths ≥lower in second. omit allocations on second outside k. costs budgets no lost at SNAP
structure Arcade (C:Family G) (P':Ensemble T)(f:V ↪ T)(a:T→G') (D:Origin X)(U:Finset X)(m j:X→ℕ)(N p:ℕ) (P:Ensemble V) (E:Track C.path V p)(o:X→Track C.path V p)(b:ℕ)(l:ℕ→ℕ) (E':Track C.path T p)(o': X→Track C.path T p)(k:ℕ):Prop where
    bed : CutOrder C P D U m j N p E o b l
    fly : Screenlet P P' f
    ceiling : k ≤ N
    rings : Migrating C.path k p N E'
    turns i : k ≤ i → i ≤ N→ E' i ∘ f =E i
    honors x i : x∈allUp D U → k ≤ i→ i ≤ N→ o' x i ∘ f=o x i
    back x i : x∈allUp D U → k ≤ i→ i < N → (C.path.levels.clock.op i p).ratio.parent ∘ o' x (i+1)=o' x i
    pays x i : x∈allUp D U → k ≤ i→ i ≤ N→ ∀ v,v≠P'.v→ o' x i v=affine (P'.move v).1 (E' i v) (o' x i P'.v)
    occupancy x i : x∈allUp D U→ k ≤ i→ i ≤ N→ Injective (fun v:T=> (o' x i v,a v))
    seats x y i : x∈allUp D U → y∈allUp D U→ k ≤ i → i ≤ N → ∀ v w:T,a v=a w→ v≠w → atLevel C i b ≤ separation (o' x i v) (o' y i w)
    interval x y i : x∈allUp D U → y∈allUp D U → ¬ x ≤ y → ¬ y ≤ x→ m (Arboreal.couple D x y) < i → k ≤ i → i ≤ N → ∀ v, atLevel C i b ≤ separation (o' x i v) (o' y i v)
    share x y : x∈U→ y∈ allUp D U→ k ≤ m x→ x ≤ y→ finishAt D m y=m x→∀ v:T,coverNumber (bins C (m x)).B ({o' x (m x) v,o' y (m x) v}:Support _) ≤ l (m x)
namespace Arcade
variable (h:Arcade C P' f a D U m j N p P E o b l E' o' k)
include D h
set_option quotPrecheck false
omit [Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype I][DecidableEq I][Fintype T][DecidableEq T][Fintype G'] in
lemma lives (v:X)(hv:v∈allUp D U) (hu:F⊆U) : Session.Coast f P P' k N E E' (o∘columns D W F v) (o' ∘ columns D W F v):=by
   have he(i:brim D F ⊕ W): columns D W F v i ∈ allUp D U:=by
       cases i; next x=> exact brim_under D U F hu x.2
       next=> exact hv
   exact ⟨h.fly,h.rings,h.turns,fun i m hx hv=> h.honors _ _ (he i) hx hv,fun i m hx hv=> h.pays _ _ (he i) hx hv,fun i m hx hv=>h.back _ _ (he i) hx hv⟩
-- extras survive when parent clock inactive
variable (S:Wave m F K n)(he:F⊆U)(hb: v∈ allUp D U)
-- occupancy only. any choices of origins taken from active points
omit [Fintype V][DecidableEq V][DecidableEq T] in
lemma cover (z:I→X) (hp:∀ i,z i∈allUp D U)(hm:k ≤ n)(hn:n ≤ N)(hs:Fintype.card (G'×I) ≤ A.r g): Occupancy (Lights.pegs T I (o'∘ z) n) (A.r g):=by
    intro y; let P:= univ.filter (fun i:T×I=>pegs T I (o'∘z) n i=y); let f':T×I→ G'×I:=fun i=>(a i.1,i.2); have hf:Set.InjOn f' ↑P:=by
        rintro ⟨t,i⟩ hu ⟨t',j⟩ hv he; obtain ⟨ha,hv'⟩:=Prod.mk.inj he; change i=j at hv'; subst j
        exact Prod.ext ((h.occupancy (z i) n (hp i) hm hn) (Prod.ext ((mem_filter.mp hu|>.2).trans ((mem_filter.mp hv|>.2).symm)) ha)) rfl
    exact (card_image_of_injOn hf).symm.le.trans ((Finset.card_le_univ _).trans hs)
omit h
include S in
omit [Fintype W][DecidableEq W] in
lemma front {x:X}(hx:x∈allUp D U)(hf:F⊆U)(i:brim D K ⊕ W) : columns D W K x i ∈allUp D U:=by
    cases i; next x=> exact brim_under D U K (S.next.trans hf) x.2
    next=> exact hx
omit [Fintype W][DecidableEq W] in
lemma front' {x:X}(hx:x∈allUp D U)(hf:F⊆U)(i:brim D F⊕ W): columns D W F x i∈allUp D U:=by
    cases i; next x=> exact brim_under D U F hf x.2
    next=> exact hx
include h he hb
omit [Fintype V][DecidableEq V][DecidableEq T] in
lemma begun {r u:ℕ}(hp:k ≤ r)(ht:r ≤ N)(hA: Fintype.card G'*(places X+Fintype.card W) ≤ A.r u):Occupancy (Lights.pegs T (brim D F⊕W) (o'∘columns D W F v) r) (A.r u):=by
   apply cover D h _ (fun i=> front' D W hb he i) hp ht (le_trans ?_ hA); rw [Fintype.card_prod,Fintype.card_sum,Fintype.card_coe]; apply Nat.mul_le_mul_left; apply Nat.add_le_add_right; have h':=(Finset.card_le_univ (brim D F)); unfold places; omega
end Arcade
end YM.OPE.Arboreal
