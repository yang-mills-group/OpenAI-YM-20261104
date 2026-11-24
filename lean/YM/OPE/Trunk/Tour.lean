import YM.OPE.Trunk.Host
/-!
# Spatial locus.Run budget from real placement -> Tour elsewhere

Enough margin for spacers only between groups on a segment. Inter-segment use
true spacers to handle every price recovery. Same-axis collisions at any other sites
not a problem because forbidden in each comparison.PERMIT exposures around additional
basis markers determined only per range of current plan. No counter occupancy in
Staff spaces hidden from actual proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station
open scoped Topology BigOperators Classical ContDiff
variable {I J T Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p t t':ℕ}
    {Q: Rhythm I}
    {C: Family G}
set_option quotPrecheck false
namespace Rhythm
variable (C) (Q) (S: Q.Loom)
local notation "E"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "K"=> C.path.levels.budget
local notation "B"=> Site (C.side b p)
variable (u:∀ i:ℕ,I→Site (C.side i p))
def extras (Z:Type) (u:I→Site (C.side m p)) : I⊕Z→ Site (C.side m p):= Sum.elim u (fun _=>0)
structure Tour (b H N:ℕ)(p:ℕ)(u:∀ i:ℕ,I→Site (C.side i p)) : Prop where -- explicit C etc
    born : b ≤ S.below 0
    screen : S.launch Q.limit < N
    sites i:b ≤ i→i<N→∀ k,u i k=(C.path.levels.clock.op i p).ratio.parent (u (i+1) k)
    starts i (m:ℕ): S.launch (Q.age i) ≤ m→m<N→ u (m+1) i=(C.path.levels.clock.op m p).ratio.embed (u m i)
    coalescent t:t≤Q.limit→∀ i j,Q.phase t i j→u (S.below t +1) i=u (S.below t+1) j -- precedence
    fully t:t≤Q.limit→∀ i,t ≤ Q.age i→ let m:=S.below t; u (m+1) i=(C.path.levels.clock.op m p).ratio.embed (u m i)
    spine t:t ≤ Q.limit→∀ i,Q.pinned H i t→∀ m,b ≤ m→m ≤S.below t→u m i=0
    alumni t: t < Q.limit→∀ i,t+1 ≤ Q.age i → ∀ m:ℕ,S.launch t≤ m → m < S.below (t+1) → u (m+1) i= (C.path.levels.clock.op m p).ratio.embed (u m i)
    distant i: S.below 0 ≤ i→i ≤ N→ Cross (C.path.levels.budget i).B ((standC C b N p).spectrum i (extras C (p:=p) (m:=i) Unit (u i)))
    clear m:m ≤ N→∀ i j:I,i≠j→S.launch (Q.gap i j) ≤ m→ (C.path.levels.budget m).B^2 ≤ separation (u m i) (u m j)
variable {P:I→ Z→Prop}
-- purchase after until which Film t
-- clarify args
local notation "Ζ"=> walletF Z
local notation "Φ"=> (fun m:ℕ=> extras C (p:=p) (m:=m) Z (u m))
-- avoid binder Big names
local notation "p'"=> (fun m t=> ((track Z Q (Φ m) t)))
namespace Tour
variable {C Q S u}
variable (X:Tour Q C S b H N p u) {W r D}(L:LogPackage C W r D)
local notation "B'"=> (Y).budget
set_option quotPrecheck false
variable {s : Ward (Names (Site (C.side b p)) (Q.Panel t ⊕ Z))} (h:Q.Host t P s)
include X
lemma atleast (e:t≤Q.limit): b ≤ S.below t:= X.born.trans (S.le_below Q (Nat.zero_le _) e)
lemma lasts (e:t≤Q.limit): S.launch t < N:=(S.mono Q e le_rfl).trans_lt X.screen
lemma centerStep (h:b ≤ m)(he:m<N) (i:Q.Panel t⊕Z) : (track Z Q (Φ m) t i)=(Y|>.clock.op m p).ratio.parent (p' (m+1) t i):=by
    cases i with
    | inl i=> exact X.sites m h he _
    | inr i => let s:=(Y).clock.op m p; change 0=s.ratio.parent 0; rw [← show s.ratio.embed 0=0 from s.ratio.root.map_zero]; exact (Ratio.embed_parent ..).symm
lemma spread_budget (hk:S.below 0 ≤ m)(he:m ≤ N)(Z:Type)[Fintype Z][DecidableEq Z](t:ℕ) : Cross ((K m).B) ((E).spectrum m ((track Z Q (extras C (p:=p) (m:=m) Z (u m)) t))) :=by
    let A':= Sum.elim (fun k:Q.Panel t=> Sum.inl k.val) (fun _:Z=> (Sum.inr () : I ⊕Unit))
    let u': I ⊕ Unit→ Site (C.side m p):= extras C (p:=p) (m:=m) Unit (u m)
    have he' : track Z Q (extras C (p:=p) (m:=m) Z (u m)) t = u' ∘ A':=funext fun i=>by cases i<;>rfl
    rw [he']; intro i j h; exact X.distant m hk he (i.1,A' i.2) (j.1,A' j.2) h
lemma prices_at (hk:S.below 0 ≤ m)(he:m ≤ N)(k:ℕ)(Z:Type)[Fintype Z][DecidableEq Z](hv:Fintype.card I+Fintype.card Z ≤ k)(t:ℕ) : (E).occupied k (track Z Q (extras C (p:=p) (m:=m) Z (u m)) t):= (X.spread_budget hk he Z t).counts ((Q.ceiling Z t).trans hv) ((K m).B_pos)

omit X
private lemma sameCard (L:J→Site (C.side m p)){V:Site (C.side b p)}(i j:J) : separation ((E).spectrum m L (V,i)) ((E).spectrum m L (V,j))=separation (L i) (L j):=by simp [affine,Playout.spectrum,separation_translate,separation_signed]
private lemma table_seats {V I:Type}[Fintype I][DecidableEq I][Fintype V][DecidableEq V]{i j:V×I}{s: Ward (Names V I)} (h: Drapery.room s i j): Drapery.room s j i:= let ⟨p,hp,hq,hE⟩:=h; ⟨p,hp,hE,hq⟩
include X h
-- for spacers enough to pay pair of DISTINCT lower-phase panel classes
lemma apartCost (ht:t ≤ t')(hs:S.below 0 ≤ m)(hv:m ≤ N)(hk:∀ i, i < t→S.launch i ≤ m)(he:∀ i z,P i z→(K m).B^2 ≤ separation (u m i) 0): ∀ i j: (Site (C.side b p)) × (Q.Panel t' ⊕ Z), Drapery.room (pullback (walletF Z (Q.fold ht)) s) i j → (partialGroup (Site (C.side b p)) (walletF Z (Q.fold ht))).bunch i≠(partialGroup (Site (C.side b p)) (walletF Z (Q.fold ht))).bunch j → let y:=(E).spectrum m (p' m t'); (K m).B*meter L m ≤ separation (y i) (y j):=by
     let A:=walletF Z (Q.fold ht); let f:= (partialGroup (Site (C.side b p)) A).bunch; rintro ⟨i,q⟩ ⟨j,l⟩ hh hz g; let L':= (p' m t'); refine le_trans (b:=(K m).B^2) (by rw [pow_two]; exact Nat.mul_le_mul_left _ ((meters L m).2.1)) ?_; by_cases he':i=j; swap; · exact X.spread_budget hs hv Z t' (i,q) (j,l) he'
     subst j; let y:= Drapery.seats.1 hh; -- h instead of let
     change _ ≤ separation ((E).spectrum m L' (i,q)) ((E).spectrum m L' (i,l)); rw [sameCard (C:=C) L']
     rcases q with q|q <;> rcases l with l|l
     · let K':= Q.fold ht; have he : K'.bunch q ≠ K'.bunch l:= fun h=> hz (Prod.ext rfl (congr_arg (Sum.inl (β:=Z)) h)); have hs: ¬Q.phase t q.val l.val:= fun h=> he ((Q.seats ..).2 h); exact X.clear m hv q.val l.val (fun h=>hs (Or.inl h)) (hk _ (Q.upperAge hs))
     · exact he q.val l ((h.trans ht).acts hh)
     · rw [separation_comm]; exact he l.val q ((h.trans ht).acts (table_seats hh))
     have he: q=l:= h.single i l q y; exact (hz (congr_arg _ (by rw [he]))).elim
-- no post fold
lemma interspace (hs:S.below 0 ≤ m)(hv:m ≤ N)(hk:∀ i, i < t→ S.launch i ≤ m) (he:∀ i z,P i z→(K m).B^2 ≤ separation (u m i) 0): Spaced s ((E).spectrum m (p' m t)) ((K m).B*meter L m) := by
    have ht: walletF Z (Q.fold (le_refl t))=Fibers.same _:=by
       cases hB: walletF Z (Q.fold (le_refl t)) with | mk x y H=>
       have hb : x=id:=funext (fun q=>by cases q with
                  | inr z=>rw [show x _=_ from congr_arg (fun A=> A.bunch (.inr z)) hB.symm]; rfl
                  | inl p=>rw [show x _=_ from congr_arg (fun A=> A.bunch (.inl p)) hB.symm]; exact congr_arg Sum.inl (Q.valent p))
       subst x; have hx:y=id:=funext fun i=> H i; subst y; rfl
    have he' := X.apartCost L h (le_refl t) hs hv hk he; rw [ht,pull_same] at he'; exact he' -- `Spaced` defeq id?
end Tour
end Rhythm
end YM.OPE.Log.Trunk
