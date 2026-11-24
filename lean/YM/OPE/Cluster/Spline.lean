import YM.OPE.Cluster.Weave
/-!
# Ground local geometry at fixed input parameters and period

Support all possible sweeps with sanctuaries. Cost is controlled by the Mast.size
alone; only charges the slot-to-parent movement once. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Station Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J W:Type}[Fintype I][DecidableEq I]{G:Gauge}{C:Family G}{j k N m q l p J':ℕ}
namespace Mast
variable (B:Mast I)(u v z:Finset I) (f grid hold:I→ℕ)(s:Finset I)(o:I→∀ i:ℕ,Site (C.side i p))
local notation "P"=> B.parent
local notation "ω"=> B.root
local notation "R"=> B.rank
local notation "K"=> C.path.levels
set_option quotPrecheck false
def now (k:ℕ):= z.filter fun i=> i=B.root ∨ f i < k
def release (k:ℕ)(i:I): Pod := if hold i < k ∨ hold i=k ∧ i∈s then some (hold i) else none
-- budget for any one event movement from slot rep to rep
abbrev spaces (I:Type) [Fintype I] := 200*(Fintype.card I+1) -- radius coeff multiplier
def PatrolFee (C:Family G)(I:Type)[Fintype I](k:ℕ) := radiusCost C (spaces I) k
-- local release requires BOTH itself and immediate parent unlocked at retirement
structure Floor (v u:Finset I)(f hold:I→ℕ)(s:Finset I) (j k:ℕ):Prop where
   inducts:B.Region u
   inner : ∀ i∈u,i≠B.root → f i ≤ j
   deaths : ∀ i∈u,i∉v→ f i=j ∧ release hold s j i=none ∧ release hold s j (B.parent i)=none
   leap : ∀ i,j < hold i → k ≤ hold i
   locked : ∀ i∈s, hold i ≤ j  -- avoid moving past endpoint inclusive
structure Scenery (C:Family G)(o:I→∀ i:ℕ,Site (C.side i p))(f grid:I→ℕ)(r:ℕ→ℕ)(l m:ℕ) : Prop where
   back: m ≤ l
   origin : ∀ i,o B.root i=0
   beans (j:ℕ): l ≤ j → Fintype.card I ≤ r j
   glow (j:ℕ) : l ≤ j→ stride C 100 j -4 ≤ (C.path.levels.budget j).B^2
   buds (j:ℕ) : l ≤ j → Cross (C.path.levels.budget j).B ((royal C m p j).place (fun i=>o i j))
   crowd i x y: B.rank x < B.rank y→ f x < i → Loom.stride C 100 i-4 ≤ separation (o x i) (o y i)
   travel i: i≠B.root → separation (o i (f i)) (o (P i) (f i)) ≤ 32*Loom.stride C 100 (f i)+1
   starts i b:(C.path.levels.clock.op b p).ratio.parent (o i (b+1)) = o i b
   align i b: grid i≤ b→ o i (b+1)=(C.path.levels.clock.op b p).ratio.embed (o i b)
private lemma plumed (C:Family G)(u:Type)[Fintype u](j:ℕ) : Fintype.card u*(32*stride C 100 j+1) ≤ (C.path.levels.budget j).B*(PatrolFee C u j-1):=by
    let D:=(C.path.levels.budget j).B; have he:1 ≤ D:=(C.path.levels.budget j).B_pos; let n:=Fintype.card u; let q:= Loom.count C 50 j
    have hQ:Loom.count C 100 j ≤ 2*q:= by
       apply Nat.ceil_le.mpr; push_cast; let x:=C.path.levels.clock.hatBeta (j+1); have hp:=Nat.le_ceil ((50:ℝ)*Real.log x); change 100*Real.log x ≤ 2*↑(Loom.count C 50 j); unfold Loom.count; push_cast; linarith only [hp]
    change n*(32*(D*_+4)+1) ≤ D*(200*(n+1)*(q+10)-1)
    rw [Nat.mul_sub_left_distrib,mul_one]; have hx:=Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 32 (Nat.add_le_add_right (Nat.mul_le_mul_left D (Nat.add_le_add_right hQ 2)) 4)) 1)
    refine hx.trans (Nat.le_sub_of_add_le ?_); nlinarith only [he,Nat.zero_le (n*D*q),Nat.zero_le (D*q),Nat.le_mul_of_pos_right n he]
variable {Q:ℕ→ℕ} {v u f grid hold s o}
variable {B} (H: Scenery B C o f grid Q l m) (F:Floor B v u f hold s j k) (hj:l ≤ j)
local notation "D"=> royal C m p
local notation "n"=> C.side m p
include H hj
omit [DecidableEq I] in
lemma Scenery.patrol (v:Finset I) : Cross (K|>.budget j|>.B) ((D j).place (fun l:v=>o l.val j)):= fun x y he=> H.buds j hj (x.1,x.2.val) (y.1,y.2.val) he
omit [DecidableEq I] in
lemma Scenery.lit (v:Finset I): Occupancy ((D j).place (fun l:v=>o l.val j)) (Q j):= bucket ((K).budget j|>.B_pos) ((Fintype.card_le_of_injective (Subtype.val : v → I) Subtype.val_injective).trans (H.beans j hj)) (H.patrol hj v)
include F
lemma Scenery.band : Band C (fun l:u=>o l.val) Q j k m:=by
    refine ⟨fun i hh he l=>H.starts ..,fun i hx _=> H.lit (hj.trans hx) u,?_⟩
    rintro i hx hk V' ⟨a,x⟩ ⟨b,y⟩ he; by_cases h':a=b; swap; · exact (H.glow i (hj.trans hx.le)).trans (H.patrol (hj.trans hx.le) u (a,x) (b,y) h')
    subst a; unfold V'; simp_rw [placeR (H.back.trans (hj.trans hx.le)),affine,separation_translate,separation_signed]
    have h(a b:u)(he:R a.val < R b.val) : stride C 100 i-4 ≤ separation (o a.val i) (o b.val i) := H.crowd i _ _ he ((F.inner a.val a.property fun h'=> by rw [h'] at he; exact he.not_ge (B.high _)).trans_lt hx)
    rcases lt_or_gt_of_ne (show R x.val≠R y.val from fun h=> he (Prod.ext rfl (Subtype.ext (B.inj h)))) with h'|h'; exact h _ _ h'; exact (h _ _ h').trans_eq (separation_comm ..)
variable (hv:B.root∈v) (hs:v⊆u)
local notation "L"=> B.splice u v hv hs
omit hj in
lemma Scenery.migrate (x:u) : separation (o ((L).twig ((L).bunch x)).val j) (o x.val j) ≤ (K|>.budget j|>.B)*(PatrolFee C I j-1):=by
    let e:= 32*stride C 100 j+1; have h (x) : x∈u → separation (o (B.trace v x) j) (o x j) ≤ B.depth x*e:=by
       refine B.travels (fun i=>i∈u → separation (o (B.trace v i) j) (o i j) ≤ B.depth i*e) ?_ ?_ x; swap
       · intro i hi H' hh; by_cases h:i∈v; rw [B.same _ h,separation_self]; exact Nat.zero_le _
         rw [B.follows _ hv h]; apply le_trans (separation_triangle _ (o (P i) j) _)
         apply ((Nat.add_le_add (H' (F.inducts i hh)) ?_)).trans (show B.depth (P i)*e+e ≤ _ from (Nat.succ_mul (B.depth (P i)) e).symm.trans_le (Nat.mul_le_mul_right e (B.drops i hi))) -- syntax problem
         unfold e; rw [separation_comm,← show f i=j from (F.deaths i hh h).1]; exact H.travel i hi -- e rewrite
       intro _; rw [B.same _ hv,separation_self]; exact Nat.zero_le _
    exact (h x.val x.property).trans ((Nat.mul_le_mul_right e (Nat.sub_le (Fintype.card I) (R x.val).val)).trans (plumed C I j))
local notation "r!"=> release hold s
omit H hj
include F hs hv
lemma Floor.land (x:v) (he:release hold s j x.val≠none) : (L).Only x:=by
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨((L).focuses ..).2 ((L).sectioned _),?_⟩
    intro i hi; refine Subtype.ext ?_; by_contra H; change i.val ≠ x.val at H; let X:= (L); have ht:B.trace v i.val=x.val:=congr_arg Subtype.val ((X.focuses i x).1 hi)
    obtain ⟨e,hm,hk,h⟩:= B.hits v i.val x.val hv ht H u i.property F.inducts; exact he (h ▸ (F.deaths e hm hk).2.2)
omit hv hs F
omit [Fintype I] in
lemma holy (x:I)(he:r! j x = some m): hold x=m ∧ (m < j ∨ m=j ∧ x∈s) := by
    unfold release at he; split_ifs at he with h; have hh:= Option.some_inj.mp he; exact ⟨hh,hh ▸ h⟩
omit [Fintype I] in
lemma locked_p (x:I) (h:r! k x ≠ none)(_hh:j<k) (ht:(r!) j x = none)(ha:∀ i,j < hold i→ k≤hold i) (he:∀ i∈s,hold i≤ j): hold x=j:= by
    unfold release at h ht; split_ifs at ht h with h1 h2 -- test
    all_goals first| contradiction| apply Option.noConfusion ht | have hb:= ha x; have hP:= he x; grind
include H hj F hs hv
lemma Scenery.birth (long:Bool)(hh:long=true → ∀ i∈u,i≠B.root → grid i ≤ j)(hq:j<k) : Event (L) C (fun i:u=>o i.val) Q j k m (PatrolFee C I j) long (fun i=>release hold s k i.val) (fun i=>release hold s j i.val):=by
    refine ⟨H.band F hj,fun i h he k hk hi=>?_,fun i p ht=>?_,?_,?_,?_⟩
    · by_cases hx:i.val=B.root
      · simp_rw [hx,H.origin]; exact (C.path.levels.clock.op k p).ratio.root.map_zero.symm
      exact H.align _ _ ((hh h _ i.property hx).trans hk)
    · obtain ⟨h₀,h₁⟩:=holy i.val ht; by_contra! h; have ha:= F.leap i.val; have he:= F.locked i.val; grind
    · intro i p hx; obtain ⟨hh,he⟩:= holy i.val hx; refine ⟨F.land hv hs _ (fun ht=>by rw [ht] at hx; contradiction),?_⟩; change r! k i.val=_; rw [release,hh]; exact if_pos (Or.inl (by omega))
    · intro i p hx he; obtain ⟨h,p'⟩:= holy i.val hx; refine h ▸ locked_p i.val (hx.symm ▸ Option.some_ne_none _) hq ?_ F.leap F.locked
      by_cases hh:i.val∈v; change r! j (B.trace v i.val)=none at he; rwa [B.same _ hh] at he
      exact (F.deaths i.val i.property hh).2.1
    · rintro ⟨v,g⟩ U; refine (assembled _ _ (p:=PatrolFee C I j-1) ?_).trans_eq (Nat.sub_add_cancel ?_)
      · unfold U; simp_rw [placeR (H.back.trans hj),affine,separation_translate,separation_signed]; exact H.migrate F hv hs g
      · unfold PatrolFee radiusCost spaces; change 0 < _; positivity
end Mast
end YM.OPE.Yarn

