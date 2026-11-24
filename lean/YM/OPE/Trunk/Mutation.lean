import YM.OPE.Trunk.Interrupt
/-! # The cost and expression at root following a signed v-projection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
namespace Variant
open Plain Highest Studio Playout Pigment
local notation "P!"=> Q.TypeAt Z
local notation "K!"=> (owner Q 0)
local notation "q!"=> walletF Z (Q.fold (Nat.zero_le H))
local notation "h!"=> (walletF Z (Q.fold (Nat.zero_le 1)))
local notation "ι"=> carried Q Z
lemma only_c (Q:Rhythm I)(t:ℕ)(Z:Type)[Fintype Z][DecidableEq Z]:
   (walletF Z (Q.fold (Nat.zero_le t))).contents (.inl (owner Q 0))= (univ : Finset (Q.Panel t)).image Sum.inl:=by
   rw [Q.mapped Z (Nat.zero_le t) _]; congr; exact eq_univ_of_forall (fun i=> (Fibers.focuses ..).2 (Q.unity _))
lemma only_root (Q:Rhythm I)(t:ℕ): Q.tribe (owner Q t).val t=Q.focus t:=by
    ext i; rw [on_focus,Q.arrives]; exact ⟨Q.conj (Q.matchs Q.star _),Q.conj (Q.swap (Q.matchs Q.star _))⟩
variable {f:Q.TypeAt Z H→ Config G (C.side N p)→ℂ}
    (v:C.label d) (g:I→ Config G (C.side N p)→ℂ)
lemma orientE (Q:Rhythm I)(t:ℕ)(Z:Type)[Fintype Z][DecidableEq Z](Y:Type*)[CommMonoid Y](f:I→Y): (∏ x∈ Finset.univ.erase (owner Q t),∏ k∈Q.tribe x.val t,f k)=∏ i∈ Finset.univ\ Q.focus t,f i:=by
   simp_rw [← Q.plate]; let U:= Q.fromAll t; let p:= univ.erase (owner Q t); rw [← Finset.prod_biUnion]; swap; · exact fun i hi j hj he=> U.disjoint_c _ _ he
   rw [show Finset.biUnion p _=_ from ?_];
   · change p.biUnion U.contents= univ \ Q.focus t; ext i; simp only [mem_biUnion,p,mem_erase,mem_univ,and_true,Fibers.focuses,Finset.mem_sdiff,true_and]
     have he : (i∈Q.focus t) ↔ U.bunch i=owner Q t:= by rw [← only_root,← Q.plate,Fibers.focuses]
     rw [he, ← ne_eq]; constructor
     · rintro ⟨k,hk,hl⟩; subst k; exact hk
     intro h; exact ⟨U.bunch i,h,rfl⟩ -- indent

def childF (g:I→ Config G (C.side N p)→ℂ) (Q:Rhythm I)(t:ℕ)(U) := ∏ i∈ Q.focus t,g i U
lemma joins_E (hp:∀ k:Q.Panel H,f (.inl k) = fun U=>∏ i∈ Q.tribe k.val H, g i U) :
    let F (i: P! H):= applySign d f v (ι H) i; let s:=childF (C:=C) g Q H-C.O N p v 0
    f (ι H)=childF (C:=C) g Q H∧ grouped_X F q! (ι 0)=fun U=> s U*∏ i ∈ univ \ Q.focus H,g i U:=by
    intro F s; have he:f (ι H)=childF (C:=C) g Q H:=by rw [show f (ι H)=_ from hp (owner Q H),only_root];rfl
    have hh(k:Q.Panel H)(h:k≠owner Q H) : F (.inl k)=f (.inl k):= if_neg (fun hp=>h (Sum.inl.inj hp)); have hz:F (ι H)=s:= by unfold F; rw [applySign,if_pos rfl,he]
    refine ⟨he,?_⟩; funext U; unfold grouped_X; rw [show (q!).contents (ι 0)=_ from only_c Q H Z, prod_image (fun _ _ _ _ hr=> Sum.inl.inj hr),← Finset.mul_prod_erase _ _ (mem_univ (owner Q H)), show F (Sum.inl (owner Q H))= _ from hz,← orientE Q H Z ℂ (fun i=>g i U)]
    refine congr_arg _ (prod_congr rfl fun i hi=>?_) -- err
    rw [hh i (mem_erase.mp hi).1,hp]

local notation "ζ"=> C.path.levels.clock
variable (U':Q.Strike H l) (v':I→ℝ)(w:ℕ→Z→ℝ)
local notation "τ"=> S.below 0
local notation "η"=> patchWidth Q S C H l d v' w
include U'
lemma edge_root : lineRelease h! (η 1 τ) (ι 0)= (∏ i,v' i) * widen S C H l d:=by
    have hm:= U'.atMost; have ht:= U'.before; let p:= ι 0; let K:= η 0; have hζ:=ownerAlive U' (Nat.zero_le _) Z; have h:¬l<0:= Nat.not_lt_zero _; have hX:p∉keep Q Z l 0:=by rw [keep,if_neg h]; exact hζ
    rw [← show afterWidth (η 1) (S.below 0) (h!) _ τ p=_ from if_neg hX]; rw [← along_w U' v' w (by omega : 0<H)]
    change patchWidth Q S C H l d v' w 0 τ p= _; rw [patchWidth,if_pos rfl,if_neg h]; congr 1; exact (piece_pay (S:=S) (C:=C) (m:=τ) w v' (i:= owner Q 0) (Nat.zero_le _)).trans (estate_root ..)
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
