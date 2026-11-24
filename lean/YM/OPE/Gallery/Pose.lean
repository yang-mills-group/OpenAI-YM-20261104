import YM.OPE.Portfolio.Unscented
import YM.OPE.Log.Brake
/-! # Masked all-slot geometry bookkeeping. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid
open scoped Topology BigOperators Classical
variable {I J V T L X : Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side}
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype T][DecidableEq T]
    [Fintype L][DecidableEq L][Fintype X][DecidableEq X]
variable {A:Fibers I J}{K:Fibers I T}{C:Fibers T J}{s:Ward (Names V J)}
    {m:Finset J}
-- Mask pullback including all proposals within collapsed region.
namespace Drapery
variable (A s)
def pullback : Ward (Names V I) where
    ready p:= s.ready ( (partialGroup V A).span p)
    blank:=by rw [show (partialGroup V A).span ((Names V I).quiet)=(Names V J).quiet from Subtype.ext (image_empty _)]; exact s.blank
    down {i j} he hT:= s.down (Finset.image_subset_image he) hT
    fire i:=by rw [show (partialGroup V A).span ((Names V I).fire i)=(Names V J).fire (i.1,A.bunch i.2) from Subtype.ext (image_singleton ..)]; exact s.fire _
lemma same_lanes {A B: Ward (Names V J)}(he:A.ready=B.ready) : A=B:=by cases A;cases B;congr
lemma pull_same : pullback (Fibers.same J) s=s:=by
    apply same_lanes; funext i; unfold pullback; suffices he : (partialGroup V (Fibers.same J)).span i=i by dsimp; rw [he]
    apply Subtype.ext; change i.val.image id=i.val; exact image_id
-- compat comp
lemma pull_ready (a:(Names V I).Mode): (pullback A s).ready a ↔ s.ready ((partialGroup V A).span a):= Iff.rfl
lemma ready_up (a:(Names V J).Mode): (pullback A s).ready ((partialGroup V A).plena a) ↔ s.ready a:=by rw [pull_ready,Fibers.reband]
lemma trial (h:Trial s):Trial (pullback A s):=by
    intro q p; simp_rw [pull_ready]; have he(i): nome (slotsZ:=J) q ((partialGroup V A).bunch i)=(partialGroup V A).bunch (nome q i):=rfl
    have hk : (partialGroup V A).span (drum q p) = drum q ((partialGroup V A).span p):=Subtype.ext (by unfold Fibers.span; simp only [drum,pares,image_image]; rfl)
    rw [hk]; exact h _ _
variable {A s}
def room (q:Ward (Names V I))(i j:V×I):Prop:= ∃ p:(Names V I).Mode,q.ready p ∧ i∈p.val∧j∈p.val
local notation "f"=> partialGroup V
lemma seats {i j} : room (pullback A s) i j ↔ room s ((f A).bunch i) ((f A).bunch j):=by
    constructor
    · rintro ⟨p,hs,he,hV⟩; exact ⟨(partialGroup V A).span p, hs,mem_image_of_mem _ he,mem_image_of_mem _ hV⟩
    rintro ⟨p,hs,he,hV⟩; exact ⟨(partialGroup V A).plena p,(ready_up A s p).2 hs, (Fibers.reaped ..).2 he,(Fibers.reaped ..).2 hV⟩
lemma widths (C:Fibers I V)(p:V): (C.contents p).Nonempty:=⟨C.twig p,(C.focuses ..).2 (C.sectioned _)⟩
lemma card_size (A:Fibers I J): Fintype.card J≤Fintype.card I:= Fintype.card_le_of_surjective A.bunch A.sectioned.surjective

def splitAt (A:Fibers I J) (K:Fibers I T)(C:Fibers T J): Prop:=∀ i,A.bunch i=C.bunch (K.bunch i)
namespace splitAt
variable (h:splitAt A K C)
include h
lemma runs (j:T): A.bunch (K.twig j)= C.bunch j:=by rw [h (K.twig j),K.sectioned]
lemma wardrobe (s:Ward (Names V J)) : pullback K (pullback C s)=pullback A s:=by
   apply same_lanes; funext i; refine propext ((pull_ready K (pullback C s) i).trans ((pull_ready C s _).trans ?_)); rw [pull_ready]; suffices he : (partialGroup V C).span ((partialGroup V K).span i) = (partialGroup V A).span i by rw [he]
   apply Subtype.ext; unfold Fibers.span; dsimp only; rw [image_image]; congr 1; funext i; exact Prod.ext rfl (h i.snd).symm
lemma headset (A': Fibers T X)(K':Fibers X J) (he : splitAt C A' K'): splitAt A (K.comp A') K':= fun i=> (h i).trans (he _)
lemma dorm1 (j) (hp:A.Solo (C.bunch j)) : K.Solo j:=by
   intro i he; have hf:A.bunch i=C.bunch j:= (h i).trans (congr_arg C.bunch he); exact (hp _ (h.runs j)).symm.trans (hp _ hf)
lemma dorm2 {j}(hp:A.Solo j) : C.Solo j:=by intro i he; apply K.sectioned.injective; exact (hp _ ((h.runs _).trans (C.sectioned _))).symm.trans (hp _ ((h.runs _).trans he))
lemma apart {o:V×I→ Site n}{k:ℕ} (hp:∀ i j,room (pullback A s) i j→ (f A).bunch i≠ (f A).bunch j→ k ≤ separation (o i) (o j)) : ∀ i j,room (pullback C s) i j→ (f C).bunch i≠(f C).bunch j→k ≤ separation (o ((f K).twig i)) (o ((f K).twig j)):=by
   have he(b:V×T) : (f A).bunch ((f K).twig b)=(f C).bunch b:= Prod.ext rfl (h.runs _); intro i j hi hx; refine hp _ _ (seats.mpr (he i ▸ he j ▸ seats.mp hi)) ?_
   rw [he,he]; exact hx
lemma contents_combine (j:J): A.contents j=(C.contents j).biUnion K.contents:=by
   ext i; rw [Fibers.focuses,h,mem_biUnion]; simp_rw [Fibers.focuses]; simp
lemma group_prod (W:Type*)[CommMonoid W](a:I→W)(i:J) : ∏ x∈ A.contents i,a x=∏ y∈ C.contents i,∏ x∈K.contents y,a x:=by rw [h.contents_combine]; exact prod_biUnion (fun i hi j hj he=> K.disjoint_c _ _ he)
lemma occupySame {m:Finset J}(hm:∀ j∈m,A.Solo j)(j:J)(hj:j∈m): K.twig (C.twig j)=A.twig j:=(hm j hj _ ((h.runs _).trans (C.sectioned ..))).symm
end splitAt

-- merge a single pair
lemma proposal (i j:T)(he:i≠j)(hv:C.bunch i=C.bunch j) : ∃ (J':Type)(_ : Fintype J')(_ : DecidableEq J')(A:Fibers T J')(B:Fibers J' J), splitAt C A B ∧
    (∀ k:T, A.twig (A.bunch k)=if k=j then i else k) ∧ Fintype.card J'<Fintype.card T:=by
    let K:= {p:T// p≠j}; let F(u:T):K:= if h:u=j then ⟨i,he⟩ else ⟨u,h⟩; let a:Fibers T K:=⟨F,Subtype.val,fun k=>dif_neg k.property⟩
    have hp(k:T) : C.bunch k=C.bunch (F k).val:=by unfold F; split; rename_i he; rw [he]; exact hv.symm; rfl
    let b:Fibers K J:=⟨C.bunch ∘ a.twig, F ∘ C.twig,fun k=> (hp _).symm.trans (C.sectioned _)⟩
    letI : Fintype K:= inferInstanceAs (Fintype {p : T // p ≠ j}); letI : DecidableEq K:= Classical.typeDecidableEq _; refine ⟨K,inferInstance,inferInstance,a,b,fun k=> hp k,fun k=>?_,?_⟩
    · change (F k).val=_; unfold F;split_ifs<;> rfl
    have hT : Fintype.card K= Fintype.card T-1:=by change Fintype.card {p:T// p≠j}=_; simpa using (Fintype.card_subtype_neq j)
    have hx:T:=i; have ht : 0 < Fintype.card T:= Fintype.card_pos_iff.mpr ⟨i⟩; omega
end Drapery
end YM.MergeProof.Ribbons.ManyCopies.Cadet
