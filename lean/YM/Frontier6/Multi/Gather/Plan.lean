import YM.MergeProof.North.Focal
import YM.Frontier6.Multi.Scene.Fermi

/-!
# Reap all branches above a concentration map.

Generalization of North/Focal to arbitrary surjective grouping. (Signed
propagation in our proof will be on the continuum side; this part pays for the
all-order-in-markers simultaneous nonlinear program on **raw** products, not
counterterms deleted at this level.) Maps delete modes only if they fail to cover
the *entire* preimage. No assumption of all groups having the same arity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Finset Function Marker Extra.Trajectories Accent
open Ribbon (Bud)
open scoped Topology BigOperators Classical
variable {O V I J : Type*}[DecidableEq O][Fintype O][DecidableEq V][Fintype V]
structure Concentrate (O V:Type*) where
    hit : O→ V
    seat : V→ O
    parked : RightInverse seat hit

namespace Concentrate
variable (E:Concentrate O V)
def span (i:(Bud O).Mode) : (Bud V).Mode:= ⟨i.val.image E.hit, mem_univ _⟩
lemma spans (i:(Bud O).Mode)(j) : j∈(E.span i).val ↔ ∃ k : O, k∈i.val∧ E.hit k=j:=mem_image

def plena (b:(Bud V).Mode) : (Bud O).Mode:=⟨univ.filter (fun i=> E.hit i ∈ b.val),mem_univ _⟩
def Pays (i:(Bud O).Mode) := i=E.plena (E.span i)
lemma reband (b:(Bud V).Mode) : E.span (E.plena b)=b:=by
    apply Subtype.ext; ext i; rw [E.spans]; constructor
    · rintro ⟨j,hj,rfl⟩; exact (mem_filter.mp hj).2
    intro hi; refine ⟨E.seat i,mem_filter.mpr ⟨mem_univ _,?_⟩, E.parked i⟩; rw [E.parked]; exact hi
lemma worth_iff (i:(Bud O).Mode) : E.Pays i↔ ∀ j∈ (E.span i).val,∀ k, E.hit k=j→k∈i.val:=by
   constructor; intro h j hj k hk; change i=_ at h; rw [show i.val=_ from congr_arg Subtype.val h]; exact mem_filter.mpr ⟨mem_univ _, hk.symm ▸ hj⟩
   intro h; apply Subtype.ext; ext x; exact ⟨fun hh=> mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ hh⟩,fun hh=>h _ (mem_filter.mp hh).2 x rfl⟩

def reap : Poly (Bud O)→L[ℂ] Poly (Bud V):= LinearMap.toContinuousLinearMap ({
    toFun:=fun p=>Poly.inject fun s=> p.part (E.plena s)
    map_add':= fun _ _ => Poly.ext fun _=> rfl
    map_smul':= fun _ _ => Poly.ext fun _=> rfl } : Poly (Bud O) →ₗ[ℂ] Poly (Bud V))
lemma harvest (i:(Bud O).Mode)(a:ℂ) : E.reap (Poly.send i a)=if E.Pays i then Poly.send (E.span i) a else 0:=by
   ext1 s; change (Poly.send i a).part (E.plena s)=_; rw [Poly.part_send]; split
   next h=> rw [← h,E.reband, if_pos (show E.Pays (E.plena s) from (by unfold Pays; rw [E.reband])),Poly.part_send,if_pos rfl]
   next h=> split
            next he=> rw [Poly.part_send, if_neg (fun (ht:s=E.span i)=> h (ht.symm ▸ he.symm))]
            rfl
lemma combines {q:I→(Bud O).Mode} {s:Finset I}(h:Fits q s): (E.span (unionTag _ _ h)).val=s.biUnion (fun i=>(E.span (q i)).val):=by
   ext; simp only [E.spans,unionTag,mem_biUnion]; constructor
   · rintro ⟨j,⟨i,hi,hj⟩,hk⟩; exact ⟨i,hi,j,hj,hk⟩
   rintro ⟨i,hi,j,hj,hk⟩; exact ⟨j,⟨i,hi,hj⟩,hk⟩

def fiber (v:V):Finset O:= univ.filter (fun i=> E.hit i=v)
lemma above (b:(Bud V).Mode) : (E.plena b).val=b.val.biUnion E.fiber:=by ext i; simp [fiber,plena]
lemma fare (w:O→ℝ)(b:(Bud V).Mode) : Poly.toll w (E.plena b)=Poly.toll (fun i=>∏ j∈E.fiber i,w j) b:=by
   unfold Poly.toll; rw [above]; apply prod_biUnion; intro i hi j hj hk; exact disjoint_left.mpr (fun k hx he=> hk (((mem_filter.mp hx).2).symm.trans (mem_filter.mp he).2))
lemma afford (i:(Bud O).Mode)(h:E.Pays i)(w:O→ℝ)(u:V→ℝ)(ht:∀ i, u i=∏ j∈ E.fiber i,w j): Poly.toll w i=Poly.toll u (E.span i):=by
   nth_rw 1 [show i=E.plena (E.span i) from h]; rw [E.fare]; rw [show u=(fun i=>_) from funext ht]
lemma recomp {q:I→(Bud O).Mode}{s:Finset I}(h:∀ i∈s,E.Pays (q i))(A:I→ℂ): E.reap (∏ i∈s,Poly.send (q i) (A i))=∏ i∈s,Poly.send (E.span (q i)) (A i):=by
   by_cases hv:Fits q s
   · have hp:Fits (fun i=>E.span (q i)) s:=by
        refine ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hk he=>?_,mem_univ _⟩
        exact disjoint_left.mp (hv.1 hi hj hz) ((E.worth_iff _).mp (h _ hi) _ hk (E.seat k) (E.parked k)) ((E.worth_iff _).mp (h _ hj) _ he (E.seat k) (E.parked k))
     have hx:E.Pays (unionTag _ _ hv):=by
        rw [E.worth_iff,E.combines]; intro i hi j hh; obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨k,hk,(E.worth_iff _).mp (h k hk) i hz j hh⟩
     rw [tagged_prod _ s hv,E.harvest,if_pos hx,tagged_prod _ _ hp]; exact congr_arg (fun p=> Poly.send p _) (Subtype.ext (E.combines hv))
   rw [show (∏ i∈s,Poly.send (q i) (A i))=0 from Classical.byContradiction (fun h=> hv (fits_of_tagged_prod _ h)),map_zero]; symm; by_contra hh
   have hp:= fits_of_tagged_prod (fun i=> E.span (q i)) hh; exact hv ⟨fun i hi j hj hz=> disjoint_left.mpr (fun _ hx he=> disjoint_left.mp (hp.1 hi hj hz) (mem_image_of_mem E.hit hx) (mem_image_of_mem E.hit he)),mem_univ _⟩
end Concentrate
end YM.MergeProof.Canopies
