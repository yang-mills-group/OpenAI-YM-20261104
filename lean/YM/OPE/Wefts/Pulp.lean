import YM.OPE.Stellar.Focal
/-!
A complete-fiber coefficient extraction on each copy's leaf partitions,
retaining multiple markers on the same chamber for a later contraction.
Adapted from OPE.Stellar.Focal (Scions) for nontrivial target slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Wefts
open Finset Function Marker Extra.Trajectories Scions
open scoped Topology BigOperators Classical

variable {sp bt:ℕ}{V I J : Type*} [DecidableEq V] [Fintype V]

structure Divider (sp bt:ℕ) where
   paint: Pods sp → Pods bt
   reach: Pods bt → Pods sp
   lands i: paint (reach i) = i

namespace Divider
variable (G : Divider sp bt)
def addr : Name sp V → Name bt V := fun p=>(p.1,G.paint p.2)
omit [DecidableEq V] [Fintype V] in
lemma fst_addr (x:Name sp V): (G.addr x).1=x.1:=rfl
omit [DecidableEq V] [Fintype V] in
lemma surj : Surjective (G.addr (V:=V)) := fun ⟨v,b⟩=> ⟨(v,G.reach b),Prod.ext rfl (G.lands b)⟩
private def fiber (f:Pods sp→ℝ)(j:Pods bt) := ∏ i∈ (univ.filter (fun i=>G.paint i=j)), f i
end Divider

variable (M:Divider sp bt)
def shades (i:(Aged sp V).Mode) : (Aged bt V).Mode:= ⟨i.val.image M.addr,mem_univ _⟩
def plenary (b:(Aged bt V).Mode) : (Aged sp V).Mode:=⟨univ.filter fun x => M.addr x ∈ b.val,mem_univ _⟩
def Payable (i:(Aged sp V).Mode) := i=plenary M (shades M i)
lemma includes (i:(Aged sp V).Mode)(j) : j∈(shades M i).val ↔ ∃ k:Name sp V, k∈i.val ∧ M.addr k = j:=by simp [shades]
lemma filled (b:(Aged bt V).Mode)(y:Name sp V):y∈(plenary M b).val↔ M.addr y∈b.val:= by simp [plenary]
lemma reband (b:(Aged bt V).Mode) : shades M (plenary M b)=b:=by
   apply Subtype.ext; ext i; rw [includes]; exact ⟨fun ⟨k,h,e⟩=> e ▸ (filled ..).mp h,fun h=>by obtain ⟨k,rfl⟩:= M.surj i; exact ⟨k,(filled ..).mpr h,rfl⟩⟩
lemma worth_iff (i:(Aged sp V).Mode) : Payable M i↔ ∀ k:Name sp V,M.addr k∈(shades M i).val→ k ∈i.val:=by
   constructor; intro h k hk; change i=_ at h; nth_rw 1 [h]; exact (filled ..).mpr hk
   intro h; apply Subtype.ext; ext k; exact ⟨fun hj=> (filled ..).mpr ((includes ..).2 ⟨k,hj,rfl⟩), fun hk=> h k ((filled ..).mp hk)⟩

def reaps : Poly (Aged sp V)→L[ℂ] Poly (Aged bt V):= LinearMap.toContinuousLinearMap ({
    toFun:=fun p=>Poly.inject fun s=> p.part (plenary M s)
    map_add':= fun _ _ => Poly.ext fun _=> rfl
    map_smul':= fun _ _ => Poly.ext fun _=> rfl } : Poly (Aged sp V) →ₗ[ℂ] Poly (Aged bt V))
lemma harvest (i:(Aged sp V).Mode)(a:ℂ) : reaps M (Poly.send i a)=if Payable M i then Poly.send (shades M i) a else 0:=by
   ext1 s; change (Poly.send i a).part (plenary M s)=_; rw [Poly.part_send]; split
   next h=> rw [← h,reband, if_pos (show Payable M (plenary M s) from (by unfold Payable; rw [reband])),Poly.part_send,if_pos rfl]
   next h=> split
            next he=> rw [Poly.part_send, if_neg (fun (ht:s=shades M i)=> h (ht.symm ▸ he.symm))]
            rfl
lemma combines {q:I→(Aged sp V).Mode} {s:Finset I}(h:Fits q s): (shades M (unionTag _ _ h)).val=s.biUnion (fun i=>(shades M (q i)).val):=by
   ext; simp only [includes,unionTag,mem_biUnion]; tauto
lemma afford (i:(Aged sp V).Mode)(h:Payable M i)(w:Name sp V→ℝ)(u:Name bt V→ℝ)
    (ht:∀ i, u i=(∏ cStar∈(univ.filter (fun j:Pods sp=> M.paint j=i.2)), w (i.1,cStar))): Poly.toll w i=Poly.toll u (shades M i):=by
   have hv j : u j= ∏ x : Name sp V,if M.addr x=j then w x else 1 := by
      rcases j with ⟨j,q⟩; rw [ht,Fintype.prod_prod_type,prod_eq_single j]
      · rw [prod_filter]; simp [Divider.addr]
      · intro b _ hb; simp [Divider.addr,hb]
      simp
   nth_rw 1 [show i=plenary M (shades M i) from h]; unfold Poly.toll plenary; rw [prod_filter]; simp_rw [hv]; rw [prod_comm]; refine prod_congr rfl fun j _=>?_ ; by_cases he: M.addr j ∈ (shades M i).val
   · rw [if_pos he,prod_eq_single (M.addr j)]
     simp; intro b _ hh; exact if_neg hh.symm
     exact fun h=>(h he).elim
   simp only [if_neg he]; symm; exact Finset.prod_eq_one fun l hl=> if_neg (fun hd:M.addr j=l =>he (hd.symm ▸ hl))
lemma recomp {q:I→(Aged sp V).Mode}{s:Finset I}(h:∀ i∈s,Payable M (q i))(A:I→ℂ): reaps M (∏ i∈s,Poly.send (q i) (A i))=∏ i∈s,Poly.send (shades M (q i)) (A i):=by
   by_cases hv:Fits q s
   · have hp:Fits (fun i=>shades M (q i)) s:=by
        refine ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hk he=>?_,mem_univ _⟩
        obtain ⟨l,rfl⟩:= M.surj k; exact disjoint_left.mp (hv.1 hi hj hz) ((worth_iff ..).mp (h _ hi) l hk) ((worth_iff ..).mp (h _ hj) l he)
     have hx:Payable M (unionTag _ _ hv):=by
        rw [worth_iff]; intro i hi; rw [combines] at hi; obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨k,hk,(worth_iff ..).mp (h k hk) i hz⟩
     rw [tagged_prod _ s hv,harvest,if_pos hx,tagged_prod _ _ hp]; exact congr_arg (fun p=> Poly.send p _) (Subtype.ext (combines M hv))
   rw [show (∏ i∈s,Poly.send (q i) (A i))=0 from Classical.byContradiction (fun h=> hv (fits_of_tagged_prod _ h)),map_zero]; symm; by_contra hh
   have hp:= fits_of_tagged_prod (fun i=> shades M (q i)) hh
   exact hv ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hk he=> disjoint_left.mp (hp.1 hi hj hz) ((includes ..).2 ⟨k,hk,rfl⟩) ((includes ..).2 ⟨k,he,rfl⟩),mem_univ _⟩
end YM.MergeProof.Wefts
