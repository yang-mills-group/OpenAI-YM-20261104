import YM.QuadraticLocal.Earn.Club
/-! # Combinatorial clearance of sets of independent impulses for prescriptive catalog -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset Lattice RG Wilson Marker Multi
open Push Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι: Type}[DecidableEq V]{G:Gauge}{n:Side}
variable {P:Passport n V} {R:Census V}
variable (X:ι→Row P R G α)
set_option quotPrecheck false
local notation "σ"=> (fun i:ι=> (X i).mode)
local notation "σ'"=> (fun i:ι=> (X i).mode.val)
namespace Game
variable (A:Finset ι)(q:ι→ℂ)
local notation "E"=> A.biUnion (fun i:ι=> (X i).mode.val)
local notation "D"=> (A:Set ι).Pairwise (fun i j=> Disjoint (X i).mode.val (X j).mode.val)
local notation "Q" i:max=> Poly.send (X i).mode (q i)
local notation "U" x:max=> (∏ i∈x, Poly.send (X i).mode (q i))
-- avoid Card.C.Eq.Av ambiguous
lemma grapes (hs:(A:Set ι).Pairwise (fun i j=> Disjoint (X i).mode.val (X j).mode.val)) (s:R.Mode)(h:s.val=A.biUnion (fun i=> (X i).mode.val)) :
    (∏ i∈A, Poly.send (X i).mode (q i))= Poly.send s (∏ i∈A,q i):=by
 induction A using Finset.induction generalizing s with
 | empty=> rw [show s=R.quiet from Subtype.ext (h.trans (by rw [Finset.biUnion_empty]; rfl)),prod_empty, prod_empty]; rfl
 | insert i s₀ hi ih=>
    rw [Finset.biUnion_insert] at h; let z:=s₀.biUnion (fun j=>(X j).mode.val); have he:z ∈ R.choices:= R.down s.prop _ (h ▸ Finset.subset_union_right); let V:R.Mode:= ⟨z,he⟩
    have hη: Poly.merges (X i).mode V s:=by
       refine ⟨Finset.disjoint_left.mpr ?_,h.symm⟩; intro t ht hv; obtain ⟨j,hj,h⟩:= Finset.mem_biUnion.mp hv; exact Finset.disjoint_left.mp (hs (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj)) ht h
    rw [prod_insert hi, prod_insert hi, ih (hs.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)) V rfl, send_prod hη]
lemma denied (hs:¬ ((A:Set ι).Pairwise (fun i j=> Disjoint (X i).mode.val (X j).mode.val) ∧ ∃ s:R.Mode,s.val=A.biUnion (fun i=> (X i).mode.val))) : U A=0 := by
 induction A using Finset.induction with
 | empty=> exact False.elim (hs (by exact ⟨(by rw [Finset.coe_empty]; exact Set.pairwise_empty ..),R.quiet,(show (∅:Finset V)=_ from Finset.biUnion_empty.symm)⟩))
 | insert i s₀ hi ih=>
    rw [prod_insert hi]; by_cases h: (s₀:Set ι).Pairwise (fun i j=> Disjoint (X i).mode.val (X j).mode.val) ∧ ∃ s:R.Mode,s.val=s₀.biUnion (fun i=> (X i).mode.val)
    swap; · rw [ih h,mul_zero]
    obtain ⟨ha,v,hv⟩:=h; rw [grapes X s₀ q ha v hv]; apply send_noProd; rintro ⟨w,he,h⟩; apply hs; rw [Finset.biUnion_insert]
    have hP j (hj:j∈s₀): Disjoint (X i).mode.val (X j).mode.val:= he.mono_right (hv ▸ Finset.subset_biUnion_of_mem (fun i=> (X i).mode.val) hj)
    refine ⟨?_,w, (hv ▸ h.symm)⟩; rw [Finset.coe_insert]; rw [Set.pairwise_insert]; exact ⟨ha,fun y hy _=> ⟨hP _ hy,(hP _ hy).symm⟩⟩

lemma club_price (C:Club X) : ∏ i∈ C.val, Poly.send (X i).mode (q i)= Poly.send ( Club.alliance X C ) (∏ i∈C.val,q i):= Game.grapes X C.val q (Club.apart X C) (Club.alliance X C) (Club.fulfills ..)
lemma omitted (hs:A.Nonempty)(h:∀ i∈A,¬ (X i).clear)(hp:¬∃ C: Club X,C.val=A): ∏ i∈ A,Poly.send (X i).mode (q i)=0:=by
 apply Game.denied; rintro ⟨hi,he⟩; exact hp ⟨⟨A,hs,hi,he,h⟩,rfl⟩
end Game
end YM.QuadraticLocal.Earn
