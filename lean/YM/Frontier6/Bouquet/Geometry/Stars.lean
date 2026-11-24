import YM.Frontier6.Bouquet.Ensemble.Refine
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Use universal orthogonal slots (ambient ℓ² only for programming convenience).
 All integration/test operations on finite-dimensional normal directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble
open scoped Topology BigOperators Classical InnerProductSpace lp
abbrev Room := lp (fun _ : Slot=> E4) 2
abbrev Place:= Submodule ℝ Room
abbrev dim (P:Place):= Module.finrank ℝ P
abbrev house (i:Slot): Room→L[ℝ] E4:=lp.evalCLM ℝ (fun _ : Slot=> E4) 2 i
abbrev occupant (i:Slot): E4→L[ℝ] Room:=lp.singleContinuousLinearMap ℝ (fun _ : Slot=> E4) 2 i
section
variable (w:E4)(i:Slot)(j:Slot)(x:Room)
@[simp] lemma home_eq : house i x=x i:= rfl
@[simp] lemma occupancy : (occupant i w) i=w:= by rw [occupant,lp.singleContinuousLinearMap_apply]; exact lp.single_apply_self ..
lemma absentee (he:i≠j): (occupant i w) j=0:=by rw [occupant,lp.singleContinuousLinearMap_apply]; exact lp.single_apply_ne (E:=fun _ : Slot=> E4) 2 i w (Ne.symm he)
lemma occupancy_at : house i (occupant i w)=w:= occupancy w i
lemma occupant_inner : ⟪occupant i w,x⟫_ℝ=⟪w,x i⟫_ℝ:= lp.inner_single_left ..
lemma norm_house : ‖x i‖≤‖x‖:= lp.norm_apply_le_norm (by norm_num) x i
end

section
variable (u:Finset Slot)(v:Pod)
-- relative frames need explicit centroid with no counting normalization missing.
def entire (u: Finset Slot) : Place where
   carrier := {x|∀ i:Slot,i∉ u→ x i=0}
   add_mem' := fun h g i hi=>by simp [h i hi,g i hi]
   smul_mem' := fun _ _ h i hi => by simp [h i hi]
   zero_mem' := fun _ _=> rfl
lemma entire_mem (x:Room):x∈ entire u ↔ ∀ i:Slot,i∉ u→ x i=0:= Iff.rfl
lemma entire_le {A B:Finset Slot}(he:A⊆B): entire A≤ entire B:=fun _ hx i hi=> hx i (mt (he ·) hi)
lemma entire_solo {u:Finset Slot} {i:Slot}(he:i∈u)(w:E4): occupant i w∈ entire u:=fun j hj=> absentee w i j (by rintro rfl; contradiction)
lemma written {u:Finset Slot}(x:Room)(h:x∈ entire u): x=∑ i∈u,occupant i (x i):=by
   apply lp.ext; funext i
   have he(i:Slot): x i=(∑ i∈u,occupant i (x i)) i:=by
       change _=house i _; rw [map_sum]; by_cases hh:i∈u
       · rw [sum_eq_single_of_mem i hh]; exact (occupancy ..).symm; intro b _ hb; exact absentee _ _ _ hb
       exact (h i hh).trans (Finset.sum_eq_zero (s:=u) (f:=fun j=>house i (occupant j (x j))) (fun j hj=> absentee _ _ _ (by rintro rfl; contradiction))).symm
   apply he -- fail
lemma entry_cardinal_est (x:Room)(h:x∈ entire u) : ‖x‖≤∑ i∈u,‖x i‖:=by
   nth_rw 1 [written x h]; refine (norm_sum_le ..).trans_eq (sum_congr rfl fun i _=> lp.norm_single (by norm_num) i _)
-- entire finite rank via coordinate equivalence
abbrev recover : entire u→ₗ[ℝ] (u→ E4) := LinearMap.pi fun i=> (house (i:Slot)).toLinearMap ∘ₗ (entire u).subtype
lemma recover_at (f: entire u)(i:u): recover u f i=f.val i.val:=rfl
def deposit (y:u→ E4): Room:= ∑ i:u, occupant i (y i)
lemma deposit_in (y:u→ E4) : deposit u y ∈ entire u:= Submodule.sum_mem _ fun i _=> entire_solo i.property _
lemma deposit_eq (y:u→ E4)(i:u): (deposit u y) i.val = y i:=by
    change house (i:Slot) _=_; unfold deposit; rw [map_sum, sum_eq_single_of_mem i (mem_univ i)]; exact occupancy ..; intro j _ hj; exact absentee _ _ _ (fun h=> hj (Subtype.ext h))
lemma recover_bij : Bijective (recover u):=by
    constructor
    · intro i j he; apply Subtype.ext; apply lp.ext; funext k; by_cases hk:k∈u; exact congr_fun he (⟨k,hk⟩:u); exact (i.property k hk).trans (j.property k hk).symm
    intro y; exact ⟨⟨deposit u y,deposit_in u y⟩,funext fun i=> deposit_eq u y i⟩
instance entire_finite : FiniteDimensional ℝ (entire u) := FiniteDimensional.of_injective (recover u) (recover_bij u).1
lemma entire_dim : dim (entire u)=u.card*4:= (LinearEquiv.ofBijective _ (recover_bij u)).finrank_eq.trans (by rw [Module.finrank_pi_fintype]; simp)
end
end YM.Frontier6.Bouquet
