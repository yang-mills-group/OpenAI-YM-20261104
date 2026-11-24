import YM.Comparison.RG02.Order.First
/-! Pair and variance of repeated field names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Cumulants
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_inj pass_connected)
open scoped Topology ContDiff BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (a b: V) (u : R.Mode) (x : Poly R) (h : x.part R.quiet=1)
include h
private lemma parts_root (s:R.Mode) (hi:a ∈ s.val) : x.part s = ∑ j:R.Mode, if j.val⊆ s.val ∧ a∈ j.val then (connected x).part j * x.part (diff s j.val) else 0:= by
   have hx:= moment_root a x h; rw [mul_comm,← Poly.studs (highlight a (connected x))] at hx
   have he:= (highlight_part a x s).trans (if_pos hi); rw [← he,hx,sum_mul,Poly.part_sum]; apply sum_congr rfl; intro t _; simp only [mul_at_part,highlight_part]; by_cases hu:a∈t.val <;> simp [hu, ite_self]
lemma lamp : (connected x).part (R.fire a)=x.part (R.fire a):= by
   let p:=R.fire a; have he:= parts_root a x h p (Finset.mem_singleton_self _)
   rw [Finset.sum_eq_single p,if_pos (show p.val⊆p.val∧a∈p.val from ⟨Finset.Subset.refl _, mem_singleton_self ..⟩),show diff p p.val=R.quiet from Subtype.ext sdiff_self, h, mul_one] at he; exact he.symm
   · intro t _ ht; rw [if_neg]; rintro ⟨ha,hb⟩; exact ht (Subtype.ext (le_antisymm ha (singleton_subset_iff.mpr hb)))
   simp
lemma twins (he:a≠b) (hs:u.val = {a,b}) : (connected x).part u= x.part u-x.part (R.fire a)* x.part (R.fire b):= by
   let i:=R.fire a; let y(j:R.Mode) := if j.val⊆ u.val ∧ a∈ j.val then (connected x).part j * x.part (diff u j.val) else 0
   have hp:=parts_root a x h u (by rw [hs]; simp); change _=∑ t,y t at hp
   have hu : u.val≠ i.val:= fun ha=> he (((mem_singleton.mp (show b∈i.val from ha ▸ (by simp [hs]:b∈u.val)))).symm)
   rw [← add_sum_erase _ y (mem_univ i),sum_eq_single u] at hp
   · have ha:y i=x.part (R.fire a)* x.part (R.fire b):=by
        unfold y; rw [if_pos (by change {a}⊆u.val ∧ a∈ ({a} : Finset V); simp [hs]), lamp a x h, show diff u i.val=R.fire b from Subtype.ext (show u.val \ {a}= {b} from by rw [hs]; ext; grind)]
     have hb:y u = (connected x).part u:= by unfold y; rw [if_pos (by simp [hs]),show diff u u.val=R.quiet from Subtype.ext sdiff_self,h,mul_one]
     rw [hp,ha,hb,add_sub_cancel_left]
   · intro t ht he'; unfold y; rw [if_neg]; rintro ⟨ha,hb⟩; by_cases hv:b∈ t.val;
     · exact he' (Subtype.ext (le_antisymm ha (by rw [hs]; exact insert_subset hb (singleton_subset_iff.mpr hv))))
     apply (Finset.mem_erase.mp ht).1; apply Subtype.ext; change t.val={a}; ext v; constructor
     · intro hj; have hx:=ha hj; rw [hs, Finset.mem_insert,mem_singleton] at hx; exact Finset.mem_singleton.mpr (hx.resolve_right (fun e=>hv (e ▸ hj)))
     intro hj; rw [mem_singleton.mp hj]; exact hb
   intro ht; exact False.elim (ht (mem_erase.mpr ⟨fun e=> hu (congrArg Subtype.val e),mem_univ _⟩))
open Order First
variable {r : ℕ} {y : Grade R r}
omit h
lemma orphan (ha : Order.Symmetric y) (hb : Order.UnitLeading y): First.buc (logMarked y)= connected (First.buc y) := by
   have he:= sym_ratio hb ha; have hz:= ratio_quiet hb; have hl:=connected_quiet hz
   apply pass_inj ((buc_vac _).trans hl) (connected_quiet ((buc_vac y).trans hb))
   rw [← buc_pass (he.log hz) hl, pass_connected hz,buc_ratio ha hb, pass_connected ((buc_vac y).trans hb)]
end YM.Comparison.RG02.Cumulants
