import YM.OPE.Compatible.Trees.Rearrange
import YM.OPE.Exchange.Regime

/-!
# Euclidean tree layout

`s_v>0` on internal vertices, s-o at ⊥ is declared outer physical
scale. `s_v/s_parent ∈ (0,1]`, in applications can of course require a
sufficiently small fixed upper bound as well. No floor. Sibling clusters
separated in the full geometry. Don't test simultaneously an ancestor
field with any of its descendants. Dummy coordinates lengths of leaves
not used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type}[PartialOrder V][OrderBot V][Fintype V]
variable (E:Origin V)

structure Layout (M η : ℝ) (s : V → ℝ) (x : V → E4) : Prop where
  pos v : v∈heart V → 0 < s v
  scales v : v∈rest (heart V) → s v ≤ s (par E v)
  close v i : i∈ strictChildren E v → ‖x i-x v‖ ≤ M*s v
  siblings v i j : i∈ strictChildren E v → j∈strictChildren E v → i≠j → ∀ u w, i ≤ u → j ≤ w → η*s v ≤ ‖x u-x w‖

-- covers constants depending only on finite tree
private def steps (v:V) := (Finset.univ.filter (fun i:V => i < v)).card
omit [OrderBot V] in
private lemma drops {v w:V} (h:v<w) : steps v < steps w := by
  apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]; refine ⟨?_,fun e => ?_⟩
  · exact fun z e => Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp e).2 h⟩
  have hv : v∈ Finset.univ.filter (· < v) := by rw [e]; simp [h]
  simp at hv

variable {M η : ℝ} {s:V→ℝ} {x:V→ E4} (H : Layout E M η s x)
include E H
lemma Layout.earlier {v w:V} (hv:v∈heart V) (h:w ≤ v) : s v ≤ s w := by
  revert hv h
  refine journey E (P:=fun i:V => i∈heart V → w ≤ i → s i ≤ s w) (fun _ h => by rw [le_bot_iff.mp h]) ?_ v
  intro i hi ih hv' hw
  rcases hw.lt_or_eq with h|rfl
  · exact (H.scales i ((rest_mem _).mpr ⟨hi,hv'⟩)).trans (ih (internal_le hv' (par_le ..)) (touch_par E h))
  exact le_rfl

private lemma reach (hM : 0 ≤ M) {v w : V} (hv:v∈heart V) (hw:v ≤ w) :
    ‖x w-x v‖ ≤ (steps w:ℝ)*(M*s v) := by
  revert hw; have hp := mul_nonneg hM (H.pos v hv).le
  refine journey E (P:=fun i => v ≤ i → ‖x i-x v‖ ≤ (steps i:ℝ)*(M*s v)) ?_ ?_ w
  · intro hz; obtain rfl := le_bot_iff.mp hz; rw [sub_self,norm_zero]; positivity
  intro i hi ih ht
  rcases ht.lt_or_eq with h|rfl
  · have hu := from_par E hi; have hz := touch_par E h
    have hh := H.earlier E (heart_mem.mpr ⟨i,hu⟩) hz
    apply (c_dist_point _ _ _).trans ((add_le_add (H.close _ _ ((kid_mem E).mpr ⟨hu,rfl⟩)) (ih hz)).trans _)
    calc M*s (par E i) + (steps (par E i):ℝ)*(M*s v) ≤ (steps (par E i):ℝ)*(M*s v)+M*s v := by
          simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hh hM) ((steps (par E i):ℝ)*(M*s v))
         _ = ((steps (par E i):ℝ)+1)*(M*s v) := by rw [add_mul,one_mul]
         _ ≤ (steps i:ℝ)*(M*s v) := mul_le_mul_of_nonneg_right (by exact_mod_cast drops hu) hp
  rw [sub_self,norm_zero]; positivity

def envelope (V:Type) [Fintype V] (M:ℝ) := (Fintype.card V:ℝ)*M
lemma Layout.reaches (hM : 0 ≤ M) {v w:V} (hv : v∈heart V) (h:v ≤ w) : ‖x w-x v‖ ≤ envelope V M*s v :=
  (reach E H hM hv h).trans (by
    unfold envelope; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by
      exact_mod_cast (Finset.card_le_univ _ : steps w ≤ Fintype.card V)) (mul_nonneg hM (H.pos v hv).le))

lemma Layout.fork {u w:V} (h : ¬ u ≤ w) (h' : ¬ w ≤ u) : η*s (couple E u w) ≤ ‖x u-x w‖ := by
  obtain ⟨i,hi,hI,hp⟩ := foot E (separate_left E h)
  obtain ⟨j,hj,hJ,hq⟩ := foot E (separate_right E h')
  exact H.siblings _ _ _ ((kid_mem ..).mpr ⟨hi,hI⟩) ((kid_mem ..).mpr ⟨hj,hJ⟩)
    (fun e => hj.not_ge (ancestors_couple E (e ▸ hp) hq)) _ _ hp hq

lemma Layout.inject (P : Finset V) (hP:Crown P) (he:0<η) : Injective (picked (brim E P) x) := by
  intro i j h
  refine Subtype.ext (Classical.byContradiction fun hh => ?_)
  have hw := brim_apart E P hP i.2 j.2 hh
  have hz := mul_pos he (H.pos _ (heart_mem.mpr ⟨i.val,separate_left E hw⟩))
  have hp := lt_of_lt_of_le hz (H.fork E hw (brim_apart E P hP j.2 i.2 (Ne.symm hh)))
  rw [show x i.val=x j.val from h,sub_self,norm_zero] at hp; exact lt_irrefl _ hp

-- turning asymptotic eventual outer radius to uniform layouts handled in Use
lemma Layout.ratios {v:V} (hv:v∈ rest (heart V)) : s v / s (par E v)∈ Ioc (0:ℝ) 1 := by
  have hp := H.pos _ ((Finset.mem_erase.mp hv).2)
  have he := H.scales _ hv
  exact ⟨div_pos hp (hp.trans_le he), (div_le_one (hp.trans_le he)).mpr he⟩
end YM.OPE.Arboreal
