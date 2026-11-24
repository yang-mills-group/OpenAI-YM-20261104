import YM.Push.ABSOLUTE_SUMS.Path
import YM.Push.PRICE_COMPILER.Canonical
/-!
## Choosing the marker support conventions

Passive stamps use an origin and an arbitrary support containing it. Keep witnesses
for all their extra tests, auxiliary Hilbert-field arguments etc, in such supports;
they will travel by `T.image parent` not changing them when particular runs of those
tests vanish. Keep also a **connector** walk along actual nearest-neighbor bonds from
the origin visiting every stencil site. Rendering will buy not merely the minimal lift
metric of the furthest site but the whole winding length! Reserve margin in the announced
length of each `Chart`; can use more when address layouts spend more than this single skeleton.
(For Λ readers based on continuum probes use supports including any Taylor segment and
an extra length allowance charging those Taylor lengths.)

All geometry is volume-independent. No simplification about connected covers of sparse stencils
required. We use NEW short walks at the coarser level; their lift on future regulators won't
commute with the stencil selection. This incurs spatial price (before-L constants). Visits are
passive, not parallel transport substitutions in any Atom. Machine labels that need real field-
transport keep their Atom data under the complete footprint. This file is for the analytic regular
kernel presentation; hard & special error masks can keep on the projected ancestral stencils
without a new path representative (live along old render). For a concrete application choose the
finer support to include all addressed paths of the corresponding test protocol. When a Mark can
use several address budgets, one may key names more finely (keep exclusion across disjoint slots).

The path through every projected stencil also reconciles label retention with work at the actual
θ.Not assuming a minimization over supports/terms, even at fixed period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Lattice Laurent Finset Push Push.AbsoluteSums
open scoped Classical BigOperators
variable {n c : Side} {θ : Type*}
namespace Cable

/-- One deterministic orientation (lexicographic) and deterministic lifted differences.
Use as an actual connector, not a ball count. Reaching y through the projected path, even if
other lifted choices also reach y. Many-marker stencils can add independent winding components. -/
def link (x y : Site n) : Walk := route 0 (lift (y-x)) 1
@[simp] lemma link_stop (x y : Site n) : stop x (link x y) = y := by
    unfold link
    nth_rw 1 [show x = x + wrap n 0 from (by simp)]
    rw [Work.E03.stop_add_left, ← wrap_stop_cover, route_end, wrap_lift]; abel
lemma link_height (x y : Site n) : (link x y).length ≤ 4 * separation x y := by
    have h := PriceCompiler.Canonical.sizeSlot ⟨(0,1),by decide⟩ (lift (y-x))
    change (link x y).length + 4 = _ at h
    apply (Nat.add_right_cancel h).trans_le
    rw [separation_comm x]; calc
    _ ≤ ∑ _i:Axis, separation y x := sum_le_sum (fun i _=> component_le _ _)
    _ = _ := by simp [Axis]

variable (x y z : Site n)
namespace Native
open Paths
lemma first (w : Walk) : x ∈ Paths.native x w := by cases w <;> simp [Paths.native,visits]
lemma tip (w : Walk) : stop x w ∈ Paths.native x w := by
   induction w generalizing x with
   | nil=> simp [stop,Paths.native,visits]
   | cons a w IH=> unfold Paths.native; rw [List.mem_toFinset]; exact List.mem_cons_of_mem x (List.mem_toFinset.mp (IH (x+a.vec)))
lemma combine (w v : Walk) : Paths.native x (w++v) = Paths.native x w ∪ Paths.native (stop x w) v := by
   induction w generalizing x with
   | nil=> rw [List.nil_append,show stop x []=x from rfl, union_eq_right.mpr]; simp [Paths.native,visits]; exact List.mem_toFinset.mp (first x v) -- check simp
   | cons a w IH=>
      rw [show (a::w)++v = a::(w++v) from rfl];
      change (x :: visits (x+a.vec) (w++v)).toFinset = (x :: visits (x+a.vec) w).toFinset ∪ (Paths.native _ v);
      rw [List.toFinset_cons,List.toFinset_cons, show (visits (x+a.vec) (w++v)).toFinset = _ from IH (x+a.vec)]; exact (Finset.insert_union ..).symm
end Native
open Paths Native
lemma circuit {l:ℕ} (D : Support n) (h:∀ y∈D,separation x y≤ l):
    ∃ w:Walk, stop x w=x ∧ D ⊆ Paths.native x w ∧ w.length ≤ 8*l*D.card := by
    induction D using Finset.induction with
    | empty=> exact ⟨[],rfl,Finset.empty_subset _,Nat.zero_le _⟩
    | insert a D ha IH=>
       obtain ⟨w,he,hD,hw⟩:= IH (fun y hy=> h y (mem_insert_of_mem hy)); let t:=link x a; let t':=link a x
       have h₁:stop x t=a:= link_stop ..; have h₂:stop a t'=x:= link_stop ..
       refine ⟨t++(t'++w),by rw [stop_append,h₁,stop_append,h₂,he],?_,?_⟩
       · rw [combine,h₁,combine,h₂]; exact insert_subset (Finset.mem_union_left _ (h₁ ▸ tip x t)) (Subset.trans hD (Subset.trans Finset.subset_union_right Finset.subset_union_right)) -- insert_subset? API
       have h₃:= link_height x a; have h₄:= link_height a x; rw [separation_comm a x] at h₄
       have hx:= h a (mem_insert_self ..); unfold t t'; rw [card_insert_of_notMem ha,List.length_append,List.length_append]; nlinarith only [hx,h₃,h₄,hw]

section hauling
variable (q:Ratio c n)
open Corona
local notation "L"=> q.count.val
local notation "α"=> q.parent
local notation "Ω"=> (2+2+1)^4
/-- cost of one new walk segment -/
def links : ℕ:= 16*(2+2+1)^4+8

lemma segment (w: Walk)(he:w.length≤ q.count.val):
    ∃ v: Walk, stop (q.parent x) v=q.parent (stop x w) ∧ (Paths.native x w).image q.parent ⊆ Paths.native (q.parent x) v ∧ v.length≤ links := by
    let D:=(Paths.native x w).image q.parent; let y:= q.parent x
    have h(i)(hi:i∈D): separation y i ≤ 2 := by
       obtain ⟨i,hiv,rfl⟩:= Finset.mem_image.mp hi
       apply Nat.le_of_mul_le_mul_left _ (q.count.property) -- binder b?
       have hp := Paths.to_ball x w hiv; have hk:= foreshorten q x i; exact hk.trans ((Nat.add_le_add_right (hp.trans he) L).trans (by omega : L+L≤ L*2))
    obtain ⟨ω,hω,hD,hb⟩:= circuit y D h
    have hc:D.card ≤ ((2+2+1)^4) := le_trans (Finset.card_le_card (t:=halo 2 {y}) (fun i hi=> halo_spec.mpr ⟨_,mem_singleton_self _,h i hi⟩)) (by simpa using Corona.halo_size ({y}:Support c) 2)
    let z:= q.parent (stop x w); let τ:= link y z
    refine ⟨ω++τ, ?_, ?_, ?_⟩
    · rw [stop_append,hω]; exact link_stop ..
    · rw [Native.combine,hω]; exact hD.trans Finset.subset_union_left
    rw [List.length_append]; unfold τ; have hh:= h z (Finset.mem_image_of_mem _ (Native.tip x w)); have hs:= link_height y z; unfold links; norm_num at *; omega -- might expensive

/-- Keep old T, even if w length substantially exceeds it.
 All lengths charged *before* asking for the walk. -/
def mass (q : Ratio c n)(ℓ:ℕ) := Cable.links*(1+ℓ/q.count.val)

lemma caravan (w : Walk) : ∃ w' : Walk, stop (α x) w'=α (stop x w) ∧ (Paths.native x w).image α ⊆ Paths.native (α x) w' ∧ w'.length ≤ mass q w.length := by
   suffices he : ∀ i:ℕ,∀ x:Site n,∀ w: Walk,w.length=i→∃ w': Walk,stop (q.parent x) w'=q.parent (stop x w) ∧ (Paths.native x w).image q.parent ⊆ Paths.native (q.parent x) w' ∧ w'.length≤ mass q i from he _ x w rfl
   intro i; induction i using Nat.strong_induction_on with | h i IH=>?_ -- tactic syntax
   intro x w hw; by_cases h:i≤L
   · obtain ⟨v,hv,hh,hL⟩:= segment x q w (hw ▸ h); exact ⟨v,hv,hh,hL.trans (Nat.le_mul_of_pos_right _ (by positivity))⟩ -- use positivity
   have hδ: 0<L:=q.count.property
   let u:=w.take L; let v:=w.drop L; have hu:u.length=L:=by unfold u; rw [List.length_take,hw,min_eq_left (by omega)]
   have he :u++v=w:=List.take_append_drop ..; have h':v.length=i-L:= (List.length_drop ..).trans (hw ▸ rfl)
   let y:= stop x u; obtain ⟨κ,hκ,hK,hj⟩:= segment x q u hu.le
   obtain ⟨ζ,hz,hZ,ha⟩:= IH (i-L) (by omega) y v h'
   refine ⟨κ++ζ,?_,?_,?_⟩
   · rw [stop_append,hκ,hz]; nth_rw 1 [← he]; rw [stop_append]
   · nth_rw 1 [← he]; rw [Native.combine,image_union,Native.combine,hκ]; exact Finset.union_subset_union hK hZ
   rw [List.length_append]; apply (Nat.add_le_add hj ha).trans; unfold mass; let t:=i-L; have hD:t+L=i:= by unfold t; omega
   have hi : i/L=t/L+1:=by nth_rw 1 [← hD]; exact Nat.add_div_right t hδ
   rw [hi]; exact le_of_eq (by unfold t; ring)
end hauling
end Cable
end YM.QuadraticLocal.Earn
