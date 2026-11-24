import YangMills.WilsonProof.NativeSupport.JointOwnerScore
import YM.MergeProof.Heap

/-! In the full library of native hats the higher same-key groups
contribute zero to an output with just one painted owner. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Finset Lattice RG Wilson Marker Merge.Switch Extra.Trajectories MergeProof MergeProof.Menu
open scoped BigOperators Classical
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}
variable {G : Gauge} {n : Side} {R : Rep G n}
variable (q : I → Hat B R) (w : V→ℝ) (active : Finset V)
variable (origin : ∀ i,∃ v∈(q i).s.val,v∈active)
variable (p : B.Mode) (y : V) (only : p.val∩active={y})

include origin only in
theorem mounted_one_owner (f : Ways (Mound q)) :
    (sound (fun j=>sing (heap q j) w) f).part p =
      ∑ i:I,(sound (singleProbe (Sum.inl i : Mound q)) f).part ((Stock.census Unit).fire ()) *
        (sing (q i) w).part p := by
  let s (i:Mound q) := (heap q i).s
  let c (i:Mound q) := (heap q i).charge/(sumFee (heap q i) w : ℂ)
  have rooted (i : Mound q) : ∃ v∈(s i).val,v∈active := by
    cases i with
    | inl j => exact origin j
    | inr j =>
      obtain ⟨a,ha⟩ := j.2.val.property.1
      obtain ⟨v,hv,act⟩ := origin a
      exact ⟨v,mem_biUnion.mpr ⟨a,ha,hv⟩,act⟩
  change (sound (fun i=>Poly.send (s i) (c i)) f).part p=_
  rw [one_owner s c active rooted p y only,Fintype.sum_sum_type]
  have composite (j : Σ k:logDeck q,Rock q (.logKey k.val)) :
      (Poly.send (s (.inr j)) (c (.inr j))).part p=0 := by
    rw [Poly.part_send,if_neg]
    intro eq
    obtain ⟨i,hi,k,hk,ne⟩ := Finset.one_lt_card.mp (by have := j.2.property; omega : 1<j.2.val.val.card)
    have owns (a : I) (ha : a∈j.2.val.val) : y∈(q a).s.val := by
      obtain ⟨v,hv,act⟩ := origin a
      have inp : v∈p.val := eq ▸ mem_biUnion.mpr ⟨a,ha,hv⟩
      have id := mem_singleton.mp (only ▸ mem_inter.mpr ⟨inp,act⟩ : v∈{y})
      exact id ▸ hv
    exact disjoint_left.mp (j.2.val.property.2.2.1 hi hk ne) (owns i hi) (owns k hk)
  simp_rw [composite,mul_zero,sum_const_zero,add_zero]
  rfl

end YM.Integration.InletSusceptibility.NativeSwitch
