import YangMills.WilsonProof.NativeSupport.JointSingleScores

/-! In the complete numerical switch the coefficient carrying exactly one
owner has only singleton numerical tickets. This holds even when a mounted
letter represents a large old monomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Finset Marker Merge.Switch Extra.Trajectories
open scoped BigOperators Classical
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}
variable (s : I → B.Mode) (c : I → ℂ) (active : Finset V)
variable (origin : ∀ i,∃ x∈(s i).val,x∈active)
variable (p : B.Mode) (y : V) (only : p.val ∩ active={y})

include origin only in
omit [Fintype I] [DecidableEq I] in
private theorem crowded_zero (D : Finset I) (crowded : 2≤D.card) :
    (∏ i∈D,Poly.send (s i) (c i)).part p=0 := by
  by_contra h
  have nonzero : (∏ i∈D,Poly.send (s i) (c i))≠0 := fun h₀=>h (by rw [h₀]; rfl)
  have fit := fits_of_tagged_prod s nonzero
  rw [tagged_prod s D fit,Poly.part_send] at h
  have eq : p=unionTag s D fit := by_contra fun bad=>h (if_neg bad)
  obtain ⟨i,hi,j,hj,different⟩ := Finset.one_lt_card.mp (by omega : 1<D.card)
  have belongs (k : I) (hk : k∈D) : y∈(s k).val := by
    obtain ⟨v,hv,ha⟩:=origin k
    have in_p : v∈p.val := eq ▸ mem_biUnion.mpr ⟨k,hk,hv⟩
    have id : v=y := mem_singleton.mp (only ▸ mem_inter.mpr ⟨in_p,ha⟩ : v∈{y})
    exact id ▸ hv
  exact disjoint_left.mp (fit.1 hi hj different) (belongs i hi) (belongs j hj)

include origin only in
theorem one_owner (f : Ways I) :
    (sound (fun i=>Poly.send (s i) (c i)) f).part p =
      ∑ i,(sound (singleProbe i) f).part ((Stock.census Unit).fire ()) *
        (Poly.send (s i) (c i)).part p := by
  let z (i:I):=Poly.send (s i) (c i)
  have factor := dilation z f 1
  simp only [one_pow,one_smul] at factor
  have hp : p≠B.quiet := by
    intro e
    have h := only
    rw [e] at h
    change (∅ : Finset V)∩active={y} at h
    simp at h
  have remainder : (∑ D : Finset I,if 2≤D.card then (jet f D:ℂ) • ∏ j∈D,z j else 0).part p=0 := by
    rw [Poly.part_sum]
    refine sum_eq_zero fun D _=>?_
    split
    next h => rw [Poly.part_smul,crowded_zero s c active origin p y only D h,mul_zero]
    next => rfl
  rw [show sound (fun i=>Poly.send (s i) (c i)) f = sound z f from rfl,factor]
  rw [Poly.part_plus,Poly.part_plus,Poly.part_smul,Poly.one_part,if_neg hp,mul_zero,zero_add,remainder,add_zero,Poly.part_sum]
  exact sum_congr rfl fun i _=>Poly.part_smul .. 

end YM.Integration.InletSusceptibility.NativeSwitch
