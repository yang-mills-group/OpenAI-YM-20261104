import YangMills.WilsonProof.NativeSupport.JointMountFlags
import YangMills.WilsonProof.NativeSupport.JointShadow

/-! Every mode without a newly born letter is preserved by the native
forced closure, even when the incoming gas is already marked. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Finset Lattice RG Wilson Marker MergeProof MergeProof.Accent Packet
open scoped BigOperators Classical
variable {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] {G : Gauge} {n : Side}
variable (K : Box n → Config G n → YM.Marker.Poly (YM.Stock.census V)) (u : J → Config G n → YM.Marker.Poly (YM.Stock.census V))
variable (X : J → Support n) (t : ℝ) (U : Config G n) (p : Box n)

theorem erase_closure (D : YM.Marker.Poly (YM.Stock.census V) →+* YM.Marker.Poly (YM.Stock.census V)) :
    D (MergeProof.Accent.closure K u X t p U) =
      MergeProof.Accent.closure (fun i Y=>D (K i Y)) (fun i Y=>D (u i Y)) X t p U := by
  rw [quarters,quarters,map_sum]
  apply sum_congr rfl
  intro A _
  unfold tallyHead
  split
  · rw [map_prod]
    exact prod_congr rfl fun i _=>by cases i <;> rfl
  · exact map_zero D

theorem old_closure (birth : J → V) (newborn : Finset V) (born : ∀ j,birth j∈newborn)
    (coeff : J → Config G n → ℂ) (S : Finset V) (old : Disjoint S newborn)
    (law : ∀ i,K i U≠0 → i.1∩flags t U=i.2 ∧ Sure i) :
    (MergeProof.Accent.closure K (fun i Y=>Poly.send (tag {birth i}) (coeff i Y)) X t p U).part (tag S) =
      (K p U).part (tag S) := by
  let a (v:V) : ℂ := if v∈newborn then 0 else 1
  let D := diagonal a
  let F (i:J) (Y:Config G n) : YM.Marker.Poly (YM.Stock.census V) := Poly.send (tag {birth i}) (coeff i Y)
  have ha : ∏ i∈S,a i=1 :=
    prod_eq_one fun i hi=>if_neg (disjoint_left.mp old hi)
  have kept (P : YM.Marker.Poly (YM.Stock.census V)) : (D P).part (tag S)=P.part (tag S) := by
    change (diagonal a P).part (tag S)=_
    rw [on_part,ha,one_mul]
  have kill : (fun i Y=>D (F i Y)) = fun (_:J) (_:Config G n)=>0 := by
    funext i Y
    change diagonal a (Poly.send (tag {birth i}) (coeff i Y))=0
    rw [on_monomial,prod_singleton,show a (birth i)=0 from if_pos (born i),zero_smul]
  have legal (i : Box n) (h : D (K i U)≠0) : i.1∩flags t U=i.2 ∧ Sure i :=
    law i fun (e : K i U=0)=>h (by rw [e,map_zero])
  change (MergeProof.Accent.closure K F X t p U).part (tag S)=_
  rw [← kept (MergeProof.Accent.closure K F X t p U),erase_closure,kill,closure_no_fresh _ X t U p legal,kept]

end YM.Integration.InletSusceptibility.JointShadow
