import YM.MS.Local.Labels
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Physical
import YM.MS.Class.Large
/-!
# Any real homogeneous choice of reps for the physical basis

Real fields and their actual `G` symmetry. Later choose H-equivariance for
orientation as needed. This is the linear free cohomology prescription, with
$⋅$ at order zero and separate continuation rules for nonzero order. We have proved,
not assumed, existence of representatives ending in A-only. Conversion uses only
 these except for exact terms. Projection to four momenta not mixing before poles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.Physical
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open Color Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff
variable {G : Gauge} {F H : Law G} {u : G.El} {h : ℤ} {r : ℕ}
-- Any relative complement (families with H equivariance also admitted). h integer for rank classes
namespace Deck
variable (B : Deck G)
lemma select (hp:F∈Lease G h r 0) (ht:natQ F=0): ∃ H∈ B.carries h r, ∃ K∈ Lease G (h-1) r (-1), H+natQ K=F:= by
   obtain ⟨v,hv,x,⟨u,hu,rfl⟩,rfl⟩:= Submodule.mem_sup.mp (exacts hp ht)
   rw [← B.sup] at hv; obtain ⟨w,hw,z,hz,rfl⟩:=Submodule.mem_sup.mp hv
   obtain ⟨i,hi,rfl⟩ := (show z∈Submodule.map (kills G) (Lease G (h-1) r (-1)) from (show _ ∧ _ from hz).2)
   exact ⟨w,hw,i+u,add_mem hi hu,(by rw [map_add,← add_assoc]; rfl)⟩
lemma separate (hp:F∈ B.carries h r) (ht:H∈ B.carries h r) (hφ : F-H∈ Submodule.map (kills G) (Lease G (h-1) r (-1))): F=H:= by
   have he : F-H∈B.carries h r:= sub_mem hp ht
   have hv : F-H∈ Null G h r:= ⟨B.le he, hφ⟩
   exact sub_eq_zero.mp (by
      have h': F-H∈ B.carries h r ⊓ Null G h r:=⟨he,hv⟩; rw [(B.disjoint _ _).eq_bot] at h'; exact (Submodule.mem_bot _).mp h')

-- large ranks empty. h<0 allowed. Even unit belongs.
lemma ceiling (hv:h<r): B.carries h r=⊥:= by
    apply le_antisymm _ bot_le; intro x he; obtain ⟨_,ha,hk⟩:= lease_one.mp (lease_enough G (B.le he))
    apply (Submodule.mem_bot _).mpr; ext w; by_cases hh:w.length=r
    · have ht : h<fieldDim wfield w:= by rw [← hh] at hv; exact hv.trans_le (length_pay w)
      exact ha.no_tall w (fun v=>Bool.noConfusion v) ht
    exact hk w (fun v=>Bool.noConfusion v) hh

lemma form (B:Deck G) h r i : B.raw h r i∈ B.carries h r:= ((Module.finBasis ℝ _) i).property
lemma combine (B:Deck G) {h r} (hx : F∈ Lease G h r 0) (he:natQ F=0): ∃ p:B.BIndex h r→ℝ, ∃ K∈ Lease G (h-1) r (-1), ∑ i,p i • B.raw h r i + natQ K=F:= by
    obtain ⟨H,hH,K,hK,hl⟩:= B.select hx he; let P:=Module.finBasis ℝ (B.carries h r); let V : B.carries h r:=⟨H,hH⟩
    refine ⟨(P.repr V),K,hK, Eq.trans ?_ hl⟩; rw [show ∑ i,P.repr V i • B.raw _ _ i = (B.carries _ _).subtype (∑ i,P.repr V i • P i) by simp only [map_sum,map_smul]; rfl,P.sum_repr]; rfl
-- unit membership at degree0. choose it explicitly as element; basis rescalings not asserted.
lemma bright0 : Bright (hit (P:=FourP) (A:= Branch G Axis)) where
   weight l i j r := by simp [hit]
   color _ := advance_nil _
   shadow := over_line (G:=G) (A:=Axis) (P:=FourP) (n:=0) (fun i=>i.elim0) -- infer
lemma owner0 (B:Deck G): (hit:Law G)∈ B.carries 0 0:=by
    have ht : Carry G 0 0 ≤ Bed G 0 0 0:=fare ..
    have he : (hit:Law G)∈ Carry G 0 0:= subset_span (mem_setOf.mpr ⟨fun i:Fin 0=>i.elim0,fun _:Fin 0=>0,fun i=>i.elim0,by simp,rfl⟩)
    have hallowed: (hit:Law G)∈ Allowed G 0 0:= byGuide _|>.mpr ⟨he,bright0⟩
    have hN : Null G 0 0=⊥:= by
       apply le_antisymm _ bot_le; intro x h; rcases h with ⟨hx,a,ha,rfl⟩; apply (Submodule.mem_bot _).mpr
       have hv:= (lease_one.mp (lease_enough G hx)); ext w; cases w with
       | nil=> exact q0 a
       | cons i w => exact hv.2.2 _ (fun v=> Bool.noConfusion v) (by simp)
    rw [← B.sup,hN,sup_bot_eq] at hallowed; exact hallowed
end Deck
end YM.MS.Local.Physical
