import YangMills.WilsonProof.NativeSupport.CalibratedPacking
import YangMills.WilsonProof.NativeSupport.TranslatedLayer
import YangMills.WilsonProof.NativeSupport.InletColors

/-! Disjoint coarse translates of an arbitrary fixed physical pattern. The
number of rejected translates depends on its arity, regardless of the distance
between slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open scoped Classical BigOperators
variable {n c : Side} {V : Type*} [Fintype V]

private def near (o : V→Site n) (R : ℕ) (x : Site n) :=
  insert x (univ.biUnion fun i : V=>univ.biUnion fun j : V=>halo R {x+o i-o j})

private theorem near_at (o : V→Site n) (R : ℕ) (x y : Site n) :
    y∈near o R x ↔ y=x ∨ ∃ i j, separation (x+o i) (y+o j) ≤ R := by
  have moved (i j : V) : separation (x+o i-o j) y = separation (x+o i) (y+o j) := by
    unfold separation
    congr 1
    abel
  simp [near,halo_spec,moved]

private theorem near_count (o : V→Site n) (R : ℕ) (x : Site n) :
    (near o R x).card ≤ 1+(Fintype.card V)^2*(2*R+1)^4 := by
  have singleton (y : Site n) : (halo R {y}).card ≤ (2*R+1)^4 := by
    simpa only [card_singleton,one_mul,two_mul] using Corona.halo_size ({y} : Support n) R
  unfold near
  have inner (i : V) : (univ.biUnion fun j : V=>halo R {x+o i-o j}).card
      ≤ Fintype.card V*(2*R+1)^4 := by
    refine card_biUnion_le.trans ?_
    exact (sum_le_sum fun j _=>singleton _).trans_eq (by simp)
  apply (card_insert_le ..).trans
  rw [add_comm 1,add_le_add_iff_right]
  refine card_biUnion_le.trans ?_
  exact (sum_le_sum fun i _=>inner i).trans_eq (by simp [pow_two,Nat.mul_assoc])

theorem packed_copies (o : V→Site n) (R : ℕ) :
    ∃ I : Finset (Site n), Fintype.card (Site n) ≤ I.card*(1+(Fintype.card V)^2*(2*R+1)^4) ∧
      ∀ x∈I,∀ y∈I,x≠y → ∀ i j,R<separation (x+o i) (y+o j) := by
  obtain ⟨I,_,apart,dense⟩:=sparse_subset (near o R)
    (fun x=>(near_at o R _ _).mpr (.inl rfl))
    (fun x y h=>(near_at o R _ _).mpr (by
      rcases (near_at o R _ _).mp h with e | ⟨i,j,le⟩
      · exact .inl e.symm
      · exact .inr ⟨j,i,(separation_comm ..) ▸ le⟩)) _
    (near_count o R) univ
  exact ⟨I,(by simpa only [Finset.card_univ] using dense),fun x hx y hy h i j=>lt_of_not_ge fun ht=>
    apart x hx y hy h ((near_at o R _ _).mpr (.inr ⟨i,j,ht⟩))⟩

private theorem parent_move (r : Ratio c n) (b : Site c) (x : Site n) :
    r.parent (r.embed b+x)=b+r.parent x := by
  have h : r.embed b+x=r.assemble (b+r.parent x,r.residue x) := by
    nth_rw 1 [←r.unpack_at x]
    unfold Ratio.assemble
    change r.root _+(r.root _+_)=r.root _+_
    rw [map_add,add_assoc]
  rw [h,r.assemble_parent]

theorem ancestor_move (d : Descent n c) (b : Site c) (x : Site n) :
    home d (liftSite d b+x)=b+home d x := by
  induction d with
  | nil => rfl
  | push S T d ih =>
    change S.ratio.parent (home d (liftSite d (S.ratio.embed b)+x))=b+S.ratio.parent (home d x)
    rw [ih,parent_move]

end YM.Integration.InletSusceptibility.Packet
