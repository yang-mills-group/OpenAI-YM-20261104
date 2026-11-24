import YM.Integration.WilsonOriginalAlternativeExchange

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeHybrids
open Finset Function Marker WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V] (J:Census V)
def route (X:Finset V) (j:V):Port:=if j∈X then 0 else 1
def live (s:J.Mode) (X:Finset V):J.Mode:=⟨s.val∩X,J.down s.property _ inter_subset_left⟩
def guard (s:J.Mode) (X:Finset V):J.Mode:=⟨s.val\X,J.down s.property _ sdiff_subset⟩

omit [Fintype V] in
private theorem split {a b s:J.Mode} (merge:Poly.merges a b s) (X:Finset V)
    (enough:a.val⊆X) (outside:Disjoint b.val X):
    a=live J s X ∧ b=guard J s X:=by
  have mem (v:V): (v∈a.val ∨ v∈b.val) ↔ v∈s.val:=by rw [←Finset.mem_union,merge.2]
  constructor
  · apply Subtype.ext;ext v
    change v∈a.val ↔ v∈s.val∩X
    rw [mem_inter,←mem v]
    exact ⟨fun hv=>⟨Or.inl hv,enough hv⟩,fun ⟨h,hx⟩=>h.elim id
      (fun hb=>False.elim (Finset.disjoint_left.mp outside hb hx))⟩
  · apply Subtype.ext;ext v
    change v∈b.val ↔ v∈s.val\X
    rw [mem_sdiff,←mem v]
    exact ⟨fun hb=>⟨Or.inr hb,fun hx=>Finset.disjoint_left.mp outside hb hx⟩,
      fun ⟨h,hx⟩=>h.elim (fun ha=>False.elim (hx (enough ha))) id⟩

/-- Each chosen old cohort is withdrawn together, with its own correlated
ordinary and hard faces. All remaining names contribute their guarded values. -/
theorem original (p:Poly J) (C:V→ℂ) (X:Finset V) (s:J.Mode):
    (read J (route X) (stamped J p C)).part s=(p.part (live J s X))*(∏j∈s.val\X,C j):=by
  have wordval (g:V→ℂ) (t:J.Mode):(word J g).part t=∏i∈t.val,g i:=rfl
  rw [full,Poly.part_mul]
  simp only [Multi.dilation_part,wordval]
  have one (a:J.Mode) (b:J.Mode) :
      (if Poly.merges a b s then ((∏j∈a.val,retain (route X j))*p.part a)*
        ∏j∈b.val,entry C (j,route X j) else 0)=
      if a=live J s X ∧ b=guard J s X then p.part (live J s X)*(∏j∈s.val\X,C j) else 0:=by
    by_cases good:a=live J s X ∧ b=guard J s X
    · rcases good with ⟨rfl,rfl⟩
      have merge:Poly.merges (live J s X) (guard J s X) s:=by
        constructor
        · exact Finset.disjoint_left.mpr fun v hv hz=>(Finset.mem_sdiff.mp hz).2 (Finset.mem_inter.mp hv).2
        · ext v;simp only [live,guard,mem_union,mem_inter,mem_sdiff];tauto
      have orig:(∏j∈s.val∩X,retain (route X j))=1:=by
        apply Finset.prod_eq_one
        intro j hj
        simp [retain,route,(Finset.mem_inter.mp hj).2]
      have trial:(∏j∈s.val\X,entry C (j,route X j))= ∏j∈s.val\X,C j:=by
        apply prod_congr rfl
        intro j hj
        simp [entry,route,(Finset.mem_sdiff.mp hj).2]
      rw [if_pos merge]
      simp only [live,guard,orig,trial,one_mul,eq_self,and_self,if_true]
    · rw [if_neg good]
      split_ifs with merge
      · by_cases enough:a.val⊆X
        · have overlapping:¬Disjoint b.val X:=fun h=>good (split J merge X enough h)
          obtain ⟨v,hv,hx⟩:=Finset.not_disjoint_iff.mp overlapping
          rw [Finset.prod_eq_zero hv (show entry C (v,route X v)=0 by simp [route,entry,hx]),mul_zero]
        · obtain ⟨v,hv,hx⟩:=Finset.not_subset.mp enough
          rw [Finset.prod_eq_zero hv (show retain (route X v)=0 by simp [retain,route,hx]),zero_mul,zero_mul]
      · rfl
  simp_rw [one]
  rw [Finset.sum_eq_single (live J s X)]
  · rw [Finset.sum_eq_single (guard J s X)]
    · simp
    · intro z _ outside;simp [outside]
    · simp
  · intro z _ outside;apply Finset.sum_eq_zero
    intro b _;simp [outside]
  · simp
end YM.Integration.WilsonOriginalAlternativeHybrids
