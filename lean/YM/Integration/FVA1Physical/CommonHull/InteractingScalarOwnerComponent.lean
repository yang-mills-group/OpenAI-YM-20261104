import YM.Integration.FVA1Physical.CommonHull.InteractingRegionalActorBudget
import YM.Integration.FVA1Physical.Marked.JointOwnerCavity

/-! Once a finite marked owner set is chosen, only genuinely live unmarked
operators can connect its vacuum companions to additional sites. Cancel
all unrelated original scalar components exactly, including arbitrary
exterior compulsory failures, before pricing the marked residue. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Lattice RG Wilson Exchange Exchange.RoseCut
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}(B:Activities G n)(p:BudgetPoint)(U:Config G n)

def scalarEdge (x y:Site n):Prop:=∃i,B.K i U≠0 ∧ x∈(B.forced i).support ∧ y∈(B.forced i).support

def scalarTerritory (Y:Support n):Support n:=
  univ.filter fun y=>∃x∈Y,Relation.ReflTransGen (scalarEdge B U) x y

private theorem territory_contains (Y:Support n):Y⊆scalarTerritory B U Y:=
  fun y hy=>mem_filter.mpr ⟨mem_univ _,y,hy,Relation.ReflTransGen.refl⟩

private theorem territory_closed (Y:Support n)(i:ℕ)(nz:B.K i U≠0)(out:¬lies B (scalarTerritory B U Y) i):
    Disjoint (B.forced i).support (scalarTerritory B U Y):=by
  apply disjoint_left.mpr;intro v here seen
  obtain ⟨x,hx,reach⟩:=(mem_filter.mp seen).2
  apply out;intro z hz
  exact mem_filter.mpr ⟨mem_univ _,x,hx,reach.tail ⟨i,nz,here,hz⟩⟩

def regionPartners (E:Support n)(l s:Finset ℕ):ℝ:=
  if Disjoint l s ∧ Regional B E (l∪s) then ∏i∈s,B.K i U else 0

abbrev scalarParcel (F:Support n)(l:Finset ℕ):ℝ:=
  ∑'s:Pool (lies B F),regionPartners B U (flags p.threshold U∩F) l s.val

private theorem marked_split (A C D:Prop) [Decidable A] [Decidable C] [Decidable D]
    (truth:A↔C∧D) (a b c:ℝ)(factor:a=b*c):
    (if A then a else 0)=(if C then b else 0)*(if D then c else 0):=by
  by_cases left:C
  · by_cases right:D
    · rw [if_pos (truth.mpr ⟨left,right⟩),if_pos left,if_pos right,factor]
    rw [if_neg (fun yes=>right (truth.mp yes).2),if_neg right,mul_zero]
  rw [if_neg (fun yes=>left (truth.mp yes).1),if_neg left,zero_mul]

private theorem partner_formula (F:Support n)(cut:∀i,B.K i U≠0→¬lies B F i→Disjoint (B.forced i).support F)
    (l:Finset ℕ)(inside:∀i∈l,lies B F i)(s:Pool (lies B F))(r:Pool (fun i=>¬lies B F i)):
    jointCompanions B p l (s.val∪r.val) U=
      regionPartners B U (flags p.threshold U∩F) l s.val*
      regionPartners B U (flags p.threshold U\F) ∅ r.val:=by
  by_cases all:∀i∈r.val,B.K i U≠0
  swap
  · push Not at all;obtain ⟨i,hi,dead⟩:=all
    have zero:(∏j∈r.val,B.K j U)=0:=prod_eq_zero hi dead
    have gone:(∏j∈s.val∪r.val,B.K j U)=0:=prod_eq_zero (mem_union_right _ hi) dead
    simp only [jointCompanions,gone,ite_self,regionPartners,zero,mul_zero]
  have lr:Disjoint l r.val:=disjoint_left.mpr (fun i li ri=>r.property i ri (inside i li))
  have inInner:∀i∈l∪s.val,lies B F i:=fun i hi=>(mem_union.mp hi).elim (inside i) (s.property i)
  have admission:=true_cut_admission B p U F (l∪s.val) r.val inInner (fun i hi=>cut i (all i hi) (r.property i hi))
  have ds:Disjoint l (s.val∪r.val) ↔ Disjoint l s.val:=by rw [disjoint_union_right];simp only [lr,and_true]
  have truth:(Disjoint l (s.val∪r.val) ∧ B.admissible p U (l∪(s.val∪r.val))) ↔
      ((Disjoint l s.val ∧ Regional B (flags p.threshold U∩F) (l∪s.val)) ∧
        (Disjoint (∅:Finset ℕ) r.val ∧ Regional B (flags p.threshold U\F) (∅∪r.val))):=by
    simp only [ds,←union_assoc,admission,Finset.disjoint_empty_left,empty_union,true_and,and_assoc]
  exact marked_split _ _ _ truth _ _ _ (prod_union (pools_disjoint _ s r))

private theorem partner_summable {δ κ:ℝ}(valid:B.Valid p δ κ)(field:Finset ℕ→ℝ)
    (gate:∀s,field s=0 ∨ field s=∏i∈s,B.K i U):Summable field:=by
  obtain ⟨v,hs,receipt⟩:=Activities.K_total valid.boundK
  have all:Summable (fun S:Finset ℕ=>∏i∈S,v i):=summable_finsetProd_of_summable_nonneg (fun i=>(receipt i).1) hs
  apply Summable.of_norm
  refine all.of_nonneg_of_le (fun _=>norm_nonneg _) fun S=>?_ 
  rcases gate S with zero|full
  · rw [zero,norm_zero];exact prod_nonneg (fun i _=>(receipt i).1)
  rw [full,norm_prod];exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(receipt i).2 U)

private theorem joint_sum {δ κ:ℝ}(valid:B.Valid p δ κ)(l:Finset ℕ):
    Summable (fun s=>jointCompanions B p l s U):=by
  apply partner_summable B p U valid;intro s;unfold jointCompanions;split
  · exact Or.inr rfl
  exact Or.inl rfl

private theorem regional_sum {δ κ:ℝ}(valid:B.Valid p δ κ)(E:Support n)(l:Finset ℕ)(c:ℕ→Prop):
    Summable (fun s:Pool c=>regionPartners B U E l s.val):=by
  have all:Summable (regionPartners B U E l):=by
    apply partner_summable B p U valid;intro s;unfold regionPartners;split
    · exact Or.inr rfl
    exact Or.inl rfl
  exact all.comp_injective (Subtype.val_injective (p:=fun L:Finset ℕ=>∀i∈L,c i))

private theorem factor_series {A X Y:Type*}(h:X×Y≃A)(f:A→ℝ)(g:X→ℝ)(j:Y→ℝ)
    (fin:Summable f)(inl:Summable g)(ex:Summable j)(term:∀z:X×Y,f (h z)=g z.1*j z.2):
    (∑'s,f s)=(∑'x,g x)*∑'y,j y:=by
  have integr:Summable (fun z:X×Y=>f (h z)):=h.summable_iff.mpr fin
  have prod:Summable (fun z:X×Y=>g z.1*j z.2):=integr.congr term
  calc _=(∑'z:X×Y,f (h z)):=(h.tsum_eq f).symm
       _=(∑'z:X×Y,g z.1*j z.2):=tsum_congr term
       _=_:=(inl.tsum_mul_tsum ex prod).symm

private theorem joint_factorizes {δ κ:ℝ}(valid:B.Valid p δ κ)(F:Support n)
    (cut:∀i,B.K i U≠0→¬lies B F i→Disjoint (B.forced i).support F)
    (l:Finset ℕ)(inside:∀i∈l,lies B F i):
    (∑'s,jointCompanions B p l s U)=scalarParcel B p U F l*
      ∑'r:Pool (fun i=>¬lies B F i),regionPartners B U (flags p.threshold U\F) ∅ r.val:=
  factor_series (combine (lies B F)) (fun s=>jointCompanions B p l s U)
    (fun s:Pool (lies B F)=>regionPartners B U (flags p.threshold U∩F) l s.val)
    (fun r:Pool (fun i=>¬lies B F i)=>regionPartners B U (flags p.threshold U\F) ∅ r.val)
    (joint_sum B p U valid l) (regional_sum B p U valid _ _ _) (regional_sum B p U valid _ _ _)
    (fun z=>partner_formula B p U F cut l inside z.1 z.2)

/-- Exact normalized scalar companion for any filed marked owner set l in
one occurring raw coefficient. Only the supports of these literal owners
and nonzero scalar rows enter the denominator. Arbitrarily many
incompatible marked-only rows elsewhere cannot enlarge this component. -/
theorem original_scalar_owner_component {δ κ:ℝ}(valid:B.Valid p δ κ)(l:Finset ℕ)(vac:B.gas p U≠0):
    let F:=scalarTerritory B U (ownerUnion B l)
    scalarParcel B p U F ∅≠0 ∧ (∑'s,jointCompanions B p l s U)/B.gas p U=
      scalarParcel B p U F l/scalarParcel B p U F ∅:=by
  intro F
  let outside:=∑'r:Pool (fun i=>¬lies B F i),regionPartners B U (flags p.threshold U\F) ∅ r.val
  have carry(i)(hi:i∈l):lies B F i:=fun z hiZ=>territory_contains B U _ (mem_biUnion.mpr ⟨i,hi,hiZ⟩)
  have cut:=territory_closed B U (ownerUnion B l)
  have num:(∑'s,jointCompanions B p l s U)=scalarParcel B p U F l*outside:=
    joint_factorizes B p U valid F cut l carry
  have den0:=joint_factorizes B p U valid F cut ∅ (fun i hi=>(notMem_empty i hi).elim)
  have quiet(s:Finset ℕ):jointCompanions B p ∅ s U=B.gasOccurrence p s U:=by
    simp only [jointCompanions,Finset.disjoint_empty_left,empty_union,true_and,Activities.gasOccurrence]
  simp_rw [quiet] at den0
  have den:B.gas p U=scalarParcel B p U F ∅*outside:=den0
  have both:scalarParcel B p U F ∅*outside≠0:=den ▸ vac
  refine ⟨left_ne_zero_of_mul both,?_⟩
  rw [num,den];field_simp [left_ne_zero_of_mul both,right_ne_zero_of_mul both]

end YM.Integration.FVA1Physical.Marked.RemoteRoster
