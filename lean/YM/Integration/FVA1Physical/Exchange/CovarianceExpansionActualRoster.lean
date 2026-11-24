import YM.Comparison.RG02.Cumulants.Partition
import YM.RG.Activities
import YM.Corona.Fit
import YM.Push.ABSOLUTE_SUMS.Animals

/-! A nonzero connected physical hard entry must have an actually contributing
partition on this field. Each block has one admissible full roster, including
all compulsory vacuum partners and a nonzero local coefficient for each mark.
The reciprocal in every signed term is the original scalar gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseRoster
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}
  (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)

/-- The literal summand in QuadraticLocal.Fusion.Attached.packet, with its actual
regulator, frozen at the given physical field. -/
abbrev roster (S:Finset ℕ):Poly C:=if B.admissible p U S then ∏i∈S,K i else 0

omit [Fintype V] in
private theorem scalar_row (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))(S:Finset ℕ):
    (roster B p U K S).part C.quiet=(B.gasOccurrence p S U:ℂ):=by
  unfold roster Activities.gasOccurrence
  split
  · suffices h:∀L:Finset ℕ,(∏i∈L,K i).part C.quiet=(∏i∈L,B.K i U:ℝ) by exact h S
    intro L
    induction L using Finset.induction with
    | empty => simp
    | insert i L hi ih => rw [prod_insert hi,prod_insert hi,Poly.quiet_mul,K₀,ih,Complex.ofReal_mul]
  simp

/-- The signed expansion is on the real compulsory roster before taking a norm.
Every block uses the same original unmarked gas, including zero-degree partners. -/
theorem original_roster_partition (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))
    (summed:Summable (roster B p U K))(live:B.gas p U≠0)(s:C.Mode):
    let ν:ℂ:=B.gas p U
    let cash:=fun r:C.Mode=>∑'S,(roster B p U K S).part r
    (connected (ν⁻¹ • ∑'S,roster B p U K S)).part s=
      ∑π∈shards C s,mobiusTop π.val.card*(ν⁻¹^π.val.card*∏r∈π.val,cash r.val):=by
  intro ν cash
  have empty:(∑'S,roster B p U K S).part C.quiet=ν:=by
    rw [Poly.share summed]
    simp_rw [scalar_row B p U K K₀]
    exact (Complex.ofReal_tsum _).symm
  have unit:(ν⁻¹ • ∑'S,roster B p U K S).part C.quiet=1:=by
    rw [Poly.part_smul,empty,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr live)]
  rw [log_partition _ unit]
  apply sum_congr rfl
  intro π _
  congr 1
  simp only [Poly.part_smul,Poly.share summed,Finset.prod_mul_distrib,Finset.prod_const,cash]

omit [Fintype V] in
/-- The carrier for a mark occurs in a nonzero contribution to this very
product coefficient, on a subface of the same block. -/
private theorem owner_of_product (S:Finset ℕ)(s:C.Mode)(v:V)(used:v∈s.val)
    (live:(∏i∈S,K i).part s≠0):
    ∃i∈S,∃r:C.Mode,r.val⊆s.val ∧ v∈r.val ∧ (K i).part r≠0:=by
  induction S using Finset.induction generalizing s with
  | empty =>
    have ne:s≠C.quiet:=by
      intro e
      subst s
      exact notMem_empty v used
    exact False.elim (live (by rw [prod_empty,Poly.one_part,if_neg ne]))
  | insert i S hi ih =>
    rw [prod_insert hi,Poly.part_mul] at live
    obtain ⟨a,_,wa⟩:=exists_ne_zero_of_sum_ne_zero live
    obtain ⟨b,_,wb⟩:=exists_ne_zero_of_sum_ne_zero wa
    have split:Poly.merges a b s:=by
      by_contra h
      exact wb (if_neg h)
    rw [if_pos split] at wb
    have left:a.val⊆s.val:=split.2 ▸ subset_union_left
    have right:b.val⊆s.val:=split.2 ▸ subset_union_right
    rcases mem_union.mp (split.2.symm ▸ used) with va|vb
    · exact ⟨i,mem_insert_self ..,a,left,va,left_ne_zero_of_mul wb⟩
    obtain ⟨j,js,r,rb,vr,rj⟩:=ih b vb (right_ne_zero_of_mul wb)
    exact ⟨j,mem_insert_of_mem js,r,rb.trans right,vr,rj⟩

/-- At least one complete signed Möbius summand contributes. For each block
the whole chosen roster is admissible, every one of its actors contributes,
and each occupied mark is carried by a nonzero actual subrow of some actor
in that same roster. The rosters for different blocks may differ. -/
theorem original_contributing_rosters (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))
    (summed:Summable (roster B p U K))(live:B.gas p U≠0)(s:C.Mode)
    (present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,roster B p U K S)).part s≠0):
    ∃π∈shards C s,(mobiusTop π.val.card:ℂ)≠0 ∧
      ∀b∈π.val,∃S:Finset ℕ,B.admissible p U S ∧ (∏i∈S,K i).part b.val≠0 ∧
        (∀i∈S,K i≠0) ∧ ∀v∈b.sites,∃i∈S,∃r:C.Mode,
          r.val⊆b.sites ∧ v∈r.val ∧ (K i).part r≠0:=by
  rw [original_roster_partition B p U K K₀ summed live] at present
  obtain ⟨π,πmem,amount⟩:=exists_ne_zero_of_sum_ne_zero present
  refine ⟨π,πmem,left_ne_zero_of_mul amount,?_⟩
  have all:=right_ne_zero_of_mul (right_ne_zero_of_mul amount)
  intro b actual
  have cash:=prod_ne_zero_iff.mp all b actual
  have somewhere:∃S:Finset ℕ,(roster B p U K S).part b.val≠0:=by
    by_contra! absent
    apply cash
    simp_rw [absent]
    exact tsum_zero
  obtain ⟨S,real⟩:=somewhere
  have legal:B.admissible p U S:=by
    by_contra no
    exact real (by rw [roster,if_neg no];rfl)
  rw [roster,if_pos legal] at real
  refine ⟨S,legal,real,?_,fun v hv=>owner_of_product K S b.val v hv real⟩
  intro i hi dead
  exact real (by rw [prod_eq_zero hi dead];rfl)

open Push.AbsoluteSums.Animals

/-- The nonzero subrow belongs to an actual nonzero summand on an admissible
whole-field roster. The admission condition includes exact coverage of the
original flags and disjointness of the actual supports. -/
def Realized (sites:V→Site n)(s:C.Mode)(v:V)(i:ℕ):Prop:=
  ∃(S:Finset ℕ)(r b:C.Mode)(z:Site n), i∈S ∧ B.admissible p U S ∧
    (∀j∈S,K j≠0 ∧ (B.forced j).eligible p.threshold U) ∧
    (∏j∈S,K j).part b≠0 ∧ r.val⊆b.val ∧ b.val⊆s.val ∧
    v∈r.val ∧ (K i).part r≠0 ∧ sites v∈(B.forced i).support ∧
    z∈(B.forced i).inventory ∧ z∈flags p.threshold U ∧
    separation (sites v) z≤coverNumber p.B (B.forced i).support*(4*p.B+2)+2*p.B

/-- Every distinct occupied leg of this very connected reading has a
nonzero filed coefficient in a contributing full physical roster. On a
locally healthy ball the same actor is long at every admitted radius. -/
theorem original_geometric_owner (K₀:∀i,(K i).part C.quiet=(B.K i U:ℂ))
    (summed:Summable (roster B p U K))(live:B.gas p U≠0)(sites:V→Site n)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)
    (carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,sites v∈(B.forced i).support)
    (s:C.Mode)(present:(connected (((B.gas p U:ℂ)⁻¹) • ∑'S,roster B p U K S)).part s≠0)
    (v:V)(used:v∈s.val):
    ∃i,Realized B p U K sites s v i ∧ ∀D:ℕ,
      (∀z∈neighbors (D*(4*p.B+2)+2*p.B) (sites v),z∉flags p.threshold U) →
        D<coverNumber p.B (B.forced i).support:=by
  obtain ⟨π,ok,_,blocks⟩:=original_contributing_rosters B p U K K₀ summed live s present
  have gathers:unionOf π=s:=(mem_filter.mp ok).2
  have used':v∈(unionOf π).val:=gathers.symm ▸ used
  obtain ⟨b,bp,vb⟩:=mem_biUnion.mp used'
  have face:b.sites⊆s.val:=by
    intro a ha
    rw [←gathers]
    exact mem_biUnion.mpr ⟨b,bp,ha⟩
  obtain ⟨S,legal,contributes,all,owners⟩:=blocks b bp
  obtain ⟨i,here,r,subface,vr,actual⟩:=owners v vb
  have grant:=licensed i (all i here)
  have root:=carry i r actual v vr
  obtain ⟨z,flag⟩:=(B.forced i).inventory_ne
  obtain ⟨inside,failed⟩:=mem_inter.mp (grant.1.symm ▸ flag :
    z∈(B.forced i).support∩flags p.threshold U)
  have near:=Corona.extent (B.forced i).support p.B root inside
  refine ⟨i,⟨S,r,b.val,z,here,legal,fun j hj=>⟨all j hj,licensed j (all j hj)⟩,
    contributes,subface,face,vr,actual,root,flag,failed,near⟩,?_⟩
  intro D cold
  by_contra! short
  have size:=Nat.add_le_add_right (Nat.mul_le_mul_right (4*p.B+2) short) (2*p.B)
  exact cold z ((neighbors_mem _ _ _).2 (near.trans size)) failed

end YM.Integration.FVA1Physical.Exchange.RoseRoster

