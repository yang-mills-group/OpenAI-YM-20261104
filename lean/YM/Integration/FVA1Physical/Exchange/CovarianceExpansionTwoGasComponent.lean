import YM.Integration.FVA1Physical.CommonHull.InteractingScalarOwnerComponent
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionBondGasWitness

/-! The complete quiet factors outside the common scalar activity component
of two original link configurations cancel exactly before any quotient or
absolute value. The component is allowed to depend jointly on the two fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Finset Lattice RG Wilson Marked Marked.RemoteRoster RoseCut
open private joint_factorizes from YM.Integration.FVA1Physical.CommonHull.InteractingScalarOwnerComponent
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def jointTerritory (A:Activities G n)(e:Edge (Site n))(U V:Fld):Support n:=
  univ.filter fun y=>Relation.ReflTransGen (fun x z=>scalarEdge A U x z ∨ scalarEdge A V x z) e.1 y

private theorem source_inside (A:Activities G n)(e:Edge (Site n))(U V:Fld):e.1∈jointTerritory A e U V:=
  mem_filter.mpr ⟨mem_univ _,Relation.ReflTransGen.refl⟩

private theorem territory_cut (A:Activities G n)(e:Edge (Site n))(U V:Fld)(i:ℕ)
    (live:A.K i U≠0 ∨ A.K i V≠0)(outside:¬lies A (jointTerritory A e U V) i):
    Disjoint (A.forced i).support (jointTerritory A e U V):=by
  apply disjoint_left.mpr;intro z here reached
  apply outside;intro y inside
  apply mem_filter.mpr
  exact ⟨mem_univ _,Relation.ReflTransGen.tail (mem_filter.mp reached).2
    (live.elim (fun h=>Or.inl ⟨i,h,here,inside⟩) (fun h=>Or.inr ⟨i,h,here,inside⟩))⟩

def remotePartition (A:Activities G n)(p:BudgetPoint)(U:Fld)(F:Support n):ℝ:=
  ∑'r:Pool (fun i=>¬lies A F i),regionPartners A U (flags p.threshold U\F) ∅ r.val

private theorem split_gas (A:Activities G n){p:BudgetPoint}{δ w:ℝ}(valid:A.Valid p δ w)
    (U:Fld)(F:Support n)(cut:∀i,A.K i U≠0 → ¬lies A F i → Disjoint (A.forced i).support F):
    A.gas p U=scalarParcel A p U F ∅*remotePartition A p U F:=by
  have sums:=joint_factorizes A p U valid F cut ∅ (fun i hi=>(notMem_empty i hi).elim)
  have quiet(s:Finset ℕ):jointCompanions A p ∅ s U=A.gasOccurrence p s U:=by
    simp only [jointCompanions,Finset.disjoint_empty_left,empty_union,true_and,Activities.gasOccurrence]
  simp_rw [quiet] at sums
  exact sums

/-- The same exterior *signed* scalar partition remains for both physical
configurations. Positivity is unnecessary at this stage. -/
theorem two_field_partition (A:Activities G n){p:BudgetPoint}{δ w:ℝ}(valid:A.Valid p δ w)
    (e:Edge (Site n))(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (same:flags p.threshold U=flags p.threshold V):
    let F:=jointTerritory A e U V
    remotePartition A p U F=remotePartition A p V F ∧
    A.gas p U=scalarParcel A p U F ∅*remotePartition A p U F ∧
    A.gas p V=scalarParcel A p V F ∅*remotePartition A p U F:=by
  intro F
  have equal(i:ℕ)(outside:¬lies A F i):A.K i U=A.K i V:=by
    by_contra moves
    have live:A.K i U≠0 ∨ A.K i V≠0:=by
      by_contra! no;exact moves (no.1.trans no.2.symm)
    have cut:=territory_cut A e U V i live outside
    have change:=ActualGas.variable_owner_endpoints A e U V valid.forced off same i moves
    exact disjoint_left.mp cut change.1 (source_inside ..)
  have fixed:remotePartition A p U F=remotePartition A p V F:=by
    apply tsum_congr;intro r
    simp only [regionPartners,same]
    split
    · exact prod_congr rfl (fun i hi=>equal i (r.property i hi))
    rfl
  have u:=split_gas A valid U F (fun i hi=>territory_cut A e U V i (Or.inl hi))
  have v:=split_gas A valid V F (fun i hi=>territory_cut A e U V i (Or.inr hi))
  exact ⟨fixed,u,(v.trans (congrArg (scalarParcel A p V F ∅*·) fixed.symm))⟩

/-- Every external signed vacuum factor cancels even if it is arbitrarily
small, negative, or supported on other physical failures. The only remaining
mass in the cross-ratio is the common reachable component of the edited link. -/
theorem two_field_local_odds (A:Activities G n){p:BudgetPoint}{δ w:ℝ}(valid:A.Valid p δ w)
    (e:Edge (Site n))(U V:Fld)(off:ActualGas.sameOffBond e U V)
    (before:e.1∉flags p.threshold U)(after:e.1∉flags p.threshold V)
    (up:0<A.gas p U)(vp:0<A.gas p V):
    let F:=jointTerritory A e U V
    let a:=scalarParcel A p U F ∅;let b:=scalarParcel A p V F ∅
    a≠0 ∧ b≠0 ∧ A.gas p U/A.gas p V=a/b ∧
    Real.log (A.gas p U)-Real.log (A.gas p V)=Real.log |a|-Real.log |b|:=by
  intro F a b
  obtain ⟨_,left,right⟩:=two_field_partition A valid e U V off (ActualGas.flags_at_bond e U V off before after)
  let L:=remotePartition A p U F
  change A.gas p U=a*L at left
  change A.gas p V=b*L at right
  have nz:a*L≠0:=left ▸ up.ne'
  have nz':b*L≠0:=right ▸ vp.ne'
  have ap:=left_ne_zero_of_mul nz;have bp:=left_ne_zero_of_mul nz';have lp:=right_ne_zero_of_mul nz
  refine ⟨ap,bp,?_,?_⟩
  · rw [left,right];field_simp
  rw [left,right,Real.log_mul ap lp,Real.log_mul bp lp,Real.log_abs,Real.log_abs];ring

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
