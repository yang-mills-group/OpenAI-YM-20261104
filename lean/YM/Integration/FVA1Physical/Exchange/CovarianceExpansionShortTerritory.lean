import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDebt

/-! Choose the separating region from the connected component of the
original short physical actors. Outside the priced many-site event this
whole region lies in the nominated finite ball. Every omitted active
actor is a genuinely large cover touching that same ball. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Push.AbsoluteSums.Animals
open scoped Classical BigOperators
open private shorten from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSparsePhysicalChain
open private local_span head_walk from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionLocalFailureAlternative
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}

def shortActors (B:Activities G n)(p:BudgetPoint)(K:ℕ→Poly C)(D:ℕ)(i:ℕ):Poly C:=
  if coverNumber p.B (B.forced i).support≤D then K i else 0

def shortTerritory (B:Activities G n)(p:BudgetPoint)(K:ℕ→Poly C)(x:Site n)(D:ℕ):Support n:=
  univ.filter fun y=>Relation.ReflTransGen (Edge B (shortActors B p K D)) x y

theorem original_short_territory (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)
    (x y:Site n)(D m:ℕ)(far:2*m*width p D<separation x y)
    (quiet:U∉crowd p.threshold (neighbors (2*m*width p D) x) m):
    let L:=shortTerritory B p K x D
    let F:=neighbors (2*m*width p D) x
    x∈L ∧ y∉L ∧ L⊆F ∧ ∀i,K i≠0 → cross B L i →
      D<coverNumber p.B (B.forced i).support ∧ ∃z∈F,z∈(B.forced i).support:=by
  intro L F
  let short:=shortActors B p K D
  have noBig:¬LongAt B p short x (2*m) D:=by
    rintro ⟨i,active,large,_⟩
    exact active (if_neg large.not_ge)
  have charged (i:ℕ)(active:short i≠0):(B.forced i).eligible p.threshold U:=by
    apply licensed i
    by_contra dead
    exact active (by simp only [short,shortActors,dead,ite_self])
  have noCrowd:(flags p.threshold U∩F).card<m:=by
    by_contra! crowded
    obtain ⟨S,within,sz⟩:=exists_subset_card_eq crowded
    exact quiet (Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨mem_powersetCard.mpr
      ⟨within.trans inter_subset_right,sz⟩,within.trans inter_subset_left⟩⟩)
  have small:L⊆F:=by
    intro z reach
    obtain ⟨W,walk,sparse,_⟩:=shorten B short x z (mem_filter.mp reach).2
    by_cases shortW:W.length≤2*m
    · exact (neighbors_mem ..).2 (((local_span p walk (2*m) D noBig shortW).1).trans
        (Nat.mul_le_mul_right _ shortW))
    obtain ⟨Q,v,part,limited,len⟩:=head_walk walk sparse (2*m) (Nat.le_of_lt (Nat.lt_of_not_ge shortW))
    have located:= (local_span p part (2*m) D noBig len.le).2
    have scarce:=original_many_flags B p U short charged part limited F (fun i within z seen=>
      (neighbors_mem ..).2 (len ▸ located i within z seen))
    omega
  refine ⟨mem_filter.mpr ⟨mem_univ _,Relation.ReflTransGen.refl⟩,
    fun reach=>far.not_ge ((neighbors_mem ..).1 (small reach)),small,?_⟩
  intro i active crosses
  obtain ⟨z,here,inL⟩:=not_disjoint_iff.mp crosses.2
  refine ⟨?_,z,small inL,here⟩
  by_contra! low
  apply crosses.1
  intro v seen
  have hit:short i≠0:=by simpa only [short,shortActors,if_pos low] using active
  exact mem_filter.mpr ⟨mem_univ v,Relation.ReflTransGen.tail (mem_filter.mp inL).2 ⟨i,hit,here,seen⟩⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
