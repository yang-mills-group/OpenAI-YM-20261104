import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingInvoice

/-! Only m deterministic candidate cuts are needed. The selector observes
original flags in a fixed finite torus ball. On a selected cut every active
crossing actor is truly long, even if it carries no occupied source. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset MeasureTheory Lattice RG Wilson Marker Push.AbsoluteSums.Animals
open scoped Classical
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}

def annulus (x:Site n)(j w:ℕ):Support n:=neighbors ((j+1)*(2*w)) x \ neighbors (j*(2*w)) x

def clearAnnulus (θ:ℝ)(x:Site n)(j w:ℕ):Set (Config G n):=
  {U|Disjoint (flags θ U) (annulus x j w)}

def firstClear (θ:ℝ)(x:Site n)(j w:ℕ):Set (Config G n):=
  clearAnnulus θ x j w ∩ ⋂ l:Fin j,(clearAnnulus θ x l w)ᶜ

theorem annulus_measurable (θ:ℝ)(x:Site n)(j w:ℕ):MeasurableSet (clearAnnulus (G:=G) θ x j w):=by
  have eq:clearAnnulus (G:=G) θ x j w=⋂ v:↥(annulus x j w),{U:Config G n|v.val∉flags θ U}:=by
    ext U
    change Disjoint (flags θ U) (annulus x j w) ↔ _
    rw [disjoint_left,Set.mem_iInter]
    exact ⟨fun h v seen=>h seen v.property,fun h z seen inside=>h ⟨z,inside⟩ seen⟩
  rw [eq]
  exact MeasurableSet.iInter fun v=>(flags_open ..).measurableSet.compl

theorem selector_measurable (θ:ℝ)(x:Site n)(j w:ℕ):MeasurableSet (firstClear (G:=G) θ x j w):=
  (annulus_measurable θ x j w).inter (MeasurableSet.iInter fun l:Fin j=>(annulus_measurable θ x l w).compl)

private theorem band_distance (x z:Site n)(j w:ℕ):z∈annulus x j w ↔
    j*(2*w)<separation x z ∧ separation x z≤(j+1)*(2*w):=by
  change z∈neighbors ((j+1)*(2*w)) x \ neighbors (j*(2*w)) x ↔ _
  rw [mem_sdiff,neighbors_mem,neighbors_mem]
  omega

/-- The first empty annulus is selected using only genuine flags on one
fixed original configuration. Its candidate list has exactly m members. -/
theorem select_annulus (θ:ℝ)(U:Config G n)(x:Site n)(m w:ℕ)
    (outside:U∉crowd θ (neighbors (m*(2*w)) x) m):
    ∃j:Fin m,U∈firstClear θ x j w:=by
  let F:=neighbors (m*(2*w)) x
  have few:(flags θ U∩F).card<m:=by
    by_contra! crowded
    obtain ⟨S,within,sz⟩:=exists_subset_card_eq crowded
    exact outside (Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨mem_powersetCard.mpr
      ⟨within.trans inter_subset_right,sz⟩,within.trans inter_subset_left⟩⟩)
  have some:∃j:ℕ,j<m ∧ U∈clearAnnulus θ x j w:=by
    by_contra none
    have classified (j:Fin m):∃z∈flags θ U,z∈annulus x j w:=by
      by_contra! closed
      exact none ⟨j,j.isLt,disjoint_left.mpr closed⟩
    let z:=fun j:Fin m=>(classified j).choose
    have seen (j:Fin m):z j∈flags θ U ∧ z j∈annulus x j w:=(classified j).choose_spec
    have ordered (j k:Fin m)(l:j<k):z j≠z k:=by
      intro eq
      have far:=((band_distance x _ k w).mp (seen k).2).1
      have near:=((band_distance x _ j w).mp (seen j).2).2
      have space:((j:ℕ)+1)*(2*w)≤(k:ℕ)*(2*w):=Nat.mul_le_mul_right _ l
      rw [eq] at near
      omega
    let f:=fun j:Fin m=> (⟨z j,mem_inter.mpr ⟨(seen j).1,(neighbors_mem ..).2
      (((band_distance ..).mp (seen j).2).2.trans (Nat.mul_le_mul_right _ j.isLt))⟩⟩:↥(flags θ U∩F))
    have inject:Function.Injective f:=by
      intro j k h
      have eq:z j=z k:=congrArg Subtype.val h
      rcases lt_trichotomy j k with lt|same|gt
      · exact False.elim (ordered j k lt eq)
      · exact same
      exact False.elim (ordered k j gt eq.symm)
    have many:=Fintype.card_le_of_injective f inject
    simp only [Fintype.card_fin, Fintype.card_coe] at many
    omega
  let k:=Nat.find some
  have chosen:k<m ∧ U∈clearAnnulus θ x k w:=Nat.find_spec some
  refine ⟨⟨k,chosen.1⟩,chosen.2,Set.mem_iInter.mpr (fun l=>?_)⟩
  exact fun clear=>Nat.find_min some l.isLt ⟨l.isLt.trans chosen.1,clear⟩

/-- On this nominated deterministic cut every crossing active hard actor
carries its compulsory flag outside the empty band and therefore has cover>D. -/
theorem selected_long (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (licensed:∀i,K i≠0 → (B.forced i).eligible p.threshold U)(x:Site n)(j D:ℕ)
    (clear:U∈clearAnnulus p.threshold x j (width p D)):
    let w:=width p D
    let L:=neighbors (j*(2*w)+w) x
    ∀i,K i≠0 → cross B L i → D<coverNumber p.B (B.forced i).support ∧ ∃z∈L,z∈(B.forced i).support:=by
  intro w L i active between
  obtain ⟨z,zin,near⟩:=not_disjoint_iff.mp between.2
  refine ⟨?_,z,near,zin⟩
  by_contra! short
  obtain ⟨v,vin,away⟩:=Finset.not_subset.mp between.1
  obtain ⟨f,failed⟩:=(B.forced i).inventory_ne
  have field: f∈(B.forced i).support ∩ flags p.threshold U:=(licensed i active).1.symm ▸ failed
  have diam (a b:Site n)(m:a∈(B.forced i).support)(h:b∈(B.forced i).support):separation a b≤w:=
    (Corona.extent _ p.B m h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ short) _)
  have d1:=diam z f zin (mem_inter.mp field).1
  have d2:=diam f v (mem_inter.mp field).1 vin
  have zz:separation x z≤j*(2*w)+w:=(neighbors_mem ..).1 near
  have vv:j*(2*w)+w<separation x v:=Nat.lt_of_not_ge fun g=>away ((neighbors_mem ..).2 g)
  have t1:=separation_triangle x z f
  have t2:=separation_triangle x f v
  apply disjoint_left.mp clear (mem_inter.mp field).2
  apply (band_distance ..).2
  change j*(2*w)<separation x f ∧ separation x f≤(j+1)*(2*w)
  rw [Nat.succ_mul j (2*w)]
  omega

end YM.Integration.FVA1Physical.Exchange.RoseCut
