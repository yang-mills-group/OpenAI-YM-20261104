import YM.Integration.WilsonForcedReplicaBoundary
import YM.Push.GRID_APPROXIMATION.Hit

/-! Every pair of contributing complete labelled coarse covers pays the actual site
separation with its genuine sum of support costs. This applies before any field average. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonForcedReplicaDistance
open Finset Function Lattice Lattice.Corona RG Pressure Pressure.Tube Tree Wilson
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Merge
open ActualWilsonPacketSwitch WilsonForcedReplicaBoundary
open scoped Classical BigOperators
variable {c : Side} {ι : Type*} (K : ι→Support c)

private theorem absorb (T : Support c) (s : Finset ι) (i : ι) (hi:i∈s) (hit:¬Disjoint T (K i)) :
    region K T s=region K (T∪K i) (s.erase i) := by
  let B:=region K (T∪K i) (s.erase i)
  have paid : T∪K i⊆B:=root_subset K (T∪K i) (s.erase i)
  have home:=root_subset K T s
  apply Subset.antisymm
  · apply least K T s B (Finset.subset_union_left.trans paid)
    intro j hj meet
    by_cases eq:j=i
    · subst j;exact Finset.subset_union_right.trans paid
    exact closed K (T∪K i) (s.erase i) (mem_erase.mpr ⟨eq,hj⟩) meet
  apply least K (T∪K i) (s.erase i) (region K T s)
  · refine union_subset home (closed K T s hi ?_)
    obtain ⟨z,ht,hk⟩:=not_disjoint_iff.mp hit
    exact not_disjoint_iff.mpr ⟨z,hk,home ht⟩
  intro j hj
  exact closed K T s (mem_of_mem_erase hj)

/-- Each original occupied support is charged at most once, even for a cyclic overlap graph. -/
theorem cover (B : ℕ) (T : Support c) (s : Finset ι) :
    coverNumber B (region K T s)≤coverNumber B T+∑i∈s,coverNumber B (K i) := by
  classical
  induction s using Finset.strongInductionOn generalizing T with
  | _ s ih =>
    by_cases seen:∃i∈s,¬Disjoint T (K i)
    · obtain ⟨i,hi,hit⟩:=seen
      obtain ⟨z,hT,hK⟩:=not_disjoint_iff.mp hit
      have rest:=ih (s.erase i) (erase_ssubset hi) (T∪K i)
      have join:=Corona.meets_sum hT hK B
      have total:=Finset.sum_erase_add s (fun j=>coverNumber B (K j)) hi
      rw [absorb K T s i hi hit]
      omega
    have fix:region K T s=T:=Subset.antisymm
      (least K T s T Subset.rfl (fun j hj h=>(seen ⟨j,hj,(fun opposed=>h opposed.symm)⟩).elim)) (root_subset K T s)
    rw [fix]
    omega

private theorem singleton (B : ℕ) (x : Site c) : coverNumber B ({x}:Support c)≤1 := calc
  _ ≤ ({x}:Support c).card := Corona.list_cost B ⟨halo_subset B {x},
    Corona.ship_halo _ (fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
  _ = 1 := card_singleton x

/-- The two-cover distance debit uses the original regulator block size and separation. -/
theorem joined (B : ℕ) (x y : Site c) (a b : Finset ι) (hit:y∈region K {x} (a∪b)) :
    separation x y / Push.GridApprox.Attach.leg B ≤
      1+(∑i∈a,coverNumber B (K i))+(∑i∈b,coverNumber B (K i)) := by
  let t:=fun i=>coverNumber B (K i)
  have inX:=root_subset K {x} (a∪b) (mem_singleton_self x)
  have gap:=Push.GridApprox.Attach.distance_charge (region K {x} (a∪b)) B x y inX hit
  have bounded:=cover K B {x} (a∪b)
  have weight:(∑i∈a∪b,t i)+(∑i∈a∩b,t i)=(∑i∈a,t i)+(∑i∈b,t i):=Finset.sum_union_inter
  have base:=singleton B x
  dsimp only [t] at weight
  omega

variable {G : Gauge} {f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {R : Rep G f} {W α μ reserve : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
  (H : Cash W α μ L Q o reserve T R) (U : Config G c) {I : Type} [Fintype I]
  (M : I→Leaf R) (χ : Push.SectorMeasure.Chi) (fee : I→ℝ) (t : ℝ)

/-- No genuine signed term is changed by imposing the quantitative two-root physical cost. -/
theorem original (B : ℕ) (a b : I) (hne:a≠b) (x y : Site c)
    (hx:x∈(M a).crest.image S.ratio.parent) (hy:y∈(M b).crest.image S.ratio.parent)
    (p : Finset I) (ha:a∉p) (hb:b∉p) (q : Finset H.Chainbook×Finset H.Chainbook)
    (active : WilsonForcedReplicaBoundary.difference H U M χ fee t a b x p q≠0) :
    separation x y / Push.GridApprox.Attach.leg B ≤
      1+(∑i∈q.1,coverNumber B (H.library i))+(∑i∈q.2,coverNumber B (H.library i)) := by
  apply joined H.library B x y
  by_contra missing
  exact active (WilsonForcedReplicaBoundary.disconnected H U M χ fee t a b hne x y hx hy p ha hb q missing)
end YM.Integration.WilsonForcedReplicaDistance
end
