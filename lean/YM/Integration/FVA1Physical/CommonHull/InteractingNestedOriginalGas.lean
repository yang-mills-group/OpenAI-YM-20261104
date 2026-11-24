import YM.Integration.FVA1Physical.CommonHull.InteractingFiledCrossedTerritory

/-! A possibly tiny outer vacuum cancels exactly from the full crossed
reading on any face whose marked sites lie in the active component. The
regional numerator and denominator both retain every physical flag and
signed activity in that component. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Lattice RG Wilson Marker Multi Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02.Cumulants
open QuadraticLocal QuadraticLocal.Fusion.Attached Exchange Exchange.RoseCut
open private region_absent from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterConnected
open private retained_stock from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDebt
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

abbrev insidePacket (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(T:Support n):Poly C:=
  ∑'S:Pool (lies B T),component B (flags p.threshold U∩T) K S.val
abbrev outsidePacket (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(T:Support n):Poly C:=
  ∑'S:Pool (fun i=>¬lies B T i),component B (flags p.threshold U\T) K S.val

def activeTerritory (B:Activities G n)(K:ℕ→Poly C)(x:Site n):Support n:=
  univ.filter (fun y=>Relation.ReflTransGen (Edge B K) x y)

omit [Fintype V] in
private theorem original_component_cut (B:Activities G n)(K:ℕ→Poly C)(x:Site n):
    ∀i,K i≠0 → ¬lies B (activeTerritory B K x) i → Disjoint (B.forced i).support (activeTerritory B K x):=by
  intro i active outside
  refine disjoint_left.mpr fun z member reached=>outside fun y inside=>?_
  exact mem_filter.mpr ⟨mem_univ _,Relation.ReflTransGen.tail (mem_filter.mp reached).2 ⟨i,active,member,inside⟩⟩

omit [Fintype V] in
theorem short_inside_original (B:Activities G n)(p:BudgetPoint)(K:ℕ→Poly C)(x:Site n)(D:ℕ):
    shortTerritory B p K x D⊆activeTerritory B K x:=by
  intro z seen
  have chain:Relation.ReflTransGen (Edge B (shortActors B p K D)) x z:=(mem_filter.mp seen).2
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  clear seen
  induction chain with
  | refl=>exact Relation.ReflTransGen.refl
  | tail prior final ih=>
    obtain ⟨i,h,here,there⟩:=final
    have live:K i≠0:=fun dead=>h (by simp only [shortActors,dead,ite_self])
    exact ih.tail ⟨i,live,here,there⟩

private theorem cut_read (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(T:Support n)
    (cut:∀i,K i≠0 → ¬lies B T i → Disjoint (B.forced i).support T)
    (o:V→Site n)(carry:∀(i:ℕ)(r:C.Mode),(K i).part r≠0 → ∀v∈r.val,o v∈(B.forced i).support)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))(s:C.Mode)
    (insideSources:∀v∈s.val,o v∈T):
    (∑'S,RoseRoster.roster B p U K S).part s=(insidePacket B p U K T).part s*(outsidePacket B p U K T).part C.quiet:=by
  let O:=univ.filter (fun v=>o v∈T)
  let l:=insidePacket B p U K T
  let r:=outsidePacket B p U K T
  have left:l=withinSet O l:=by
    ext z;rw [begin_inner_part];split
    · rfl
    next miss=>
      obtain ⟨v,belongs,gone⟩:=Finset.not_subset.mp miss
      apply region_absent B _ K _ w wp stock v _ z belongs
      intro i owner b marked;by_contra active
      exact gone (mem_filter.mpr ⟨mem_univ _,owner (carry i b active v marked)⟩)
  have right:r=without O r:=by
    ext z;rw [begin_outer_part];split
    · rfl
    next miss=>
      obtain ⟨v,belongs,yes⟩:=not_disjoint_iff.mp miss
      apply region_absent B _ K _ w wp stock v _ z belongs
      intro i outside b marked;by_contra active
      have live:K i≠0:=fun dead=>active (by rw [dead];rfl)
      exact disjoint_left.mp (cut i live outside) (carry i b active v marked) (mem_filter.mp yes).2
  have all:s.val⊆O:=fun v hv=>mem_filter.mpr ⟨mem_univ _,insideSources v hv⟩
  have inner:inside s O=s:=Subtype.ext (inter_eq_left.mpr all)
  have away:diff s O=C.quiet:=Subtype.ext (sdiff_eq_empty_iff_subset.mpr all)
  have fact:(∑'S,RoseRoster.roster B p U K S)=l*r:=original_full_cut B p U K T cut w wp stock
  rw [fact];change (l*r).part s=l.part s*r.part C.quiet
  calc _=(withinSet O l*without O r).part s:=congrArg (fun a:Poly C=>a.part s) (congrArg₂ (·*·) left right)
       _=l.part s*r.part C.quiet:=by rw [part_split,inner,away]

/-- All signed exterior components, scalar or marked, are retained until one
identical scalar factor cancels. The exterior vacuum can be arbitrarily small.
Only the actual interior component's nonzero mass survives in the quotient. -/
theorem original_nested_cross {T I:Type}{o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)(t:T)
    (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)(paid:A.K.Paid w P.p.B e κ)(en:0≤e)(U:Config G n)
    (vac:P.activities.gas P.p U≠0)(x:Site n)(D:ℕ)(s:C.Mode)
    (within:∀v∈s.val,o v∈activeTerritory P.activities (fun i=>A.K.hard t i U) x):
    let K:=fun i=>A.K.hard t i U
    let F:=activeTerritory P.activities K x
    let L:=cutTerritory A t D x U
    let region:=insidePacket P.activities P.p U K F
    let kept:=insidePacket P.activities P.p U (retained P.activities L K) F
    region.part C.quiet≠0 ∧
      (actualCrossing A t D x U).part s/(P.activities.gas P.p U:ℂ)=
        (region.part s-kept.part s)/region.part C.quiet:=by
  intro K F L region kept
  let B:=P.activities
  let ext:=outsidePacket B P.p U K F
  let keptK:=retained B L K
  have inc:L⊆F:=short_inside_original B P.p K x D
  have cut:=original_component_cut B K x
  have cutoff(i)(h:keptK i≠0)(out:¬lies B F i):Disjoint (B.forced i).support F:=by
    apply cut i _ out;intro dead;exact h (by simp only [keptK,retained,dead,ite_self])
  have external(i)(out:¬lies B F i):keptK i=K i:=by
    by_cases live:K i=0
    · simp only [keptK,retained,live,ite_self]
    exact if_neg (fun crosses=>crosses.2 ((cut i live out).mono_right inc))
  have fixed:outsidePacket B P.p U keptK F=ext:=by
    apply tsum_congr;intro S;unfold component;split
    · exact prod_congr rfl (fun i hi=>external i (S.property i hi))
    rfl
  have carry(i)(q:C.Mode)(nz:(keptK i).part q≠0):∀v∈q.val,o v∈(B.forced i).support:=by
    by_cases cross:RoseCut.cross B L i
    · exact (nz (by simp only [keptK,retained,if_pos cross];rfl)).elim
    exact (A.K.locality t i).carry U q (by simpa only [keptK,retained,if_neg cross] using nz)
  have stock:=filed_actor_stock A wp paid en t U
  have direct (u:C.Mode)(sel:∀v∈u.val,o v∈F):
      (A.gas t U).part u=region.part u*ext.part C.quiet:=
    cut_read B P.p U K F cut o (fun i r=>(A.K.locality t i).carry _ r) w wp stock u sel
  have quiet:region.part C.quiet*ext.part C.quiet=(P.activities.gas P.p U:ℂ):=by
    rw [←direct C.quiet (fun j hj=>(Finset.notMem_empty j hj).elim)];exact Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t _)
  have good:region.part C.quiet*ext.part C.quiet≠0:=quiet ▸ Complex.ofReal_ne_zero.mpr vac
  have sold:(remainingCash B P.p U K L).part s=kept.part s*ext.part C.quiet:=by
    have h:=cut_read B P.p U keptK F cutoff o carry w wp (retained_stock B L K w wp stock) s within
    rwa [fixed] at h
  have sum:(A.gas t U).part s=(remainingCash B P.p U K L).part s+(actualCrossing A t D x U).part s:=
    congrArg (fun a:Poly C=>a.part s) (crossing_cash_exact B P.p U K L w wp stock)
  have eq:(actualCrossing A t D x U).part s=(region.part s-kept.part s)*ext.part C.quiet:=by
    rw [direct s within,sold] at sum;linear_combination -sum
  refine ⟨left_ne_zero_of_mul good,?_⟩
  rw [eq,←quiet];field_simp [left_ne_zero_of_mul good,right_ne_zero_of_mul good]

end YM.Integration.FVA1Physical.Marked.RemoteRoster
