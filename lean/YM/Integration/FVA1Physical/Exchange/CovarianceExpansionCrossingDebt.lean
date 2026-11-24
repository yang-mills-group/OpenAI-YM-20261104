import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFiledNetworkBill
import YM.Comparison.RG02.Cumulants.Parents

/-! A signed cut before any division by the cut vacuum. Scalar crossing
actors remain charged. The two separated true singleton means and their
cross terms stay on the same field and the same positive original vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Set Lattice RG Wilson Marker Multi Extra.Trajectories Comparison.RG02.Cumulants
  Primitives.GCC.Anchor QuadraticLocal
open scoped Classical BigOperators
open private region_absent from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterConnected
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

abbrev cross (B:Activities G n)(L:Support n)(i:ℕ):Prop:=
  ¬lies B L i ∧ ¬Disjoint (B.forced i).support L

def retained (B:Activities G n)(L:Support n)(K:ℕ→Poly C)(i:ℕ):Poly C:=
  if cross B L i then 0 else K i

def crossedCash (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(L:Support n):Poly C:=
  ∑' S:Finset ℕ, ({Q:Finset ℕ|∃i∈Q,cross B L i}:Set (Finset ℕ)).indicator (RoseRoster.roster B p U K) S

abbrev remainingCash (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(L:Support n):Poly C:=
  ∑' S:Finset ℕ, RoseRoster.roster B p U (retained B L K) S

omit [Fintype V] in
private theorem retained_stock (B:Activities G n)(L:Support n)(K:ℕ→Poly C)(w:V→ℝ)
    (wp:∀v,0<w v)(fund:Summable fun i=>Poly.price w (K i)):
    Summable fun i=>Poly.price w (retained B L K i):=by
  apply fund.of_nonneg_of_le (fun _=>Poly.nonnegative wp _)
  intro i
  by_cases crosses:cross B L i
  · rw [retained,if_pos crosses,Poly.zero_price];exact Poly.nonnegative wp _
  rw [retained,if_neg crosses]

omit [Fintype V] in
theorem crossing_cash_exact (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(L:Support n)
    (w:V→ℝ)(wp:∀v,0<w v)(fund:Summable fun i=>Poly.price w (K i)):
    (∑'S,RoseRoster.roster B p U K S)=remainingCash B p U K L+crossedCash B p U K L:=by
  let raw:=RoseRoster.roster B p U K
  let kept:=RoseRoster.roster B p U (retained B L K)
  let hit:Set (Finset ℕ):={S|∃i∈S,cross B L i}
  have total:=physical_series B p U K w wp fund
  have sub:=physical_series B p U _ w wp (retained_stock B L K w wp fund)
  have other:Summable (hit.indicator raw):=total.indicator _
  change (∑'S,raw S)=(∑'S,kept S)+∑'S,hit.indicator raw S
  rw [←sub.tsum_add other]
  apply tsum_congr
  intro S
  change raw S=kept S+hit.indicator raw S
  by_cases met:S∈hit
  · obtain ⟨i,used,between⟩:=met
    have zero:∏k∈S,retained B L K k=0:=
      prod_eq_zero used (by rw [retained,if_pos between])
    have vanished:kept S=0:=by simp only [kept,RoseRoster.roster,zero,ite_self]
    rw [vanished,zero_add,Set.indicator_of_mem (show S∈hit from ⟨i,used,between⟩)]
  rw [Set.indicator_of_notMem met,add_zero]
  dsimp only [raw,kept,RoseRoster.roster]
  split
  · apply prod_congr rfl
    intro i hi
    rw [retained,if_neg (fun h=>met ⟨i,hi,h⟩)]
  rfl

/-- Each unnormalized row of the retained physical roster is the exact product
of the two respective regional rows, even when either regional mass is zero. -/
theorem retained_reads (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)(L:Support n)
    (o:V→Site n)(carry:∀(i:ℕ)(s:C.Mode),(K i).part s≠0 → ∀v∈s.val,o v∈(B.forced i).support)
    (w:V→ℝ)(wp:∀v,0<w v)(fund:Summable fun i=>Poly.price w (K i)):
    let O:=univ.filter (fun v=>o v∈L)
    ∃l r:Poly C,∀s:C.Mode,(remainingCash B p U K L).part s=l.part (inside s O)*r.part (diff s O):=by
  intro O
  let S:=retained B L K
  have stock:=retained_stock B L K w wp fund
  have inactive (i:ℕ)(nz:S i≠0)(out:¬lies B L i):Disjoint (B.forced i).support L:=by
    by_contra met
    exact nz (if_pos ⟨out,met⟩)
  have carries (i:ℕ)(s:C.Mode)(h:(S i).part s≠0):∀v∈s.val,o v∈(B.forced i).support:=by
    by_cases away:cross B L i
    · exact False.elim (h (by simp only [S,retained,if_pos away];rfl))
    exact carry i s (by simpa only [S,retained,if_neg away] using h)
  let l:=∑'z:Pool (lies B L),component B (flags p.threshold U∩L) S z.val
  let r:=∑'z:Pool (fun i=>¬lies B L i),component B (flags p.threshold U\L) S z.val
  have ls:l=withinSet O l:=by
    ext s
    rw [begin_inner_part]
    split
    · rfl
    next miss =>
      obtain ⟨v,seen,no⟩:=Finset.not_subset.mp miss
      apply region_absent B _ S _ w wp stock v _ s seen
      intro i isin f used
      by_contra nz
      exact no (mem_filter.mpr ⟨mem_univ _,isin (carries i f nz v used)⟩)
  have rs:r=without O r:=by
    ext s
    rw [begin_outer_part]
    split
    · rfl
    next miss =>
      obtain ⟨v,seen,located⟩:=not_disjoint_iff.mp miss
      apply region_absent B _ S _ w wp stock v _ s seen
      intro i outside f used
      by_contra nz
      have active:S i≠0:=by rintro h;exact nz (by rw [h];rfl)
      exact disjoint_left.mp (inactive i active outside) (carries i f nz v used) (mem_filter.mp located).2
  refine ⟨l,r,fun s=>?_⟩
  have exactLeft:remainingCash B p U K L=l*r:=original_full_cut B p U S L inactive w wp stock
  rw [exactLeft]
  calc (l*r).part s=(withinSet O l*without O r).part s:=congrArg (fun A:Poly C=>A.part s) (congrArg₂ (·*·) ls rs)
       _=l.part (inside s O)*r.part (diff s O):=part_split O l r s

end YM.Integration.FVA1Physical.Exchange.RoseCut
