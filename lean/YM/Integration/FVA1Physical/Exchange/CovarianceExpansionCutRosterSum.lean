import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCutRosterFrame
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionActualRoster
import YM.Marker.Truncated
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Factor the marked physical roster series on a fixed cutoff field, without
discarding a single compulsory vacuum flag or replacing its denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker Multi
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{C:Census V}

abbrev lies (B:Activities G n)(D:Support n)(i:ℕ):Prop:=(B.forced i).support⊆D
abbrev component (B:Activities G n)(E:Support n)(K:ℕ→Poly C)(S:Finset ℕ):Poly C:=
  if Regional B E S then ∏i∈S,K i else 0

omit [Fintype V] in
theorem true_cut_roster (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (D:Support n)(nocross:∀i,K i≠0 → ¬lies B D i → Disjoint (B.forced i).support D)
    (L:Pool (lies B D))(R:Pool (fun i=>¬lies B D i)):
    RoseRoster.roster B p U K (combine (lies B D) (L,R))=
      component B (flags p.threshold U∩D) K L.val *
      component B (flags p.threshold U\D) K R.val:=by
  change RoseRoster.roster _ _ _ _ (L.val∪R.val)=_
  by_cases live:∀i∈R.val,K i≠0
  · have legal:=true_cut_admission B p U D L.val R.val L.property
        (fun i hi=>nocross i (live i hi) (R.property i hi))
    rw [RoseRoster.roster,legal,prod_union (pools_disjoint _ L R)]
    by_cases a:Regional B (flags p.threshold U∩D) L.val <;>
      by_cases b:Regional B (flags p.threshold U\D) R.val <;> simp [component,a,b]
  push Not at live
  obtain ⟨i,ir,dead⟩:=live
  have kill:∏j∈R.val,K j=0:=prod_eq_zero ir dead
  have gone:∏j∈L.val∪R.val,K j=0:=prod_eq_zero (mem_union_right _ ir) dead
  simp [RoseRoster.roster,component,gone,kill]

omit [Fintype V] in
private theorem bills (K:ℕ→Poly C)(w:V→ℝ)(wp:∀v,0<w v)
    (stock:Summable (fun i=>Poly.price w (K i))):
    Summable (fun S:Finset ℕ=>∏i∈S,Poly.price w (K i)) :=
  summable_finsetProd_of_summable_nonneg (fun i=>Poly.nonnegative wp (K i)) stock

omit [Fintype V] in
theorem regional_series (B:Activities G n)(E:Support n)(K:ℕ→Poly C)(w:V→ℝ)
    (wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i))(c:ℕ→Prop):
    Summable (fun L:Pool c=>component B E K L.val):=by
  have all:Summable (fun S:Finset ℕ=>∏i∈S,Poly.price w (K i)):=bills K w wp stock
  have sub := all.comp_injective (Subtype.val_injective (p:=fun L:Finset ℕ=>∀i∈L,c i))
  refine (Poly.budgeted wp sub (fun L=>?_)).1
  change Poly.price w (component B E K L.val)≤∏i∈L.val,Poly.price w (K i)
  unfold component
  split
  · exact Poly.multiple wp _ _
  rw [Poly.zero_price]
  exact prod_nonneg fun i _=>Poly.nonnegative wp (K i)

omit [Fintype V] in
theorem physical_series (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i)):
    Summable (RoseRoster.roster B p U K):=by
  refine (Poly.budgeted wp (bills K w wp stock) (fun S=>?_)).1
  unfold RoseRoster.roster
  split
  · exact Poly.multiple wp _ _
  rw [Poly.zero_price]
  exact prod_nonneg fun i _=>Poly.nonnegative wp (K i)

omit [Fintype V] in
/-- The actual double sum of the original actor tables factors on a physical
cut. Nonzero actors must lie wholly on one side; zero crossing tables may be
present. In particular unmarked actors capable of joining the two sides count. -/
theorem original_full_cut (B:Activities G n)(p:BudgetPoint)(U:Config G n)(K:ℕ→Poly C)
    (D:Support n)(nocross:∀i,K i≠0 → ¬lies B D i → Disjoint (B.forced i).support D)
    (w:V→ℝ)(wp:∀v,0<w v)(stock:Summable fun i=>Poly.price w (K i)):
    (∑'S,RoseRoster.roster B p U K S)=
      (∑'L:Pool (lies B D),component B (flags p.threshold U∩D) K L.val)*
      (∑'R:Pool (fun i=>¬lies B D i),component B (flags p.threshold U\D) K R.val):=by
  letI : IsTopologicalSemiring (Poly C) := {}
  let A:=Pool (lies B D)
  let H:=Pool (fun i=>¬lies B D i)
  let l:=fun L:A=>component B (flags p.threshold U∩D) K L.val
  let r:=fun R:H=>component B (flags p.threshold U\D) K R.val
  let χ:=combine (lies B D)
  have sl:Summable l:=regional_series _ _ _ _ wp stock _
  have sr:Summable r:=regional_series _ _ _ _ wp stock _
  have all:=physical_series B p U K w wp stock
  have raw:Summable (fun z:A×H=>RoseRoster.roster B p U K (χ z)):=χ.summable_iff.mpr all
  have term (z:A×H):RoseRoster.roster B p U K (χ z)=l z.1*r z.2:=
    true_cut_roster B p U K D nocross z.1 z.2
  have prod:Summable (fun z:A×H=>l z.1*r z.2):=raw.congr term
  exact (χ.tsum_eq _).symm.trans ((tsum_congr term).trans (sl.tsum_mul_tsum sr prod).symm)

end YM.Integration.FVA1Physical.Exchange.RoseCut
