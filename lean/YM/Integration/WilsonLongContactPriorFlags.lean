/- For a related powerset-of-the-union estimate, compare finite with
`summable_finsetProd_of_summable_nonneg`.
Upstream source: Mathlib/Analysis/SpecialFunctions/Log/Summable.lean
Authors: Chris Birkbeck. Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.WilsonLongContactPriorBank

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorFlags
open Lattice Wilson RG Marker Finset Merge MeasureTheory
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V}
  (A:Activities G n) (P:BudgetPoint) (w:V→ℝ) (f:ℕ→Poly Γ)

private theorem eligible (U:Config G n) (Z:Support n) (hZ:flags P.threshold U⊆Z)
    (s:Finset ℕ) (live:A.admissible P U s) (i:ℕ) (hi:i∈s):
    Ac.meets (fun a=>(A.forced a).support) i Z:=by
  obtain ⟨x,hx⟩:=(A.forced i).inventory_ne
  exact ⟨x,hZ (live.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hx⟩),(A.forced i).inventory_sup hx⟩

/-- The complete nonempty part of the physically admissible forced gas, at a fixed field. -/
theorem finite (hw:∀v,0<w v) (U:Config G n) (Z:Support n)
    (hZ:flags P.threshold U⊆Z) (cost:ℝ)
    (income:∀B:Finset ℕ,∑i∈Ac.buds (fun a=>(A.forced a).support) B Z,Poly.price w (f i)≤cost)
    (range:Finset (Finset ℕ)):
    ∑s∈range, (if s.Nonempty then Poly.price w (Photo.fronts A f U P s) else 0) ≤ Real.exp cost-1:=by
  classical
  let B:=Ac.buds (fun a=>(A.forced a).support) (range.biUnion id) Z
  let good:=range.filter fun s=>s.Nonempty ∧ A.admissible P U s
  let M (s:Finset ℕ):=∏i∈s,Poly.price w (f i)
  have hn (s:Finset ℕ):0≤M s:=Finset.prod_nonneg (fun i _=>Poly.nonnegative hw (f i))
  have cover:good⊆B.powerset.erase ∅:=by
    intro s hs
    obtain ⟨inside,live,adm⟩:=Finset.mem_filter.mp hs
    refine Finset.mem_erase.mpr ⟨live.ne_empty,Finset.mem_powerset.mpr fun i hi=>?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨s,inside,hi⟩,eligible A P U Z hZ s adm i hi⟩
  have first:(∑s∈range,if s.Nonempty then Poly.price w (Photo.fronts A f U P s) else 0)≤∑s∈good,M s:=by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro s _
    by_cases live:s.Nonempty
    · by_cases adm:A.admissible P U s
      · simpa only [live,adm,and_self,if_true,Photo.fronts,M] using Poly.multiple hw s f
      simp only [live,adm,and_false,if_false,if_true,Photo.fronts,Poly.zero_price,le_refl]
    simp [live]
  have second:(∑s∈good,M s)≤∑s∈B.powerset.erase ∅,M s :=
    Finset.sum_le_sum_of_subset_of_nonneg cover (fun s _ _=>hn s)
  have full:(∑s∈B.powerset,M s)≤Real.exp cost:=by
    rw [show (∑s∈B.powerset,M s)=∏i∈B,(1+Poly.price w (f i)) from (Finset.prod_one_add B).symm]
    calc _ ≤ ∏i∈B, Real.exp (Poly.price w (f i)) :=
           Finset.prod_le_prod (fun i _=>add_nonneg zero_le_one (Poly.nonnegative hw _))
             (fun i _=>by simpa [add_comm] using Real.add_one_le_exp (Poly.price w (f i)))
         _ = Real.exp (∑i∈B,Poly.price w (f i)) := (Real.exp_sum ..).symm
         _ ≤ _ := Real.exp_monotone (income (range.biUnion id))
  have empty: (∅:Finset ℕ)∈B.powerset:=Finset.mem_powerset.mpr (Finset.empty_subset _)
  have h:=Finset.sum_erase_add B.powerset M empty
  have one:M ∅=1:=Finset.prod_empty
  rw [one] at h
  linarith [first,second,full,h]

theorem original (hw:∀v,0<w v) (U:Config G n) (Z:Support n)
    (hZ:flags P.threshold U⊆Z) (cost:ℝ)
    (income:∀B:Finset ℕ,∑i∈Ac.buds (fun a=>(A.forced a).support) B Z,Poly.price w (f i)≤cost):
    Summable (fun s:Finset ℕ=>if s.Nonempty then Poly.price w (Photo.fronts A f U P s) else 0) ∧
    (∑'s:Finset ℕ,if s.Nonempty then Poly.price w (Photo.fronts A f U P s) else 0)≤Real.exp cost-1:=by
  let a (s:Finset ℕ):=if s.Nonempty then Poly.price w (Photo.fronts A f U P s) else 0
  have hn (s:Finset ℕ):0≤a s:=by unfold a; split; exact Poly.nonnegative hw _; exact le_rfl
  have h:=finite A P w f hw U Z hZ cost income
  have sum:Summable a:=summable_of_sum_le hn h
  exact ⟨sum,sum.tsum_le_of_sum_le h⟩

end YM.Integration.WilsonLongContactPriorFlags
