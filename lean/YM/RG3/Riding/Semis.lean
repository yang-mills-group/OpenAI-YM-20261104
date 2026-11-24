import YM.RG3.Riding.Holt
 import YM.RG3.Script.Gates

/-! # Quote compressed receipts with stronger profile on virtual Rep

Host K.e previously supplied at arbitrary stages on torus representations
or through Caption demands. Keep common across passive tests; applies on output
from Π where `t` Coffer pinned_poles etc but DOESN'T infer changing-stage
strong bounds until h.Kernel.G.§. True layout supplies always x,P.
This variant price Φ(x,i) indexed by *one* Ω previously known to Reserve.reg.
 Can pass common receipts by simultaneous construction termwise thru same
`plaster`,`costMask` etc. `Offer.Arbors` might supply a t.Broadcast only
Ω-by-Ω; see annotations on needing re-union receipts again.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Riding
open RG Wilson Lattice Function Marker Overlay RG3.Script RG3.Held
 RG3.Forms RG3.Ink Extra.Trajectories Extra.Iteration Extra.Multi Ac Push.Local Press
 Push.AbsoluteSums Push.Corrected MergeProof Accent Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side}{V:Type*}[DecidableEq V]{R:Census V}{G:Gauge}
  (P : Rep G n){p:BudgetPoint}{ζ:V→Site n}{w:V→ℝ}
section Economies
lemma covered {G:Box n→ Config G n→Poly R}{v:ℝ}{S:ℝ}
    (h : Towed w Prod.fst G P.p.B S v)(hw:∀i,0<w i):
    ∃ f : Box n→R.Mode→ℝ,
    (∀ i s,0≤ f i s) ∧
    (∀ i U s, ‖(G i U).part s‖ ≤ f i s) ∧
    Hit Prod.fst P.p.B (fun (i:Box n)=>∑ s:R.Mode, Poly.toll w s*f i s) S v:=by
  obtain ⟨a,-,ha,hA⟩:=h; choose q hq hh hp using hA
  have ht i s :0 ≤ q i s := hq _ _
  refine ⟨q,ht,hh,fun t=> budget_mono (ha t) (fun i=>?_ ) (fun i=>?_ )⟩
  · split; exact mul_nonneg (sum_nonneg (fun i _=>mul_nonneg (Poly.worth hw _).le (ht _ _))) (Real.exp_pos _).le; rfl
  split; exact mul_le_mul_of_nonneg_right (hp _) (Real.exp_pos _).le; rfl
-- Slate from only Towed; Loci & target on grouped box.
lemma masonry {S v : ℝ} {f : Box n→ Config G n→Poly R}
    (h : Towed w Prod.fst f P.p.B S v)(hw:∀i,0<w i)(hx:∀ i U,(f i U).part R.quiet=bass P i U) : ∃ a, Slate P S v a := by
  obtain ⟨t,ht,hq,hY⟩:= covered P h hw
  let a (i : mortar n):= t i.val R.quiet
  refine ⟨a,fun i=> ht _ _,fun i U=>?_ ,fun i=>?_ ⟩
  · rw [← hx]; exact hq ..
  let f (j:Box n):=if i∈ j.1 then (∑ s:R.Mode,Poly.toll w s*t j s)*Real.exp (S*coverNumber P.p.B j.1) else 0
  have hh : SumBudget (fun j:mortar n=> f j.val) v:= Script.Edition.minor_subtype {i|Sure i} (hY i)
  have htS (I:Box n) : t I R.quiet ≤ ∑ s:R.Mode, Poly.toll w s*t I s:=by
    calc
      _ = Poly.toll w R.quiet*t I R.quiet:=by rw [Poly.quiet_toll,one_mul]
      _ ≤ _:= single_le_sum (f:=fun s:R.Mode=> Poly.toll w s*t I s) (fun s _=>mul_nonneg (Poly.worth hw _).le (ht _ _)) (mem_univ _)
  refine budget_mono hh (fun j=>?_ ) (fun j=>?_)
  · split; exact mul_nonneg (ht _ _) (Real.exp_pos _).le; rfl
  unfold f; split; exact mul_le_mul_of_nonneg_right (htS _) (Real.exp_pos _).le; rfl
end Economies
end YM.RG3.Riding
