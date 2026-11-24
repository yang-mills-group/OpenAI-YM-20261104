import YM.Integration.WilsonCenteredFiledAtoms

/-! A native paid gallery may have an arbitrary address type. Its genuine
active roster before every test is countable with the same rooted wage. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredPaidPublisher
open Finset Function RG Lattice Wilson Marker QuadraticLocal Ac
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {p : BudgetPoint} (L : Lamps X ι G p o R)

def keep (A : Set ι) : Lamps X A G p o R where
  mode i:=L.mode i.val
  live i:=L.live i.val
  address i:=L.address i.val
  roots i:=L.roots i.val
  nominal x i:=L.nominal x i.val
  legal x i:=L.legal x i.val
  clear i:=L.clear i.val
  pure x i:=L.pure x i.val

theorem original (w : V→ℝ) (hw : ∀ i,0<w i) {α C : ℝ} (width : 0≤α) (bought : L.Paid w p.B α C) :
    ∃ A : Set ι,A.Countable ∧ (keep L A).Paid w p.B α C ∧
      ∀ x U,(keep L A).log x U=L.log x U := by
  obtain ⟨e,positive,cap,spent⟩:=bought.budget
  let tab (y : Site n) (i : ι):=if y∈L.ground i then
    Poly.toll w (L.mode i)*e i*Real.exp (α*coverNumber p.B (L.ground i)) else 0
  have counted (y) : (Function.support (tab y)).Countable := (spent y).2.1.countable_support
  let A:=Function.support e
  have count : A.Countable := (Set.countable_iUnion counted).mono (by
    intro i live
    refine Set.mem_iUnion.mpr ⟨(L.address i).site,?_⟩
    change tab _ i≠0
    change (if (L.address i).site∈L.ground i then Poly.toll w (L.mode i)*e i*Real.exp (α*coverNumber p.B (L.ground i)) else 0)≠0
    have here : (L.address i).site∈L.ground i := (L.address i).anchor
    rw [if_pos here]
    exact mul_ne_zero (mul_ne_zero (Poly.worth hw _).ne' live) (Real.exp_pos _).ne')
  refine ⟨A,count,?_,?_⟩
  · refine ⟨fun i=>e i.val,fun i=>positive _,fun i=>cap i.val,fun y=>?_⟩
    let b : SumBudget (tab y) C:=spent y
    exact ⟨fun i=>b.1 i.val,b.2.1.comp_injective Subtype.val_injective,
      (tsum_comp_le_tsum_of_inj b.2.1 b.1 (Subtype.val_injective (p:=(·∈A)))).trans b.2.2⟩
  intro x U
  have missed (i : ι) (out : i∉Set.range (Subtype.val : A→ι)) : L.frame i x U=0 := by
    have ez : e i=0 := by by_contra live;exact out ⟨⟨i,live⟩,rfl⟩
    have sized := L.light_size i x U (cap i x _ (L.address i).anchor)
    have zero : L.light x i U=0 := norm_eq_zero.mp (le_antisymm (ez ▸ sized) (norm_nonneg _))
    simp [Lamps.frame,zero]
  have total:=bought.sums width hw x U
  exact (((Subtype.val_injective (p:=(·∈A))).hasSum_iff missed).2 total.hasSum).tsum_eq

end YM.Integration.WilsonCenteredPaidPublisher
