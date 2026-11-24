import YM.Integration.WilsonOriginalAlternativeLamps

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeMenu
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open scoped Classical BigOperators
variable {V W T I:Type} [DecidableEq V] [Fintype W] [Fintype I]
variable {J:Census V} {G:Gauge} {n:Side} {o:V→Site n} {p:BudgetPoint}
variable (L:W→Lamps T I G p o J)

def pool : Lamps T (W×I) G p o J where
  mode q:=(L q.1).mode q.2
  live q:=(L q.1).live q.2
  address q:=(L q.1).address q.2
  roots q:=(L q.1).roots q.2
  nominal t q:=(L q.1).nominal t q.2
  legal t q:=(L q.1).legal t q.2
  clear q:=(L q.1).clear q.2
  pure t q:=(L q.1).pure t q.2

theorem original (t:T) (U:Config G n) : (pool L).log t U=∑v:W,(L v).log t U := by
  simp only [Lamps.log,tsum_fintype,Fintype.sum_prod_type]
  rfl

theorem price {w:V→ℝ} {b:ℕ} {a:ℝ} {c:W→ℝ}
    (quota:∀v,(L v).Paid w b a (c v)) : (pool L).Paid w b a (∑v,c v) := by
  choose f nonneg smooth hit using fun v=>(quota v).budget
  refine ⟨fun j=>f j.1 j.2,fun j=>nonneg _ _,fun j=>smooth _ _,?_⟩
  intro u
  apply budget_finite
  · intro q;exact (hit q.1 u).1 q.2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum (fun v _=>(tsum_fintype ..).symm.trans_le (hit v u).2.2)

theorem mono (v:V) (F:Lamps T I G p o J) (own:∀i,F.mode i=J.fire v)
    (t:T) (U:Config G n) : F.log t U=Poly.send (J.fire v) ((F.log t U).part (J.fire v)) := by
  ext s
  by_cases e:s=J.fire v
  · simp [e]
  rw [Poly.part_send,if_neg e,Lamps.log,Poly.share Summable.of_finite]
  simp only [Lamps.frame,Poly.part_send,own,if_neg e,tsum_zero]

end YM.Integration.WilsonOriginalAlternativeMenu
