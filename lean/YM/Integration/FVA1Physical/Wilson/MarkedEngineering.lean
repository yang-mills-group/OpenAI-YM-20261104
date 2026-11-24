import YM.Integration.FVA1Physical.Wilson.FiniteMarkDegrees
import YM.Integration.FVA1Physical.Wilson.WickCubeLaw

/-! A nonempty physical connected source saves one unit of valence. Its
independent Wilson emission and measured reset therefore have exactly the
field degree allowed by the incoming engineering grade at every order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Precision Exterior Tree Comparison.RG02 Valence Adjacent Analysis
open scoped Classical ContDiff BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
  {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f) (η:I→ℕ)
  (W:∀l:Hot R,C.power l=Launch.index R η l.val+1)

private def lowered (η:I→ℕ) (b i:I):ℤ:=(η i:ℤ)-(if i=b then 1 else 0)
omit [Fintype I] in
private theorem lowered_sum (η:I→ℕ) (b:I) (s:Finset I):
    (∑i∈s,lowered η b i)=((∑i∈s,η i):ℤ)-(if b∈s then 1 else 0):=by
  simp [lowered,Finset.sum_sub_distrib]

include W
theorem mixed_engineering_degree (s:Hot R) (r j:ℕ):
    Level ((Launch.index R η s.val+1+j:ℕ):ℤ)
      (fun x=>(Order.observe R r (Order.logMarked (Bulk.Fk K F tag C x r)) j).part s.val) := by
  obtain ⟨b,hb⟩:=s.property
  have worth:Toile C.power s.val (lowered η b):=by
    intro m _
    rw [W m,lowered_sum]
    change ((∑i∈m.sites,η i)+1:ℕ)≤(2:ℤ)+(((∑i∈m.sites,η i):ℤ)-(if b∈m.sites then 1 else 0))
    split <;> push_cast <;> omega
  have rank:=Valence.mark_read K F tag C (r:=r) (lowered η b) s.val j worth
  rw [lowered_sum,if_pos hb] at rank
  apply rank.promote
  unfold Launch.index;push_cast;omega

theorem mixed_engineering_reset (s:Hot R) (r p':ℕ) (hp:p'≤r) (cost:UnitCost) (n:ℤ):
    let U:=fun j (x:Stationary.Link G c)=>(Order.observe R r
      (Order.logMarked (Bulk.Fk K F tag C (Stationary.arm G c 1 x) r)) j).part s.val
    Level ((Launch.index R η s.val+1+p':ℕ):ℤ) (born U cost n r p') := by
  intro U
  let m:=fun j:ℕ=>((Launch.index R η s.val+1+j:ℕ):ℤ)
  have rank:Charge r m U:=by
    intro j _
    have h:=SignCovariance.affine_degree 0 (Stationary.arm G c 1).toContinuousLinearMap
      (mixed_engineering_degree K F tag C η W s r j)
    change Level ((Launch.index R η s.val+1+j:ℕ):ℤ) (fun x=>
      (Order.observe R r (Order.logMarked (Bulk.Fk K F tag C (Stationary.arm G c 1 x) r)) j).part s.val)
    simp only [zero_add] at h
    exact h
  exact apportion cost n r rank p' hp (fun j hj=>by unfold m;exact_mod_cast Nat.add_le_add_left hj.le _)

end YM.Integration.FVA1Physical.Wilson
