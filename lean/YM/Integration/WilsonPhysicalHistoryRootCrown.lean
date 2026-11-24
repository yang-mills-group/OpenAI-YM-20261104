import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Root-ticket accounting on the original two real components of each
regular or forced gallery entry. A marked hard entry carries its whole
original support even when it is charged to a single site. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryRootCrown
open Finset Lattice RG Extra.Multi Push.AbsoluteSums
open scoped Classical BigOperators

variable {I K : Type*} {n : Side} {B : ℕ} {A a b : ℝ}
    {soft : I → Support n} {hard : K → Support n} {site : K → Site n}
    {fee : I → ℝ} {force : K → ℝ}

theorem paired (regular : Ac.Hit soft B fee A a)
    (forced : Rooted (fun j => {site j}) hard B A force b) :
    Rooted (fun z : (I ⊕ K) × Bool => Sum.elim soft (fun j => {site j}) z.1)
      (fun z => Sum.elim soft hard z.1) B A
      (fun z => Sum.elim fee force z.1) (2 * (a+b)) := by
  classical
  intro x
  let charge (i : I ⊕ K) :=
    if x ∈ Sum.elim soft (fun j => {site j}) i then
      Real.exp (A * coverNumber B (Sum.elim soft hard i)) * Sum.elim fee force i
    else 0
  have left : SumBudget (charge ∘ Sum.inl) a := by
    convert regular x using 1
    funext j
    dsimp only [Function.comp_apply, charge, Sum.elim_inl]
    split <;> ring
  have right : SumBudget (charge ∘ Sum.inr) b := by
    simpa [Function.comp_def, charge] using forced x
  have whole : SumBudget charge (a+b) := by
    have joint := HasSum.sum (f := charge) left.2.1.hasSum right.2.1.hasSum
    refine ⟨?_, joint.summable, joint.tsum_eq.trans_le (add_le_add left.2.2 right.2.2)⟩
    rintro (i|j)
    · exact left.1 i
    · exact right.1 j
  have parts : SumBudget (fun _ : Bool => (1 : ℝ)) 2 :=
    budget_finite (fun _ => zero_le_one) (by simp)
  simpa only [mul_one, mul_comm (a+b)] using budget_prod whole parts

end YM.Integration.WilsonPhysicalHistoryRootCrown
end

