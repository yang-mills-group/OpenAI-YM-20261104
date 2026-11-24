import YM.Integration.WilsonOriginalReceivedPost
/-! Restrict the actual financial radius of each marked row without changing
its address, angular polynomial, chart majorant, or forced companions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRosterResize
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V I X : Type} [DecidableEq V] {J:Census V}
  {P:Passport n V}{p:BudgetPoint}{o:V→Site n}{w u:V→ℝ}

theorem toll (pos:∀ v,0≤u v) (under:∀v,u v≤w v) (z:J.Mode) :
    Poly.toll u z ≤ Poly.toll w z:=by
  unfold Poly.toll
  exact Finset.prod_le_prod (fun v _=>pos v) (fun v _=>under v)

theorem model (pos:∀v,0<u v) (under:∀v,u v≤w v) (M:I→Row P J G X)
    {σ b:ℝ} (salary:Offers M w σ b): Offers M u σ b:=by
  classical
  have rent (i:I):0≤(M i).height σ:=mul_nonneg (M i).sound.le (Real.exp_pos _).le
  intro y
  apply budget_mono (salary y)
  · intro i
    split
    · exact mul_nonneg (Poly.worth pos _).le (rent i)
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right (toll (fun z=>(pos z).le) under _) (rent i)
    · rfl

theorem old (pos:∀v,0<u v) (under:∀v,u v≤w v) (L:Lamps X I G p o J)
    {b:ℕ}{a wage:ℝ} (paid:L.Paid w b a wage):L.Paid u b a wage:=by
  obtain ⟨f,non,read,bill⟩:=paid.budget
  refine ⟨f,non,read,?_⟩
  intro y
  apply budget_mono (bill y)
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth pos _).le (non i)) (Real.exp_pos _).le
    · rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (toll (fun z=>(pos z).le) under _) (non i))
        (Real.exp_pos _).le
    · rfl

end YM.Integration.WilsonMeasuredRosterResize
end
