import YM.Pert.Attach.Delivery

/-! Lower the support exponent of the forced labels to harvest their tiny cap like in qcomp. This doesn't change masks or paths. Extra hit terms still need their own estimate. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} (A:Activities G n) (X:Corrections G n)
    (P Q:BudgetPoint)(q γ:ℝ)

lemma split_budget {f : ℕ ⊕ ℕ→ℝ} {u v : ℝ} (hu:SumBudget (fun i:ℕ=>f (.inl i)) u)
    (hv:SumBudget (fun i:ℕ=>f (.inr i)) v) : SumBudget f (u+v) := by
   apply budget_of_sum (Sum.rec hu.1 hv.1); intro s; rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight]
   exact add_le_add (budget_sum hu _) (budget_sum hv _)


lemma joint {K : ℕ→ℝ} {w γ₀} (ha:A.KBound Q w) (hk:∀ i U, ‖X.value i U‖ ≤ K i)
    (hb:P.supportExponent+1≤Q.supportExponent)(hs:P.B=Q.B)(hq:1≤q)
    (hβ:Ac.Hit X.region P.B K (P.supportExponent+1) γ₀)(hl:q*w+γ₀ ≤ γ)
    (he:0≤γ)(hm:((P.B+P.B+1:ℕ):ℝ)^4*γ ≤ 1) : Prices A X P q γ := by
   obtain ⟨f,hF,h⟩:=ha
   let g:=fun i=>q*f i
   have hA : Ac.Hit (fun i=>(A.forced i).support) P.B g (P.supportExponent+1) (q*w) := by
      intro x; refine budget_mono (f:=fun i=>q*(if x∈(A.forced i).support then _ else 0)) (budget_scale (by linarith) (h x)) (fun i=>?_) (fun i=>?_)
      · split_ifs; exact mul_nonneg (mul_nonneg (by linarith) (hF _).1) (Real.exp_pos _).le; exact le_rfl
      split_ifs
      · unfold g BudgetPoint.mass; rw [mul_assoc,mul_comm (f i)]; rw [hs]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb (by positivity))) (hF i).1) (zero_le_one.trans hq)
      simp
   refine ⟨⟨he,hq,hm⟩,Sum.elim g K,(fun i U=>mul_le_mul_of_nonneg_left ((hF i).2 U) (zero_le_one.trans hq)),hk,
     fun x=>budget_loosen (split_budget (hA x) (hβ x)) hl⟩
end YM.Pert.Attach
