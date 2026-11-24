import YM.Contacts.Mat.Avoid

/-! A numerical bound for the manuscript's actual signed Lagrange nodes;
the nodes in the rooted lattice are free to avoid each specified coordinate
tie. Their weights are controlled before the target and the grid spacing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedLatticeStencil
open Filter Function Set Finset Polynomial Lagrange Contacts.Mat
open scoped Topology Classical BigOperators
variable {t:ℕ} {H:ℝ}

theorem weight (F:Nodes t H) (i:Fin (t+1)) : ‖bleed F.v i‖≤H^t := by
  have hn:0≤H := (F.starts i).1.trans (F.starts i).2
  have each (j:Fin (t+1)) (ne:j≠i):
      ‖(F.v i-F.v j)⁻¹ * -(F.v j)‖≤H := by
    have lower:=F.apart i j ne.symm
    have ip:(‖F.v i-F.v j‖)⁻¹≤1 := (inv_le_one₀ (zero_lt_one.trans_le lower)).mpr lower
    rw [norm_mul,norm_inv,norm_neg]
    exact (mul_le_mul ip (by rw [Real.norm_of_nonneg (F.starts j).1];exact (F.starts j).2) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  simp only [bleed,Lagrange.basis,Lagrange.basisDivisor,eval_prod,eval_mul,eval_C,eval_sub,eval_X,zero_sub,norm_prod]
  calc
    _≤∏ j∈Finset.univ.erase i,H := Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun j hj=>each j (Finset.mem_erase.mp hj).1
    _=H^t := by simp

/-- Taylor's integral remainder and the exact signed original weights, with
no assumptions on a hypothetical exterior's independence or smoothness. -/
theorem error (F:Nodes t H) (f:ℕ→ℝ→ℂ) (A:ℝ) (ap:0≤A)
    (differentiated:∀ x∈Icc 0 H,∀ j≤t,HasDerivAt (f j) (f (j+1) x) x)
    (bounded:∀ x∈Icc 0 H,‖f (t+1) x‖≤A) :
    ‖f 0 0-∑ i,bleed F.v i • f 0 (F.v i)‖≤((t+1:ℕ):ℝ)*H^t*(A*(H^(t+1)/(t.factorial:ℝ))) := by
  have H0:0≤H := (F.starts 0).1.trans (F.starts 0).2
  have center:=combines_series F.v f F.good
  rw [←center,←Finset.sum_sub_distrib]
  calc
    _≤∑ i:Fin (t+1),‖bleed F.v i • series f t 0 (F.v i)-bleed F.v i • f 0 (F.v i)‖ := norm_sum_le _ _
    _≤∑ _:Fin (t+1),H^t*(A*(H^(t+1)/(t.factorial:ℝ))) := Finset.sum_le_sum fun i _=>by
      rw [←smul_sub,norm_smul,norm_sub_rev]
      exact mul_le_mul (weight F i) (Contacts.Mat.approx f H A differentiated ap bounded (F.starts i))
        (norm_nonneg _) (pow_nonneg H0 _)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

/-- The actual finite offsets and signed prices on the original scalar grid. -/
theorem nodes {I:Type} [Fintype I] (degree:ℕ) (x δ:ℝ) (step:0<δ) (forbid:I→ℝ) :
    ∃ F:Nodes degree (clusterRadius I degree),
      (∀ i, (∃ z:ℤ,x+F.v i*δ=δ*z) ∧ ∀ j,x+F.v i*δ≠forbid j) ∧
      ∀ i,‖bleed F.v i‖≤(clusterRadius I degree)^degree := by
  obtain ⟨F,actual⟩:=between_avoiding (n:=degree) x δ step forbid
  exact ⟨F,actual,weight F⟩

end YM.Integration.WilsonSeparatedLatticeStencil
