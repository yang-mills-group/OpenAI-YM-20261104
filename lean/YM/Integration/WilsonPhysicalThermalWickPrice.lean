import YM.Integration.WilsonPhysicalThermalWickRescale

/-! Anisotropic two-field Wick error on the actual gaussian entries.
Only the entry error is enlarged by the square of the test radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickPrice
open Finset Function MvPolynomial
open Next.Rank.Normal Next.Rank.Common Next.Rank.Rise
open WilsonPhysicalThermalWickRescale
open scoped BigOperators Classical
variable {V:Type*}

def scales (P:ℝ)(i:Fin 2):ℂ:=if i=0 then (P:ℂ)⁻¹ else (P:ℂ)

private theorem inverse {P:ℝ}(hP:1≤P):scales P 0 * scales P 1=1:=by
  have hp:0<P:=zero_lt_one.trans_le hP
  simp [scales,Complex.ofReal_ne_zero.mpr hp.ne']

private theorem norm_scales {P:ℝ}(hP:1≤P)(i:Fin 2):‖scales P i‖≤P:=by
  fin_cases i
  · simp [scales,abs_of_nonneg (zero_le_one.trans hP)]
    exact ((inv_le_one₀ (zero_lt_one.trans_le hP)).mpr hP).trans hP
  · simp [scales,abs_of_nonneg (zero_le_one.trans hP)]

theorem amplified {P B E:ℝ}(hP:1≤P)(Q F:Symmetric (Fin 2 × V))(μ:Fin 2 × V→ℂ)
    (zero:∀i j:Fin 2 × V,i.1=j.1→F.cov i j=0)(fees:Nearby Q F μ 0 B E):
    Nearby (scope (edit (scales P)) Q) F (reads (edit (scales P)) μ) 0 (B+P^2*E) (P^2*E):=by
  let a:=scales P
  have hp:0≤P:=zero_le_one.trans hP
  have pay:0≤P^2*E:=mul_nonneg (sq_nonneg _) fees.pos
  have meanPrice (i:Fin 2 × V):‖reads (edit a) μ i‖≤P^2*E:=by
    rw [mean,norm_mul]
    apply (mul_le_mul (norm_scales hP _) (by simpa using fees.mean i) (norm_nonneg _) hp).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (P-1),hP]:P≤P^2) fees.pos
  have covar (i j:Fin 2 × V):‖(scope (edit a) Q).cov i j-F.cov i j‖≤P^2*E:=by
    nth_rw 1 [←invariant a (inverse hP) F zero]
    rw [cov,cov,←mul_sub,norm_mul,norm_mul]
    apply mul_le_mul _ (fees.cov _ _) (norm_nonneg _) (sq_nonneg _)
    simpa only [pow_two] using mul_le_mul (norm_scales hP i.1) (norm_scales hP j.1) (norm_nonneg _) hp
  have larger:B≤B+P^2*E:=le_add_of_nonneg_right pay
  have bn:0≤B:=zero_le_one.trans fees.small'.paid
  refine ⟨⟨fees.small.paid.trans larger,fun i=>(meanPrice i).trans (by linarith),?_⟩,
    ⟨fees.small'.paid.trans larger,fun i=>(fees.small'.mean i).trans larger,fun i j=>(fees.small'.entries i j).trans larger⟩,
    pay,fun i=>by simpa using meanPrice i,covar⟩
  intro i j
  calc
    _≤‖(scope (edit a) Q).cov i j-F.cov i j‖+‖F.cov i j‖:=norm_le_norm_sub_add _ _
    _≤P^2*E+B:=add_le_add (covar i j) (fees.small'.entries _ _)
    _=B+P^2*E:=add_comm .. 

theorem original {P B E:ℝ}(hP:1≤P)(Q F:Symmetric (Fin 2 × V))(μ:Fin 2 × V→ℂ)
    (clear:∀i j:Fin 2 × V,i.1=j.1→F.cov i j=0)(fees:Nearby Q F μ 0 B E)
    (p:Fin 2→poly V)(q:Fin 2→ℕ)(h:∀i,pure (q i) (p i))(S:Finset (Fin 2))
    (D:ℕ)(degree:(pot S p).totalDegree≤D):
    ‖∏i∈S,(scales P i)^(q i)‖*‖blend Q μ (pot S p)-blend F 0 (pot S p)‖≤
      coin (pot S p)*(P^2*E*priced (B+P^2*E) D):=by
  let a:=scales P
  have target:=face a p q h S F 0
  have noMean:reads (edit (V:=V) a) 0=0:=by funext i;rw [mean];simp
  rw [invariant a (inverse hP) F clear,noMean] at target
  have budget:=differs (pot S p) D (amplified hP Q F μ clear fees) degree
  rw [face a p q h S Q μ,target,←mul_sub,norm_mul] at budget
  exact budget

end YM.Integration.WilsonPhysicalThermalWickPrice
end
