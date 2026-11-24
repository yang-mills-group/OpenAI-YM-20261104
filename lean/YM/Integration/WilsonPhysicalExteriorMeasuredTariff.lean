import YM.Integration.WilsonPhysicalExteriorFeePolynomial

/-! One explicit polynomial tariff on the true running and field
reannouncement of the original registered rows. The cap and perturbative
order are chosen before all three real logs and all operator labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorMeasuredTariff
open Finset MS MS.Land MS.Menus WilsonPhysicalExteriorRunningRows WilsonPhysicalExteriorFeePolynomial
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}

def length (x:Fin 3→ℝ):ℝ:=1+∑ i,|x i|
private theorem length_one (x:Fin 3→ℝ) : 1≤length x := by
  have h:0≤∑ i,|x i|:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  dsimp [length];linarith
private theorem bounded (P:MvPolynomial (Fin 3) ℝ) :
    ∃ A:ℝ,0≤A ∧ ∃ d:ℕ,∀ x:Fin 3→ℝ,|(MvPolynomial.eval x) P|≤A*(length x)^d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨|a|,abs_nonneg _,0,by simp⟩
  | add p q hp hq =>
    obtain ⟨A,a,e,ur⟩:=hp
    obtain ⟨B,b,d,vr⟩:=hq
    refine ⟨A+B,add_nonneg a b,max e d,fun x=>?_⟩
    rw [map_add,add_mul]
    exact (abs_add_le ..).trans (add_le_add
      ((ur x).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (length_one x) (le_max_left e d)) a))
      ((vr x).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (length_one x) (le_max_right e d)) b)))
  | mul_X p i hp =>
    obtain ⟨A,a,e,ur⟩:=hp
    refine ⟨A,a,e+1,fun x=>?_⟩
    have hx:|x i|≤∑j,|x j|:=single_le_sum (fun j _=>abs_nonneg (x j)) (mem_univ i)
    have h:|x i|≤length x:=by dsimp [length];linarith
    rw [map_mul,MvPolynomial.eval_X,abs_mul,pow_succ,←mul_assoc]
    exact mul_le_mul (ur x) h (abs_nonneg _) (mul_nonneg a (pow_nonneg (by linarith [length_one x]) _))

variable (Q:Prescription B)

/-- One native bound for every entry of every original glyph table with
declared horizon ≤H and every measured perturbative component ≤L. -/
theorem paid (H L:ℕ): ∃ A:ℝ,0≤A ∧ ∃ e:ℕ,∀ d≤H,∀ k≤L,∀ a b:Glyph B d,∀ x:Fin 3→ℝ,
    ‖PowerSeries.coeff k (coordinates Q d (x 0) (x 1) (x 2) a b)‖≤A*(length x)^e := by
  let I:= (d:Fin (H+1)) × (Fin (L+1) × Glyph B d.val × Glyph B d.val)
  let values (i:I):MvPolynomial (Fin 3) ℝ:= PowerSeries.coeff i.2.1.val
    (WilsonPhysicalExteriorFeePolynomial.stored Q i.1.val i.2.2.1 i.2.2.2)
  choose A pos E bound using fun i:I=>bounded (values i)
  refine ⟨∑i,A i,Finset.sum_nonneg fun i _=>pos i,∑i,E i,?_⟩
  intro d hd k hk a b x
  let i:I:=⟨⟨d,by omega⟩,⟨k,by omega⟩,a,b⟩
  have ha:A i≤∑j,A j:=single_le_sum (fun j _=>pos j) (mem_univ i)
  have he:E i≤∑j,E j:=single_le_sum (fun j _=>Nat.zero_le (E j)) (mem_univ i)
  rw [polynomial,Complex.norm_real,Real.norm_eq_abs]
  exact (bound i x).trans (mul_le_mul ha (pow_le_pow_right₀ (length_one x) he)
    (pow_nonneg (by linarith [length_one x]) _) (Finset.sum_nonneg fun j _=>pos j))

end YM.Integration.WilsonPhysicalExteriorMeasuredTariff
end
